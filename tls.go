// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE-Go file.

// Server side implementation of REALITY protocol, a fork of package tls in Go 1.20.
// For client side, please follow https://github.com/XTLS/Xray-core/blob/main/transport/internet/reality/reality.go.
package reality

// BUG(agl): The crypto/tls package only implements some countermeasures
// against Lucky13 attacks on CBC-mode encryption, and only on SHA1
// variants. See http://www.isg.rhul.ac.uk/tls/TLStiming.pdf and
// https://www.imperialviolet.org/2013/02/04/luckythirteen.html.

import (
	"bytes"
	"context"
	"crypto"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ecdsa"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/x509"
	"encoding/binary"
	"encoding/pem"
	"errors"
	"fmt"
	"github.com/patrickmn/go-cache"
	"io"
	"net"
	"os"
	"runtime"
	"strings"
	"sync"
	"time"

	"github.com/pires/go-proxyproto"
	"golang.org/x/crypto/chacha20poly1305"
	"golang.org/x/crypto/curve25519"
	"golang.org/x/crypto/hkdf"
)

type CloseWriteConn interface {
	net.Conn
	CloseWrite() error
}

type MirrorConn struct {
	net.Conn
}

func (c *MirrorConn) Read(b []byte) (int, error) {
	runtime.Gosched()
	n, err := c.Conn.Read(b)
	return n, err
}

func (c *MirrorConn) Write(b []byte) (int, error) {
	return 0, fmt.Errorf("Write(%v)", len(b))
}

func (c *MirrorConn) Close() error {
	return fmt.Errorf("Close()")
}

func (c *MirrorConn) SetDeadline(t time.Time) error {
	return nil
}

func (c *MirrorConn) SetReadDeadline(t time.Time) error {
	return nil
}

func (c *MirrorConn) SetWriteDeadline(t time.Time) error {
	return nil
}

var (
	size  = 8192
	empty = make([]byte, size)
	types = [7]string{
		"Server Hello",
		"Change Cipher Spec",
		"Encrypted Extensions",
		"Certificate",
		"Certificate Verify",
		"Finished",
		"New Session Ticket",
	}
	InvalidClientHelloError = errors.New("invalid client hello")
)

func Value(vals ...byte) (value int) {
	for i, val := range vals {
		value |= int(val) << ((len(vals) - i - 1) * 8)
	}
	return
}

type latestServerName struct {
	value string
	lock  sync.RWMutex
}

func (lsn *latestServerName) SetLatestServerName(serverName string) {
	lsn.lock.Lock()
	defer lsn.lock.Unlock()
	lsn.value = serverName
}

func (lsn *latestServerName) LoadLatestServerName() string {
	lsn.lock.RLock()
	defer lsn.lock.RUnlock()
	return lsn.value
}

func processClientHelloMsg(ctx context.Context, remoteAddr string, conn *Conn, sourceConn net.Conn, config *Config) (*clientHelloMsg, error) {
	cHelloMsg, err := conn.readClientHello(ctx)
	if err != nil || conn.vers != VersionTLS13 || !config.isInServerNames(cHelloMsg.serverName) {
		return cHelloMsg, InvalidClientHelloError
	}
	for i, keyShare := range cHelloMsg.keyShares {
		if keyShare.group != X25519 || len(keyShare.data) != 32 {
			continue
		}
		if conn.AuthKey, err = curve25519.X25519(config.PrivateKey, keyShare.data); err != nil {
			return nil, err
		}
		if _, err = hkdf.New(sha256.New, conn.AuthKey, cHelloMsg.random[:20], []byte("REALITY")).Read(conn.AuthKey); err != nil {
			return nil, err
		}
		var aead cipher.AEAD
		if aesgcmPreferred(cHelloMsg.cipherSuites) {
			block, _ := aes.NewCipher(conn.AuthKey)
			aead, _ = cipher.NewGCM(block)
		} else {
			aead, _ = chacha20poly1305.New(conn.AuthKey)
		}
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.c.AuthKey[:16]: %v\tAEAD: %T\n", remoteAddr, conn.AuthKey[:16], aead)
		}
		ciphertext := make([]byte, 32)
		plainText := make([]byte, 32)
		copy(ciphertext, cHelloMsg.sessionId)
		copy(cHelloMsg.sessionId, plainText) // hs.clientHello.sessionId points to hs.clientHello.raw[39:]
		if _, err = aead.Open(plainText[:0], cHelloMsg.random[20:], ciphertext, cHelloMsg.original); err != nil {
			copy(cHelloMsg.sessionId, ciphertext)
			break
		}
		copy(cHelloMsg.sessionId, ciphertext)
		copy(conn.ClientVer[:], plainText)
		conn.ClientTime = time.Unix(int64(binary.BigEndian.Uint32(plainText[4:])), 0)
		copy(conn.ClientShortId[:], plainText[8:])
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.c.ClientVer: %v\n", remoteAddr, conn.ClientVer)
			fmt.Printf("REALITY remoteAddr: %v\ths.c.ClientTime: %v\n", remoteAddr, conn.ClientTime)
			fmt.Printf("REALITY remoteAddr: %v\ths.c.ClientShortId: %v\n", remoteAddr, conn.ClientShortId)
		}
		if (config.MinClientVer == nil || Value(conn.ClientVer[:]...) >= Value(config.MinClientVer...)) &&
			(config.MaxClientVer == nil || Value(conn.ClientVer[:]...) <= Value(config.MaxClientVer...)) &&
			(config.MaxTimeDiff == 0 || time.Since(conn.ClientTime).Abs() <= config.MaxTimeDiff) &&
			(config.ShortIds[conn.ClientShortId]) {
			conn.conn = sourceConn
		}
		cHelloMsg.keyShares[0].group = CurveID(i)
		break
	}
	return cHelloMsg, err
}

type cacheKey string

func (ck cacheKey) Key(serverName string) string {
	return fmt.Sprintf(string(ck), serverName)
}

const (
	serverHelloCacheKey cacheKey = "%s:server_hello"
	certCacheKey        cacheKey = "%s:cert"
	certStatusCacheKey  cacheKey = "%s:cert_status"
)

var (
	targetResponseCache = cache.New(5*time.Minute, 10*time.Minute)
	targetConnLock      = new(sync.Mutex)
	ErrorCacheNotFound  = errors.New("cache not found")
	dest                latestServerName
)

func serverHelloInCache(chm *clientHelloMsg) (*serverHelloMsg, bool) {
	msg, ok := targetResponseCache.Get(serverHelloCacheKey.Key(chm.serverName))
	if !ok {
		return nil, false
	}
	shm, ok := msg.(*serverHelloMsg)
	if !ok {
		return nil, false
	}
	res := *shm
	res.original = nil
	if len(res.sessionId) != 0 {
		res.sessionId = chm.sessionId
	}
	res.random = make([]byte, 32)
	rand.Read(res.random)
	return &res, ok
}

func certMsgInCache(chm *clientHelloMsg) (*certificateMsg, bool) {
	msg, ok := targetResponseCache.Get(certCacheKey.Key(chm.serverName))
	if !ok {
		return nil, false
	}
	certMsg, ok := msg.(*certificateMsg)
	return certMsg, ok
}

func certStatusInCache(chm *clientHelloMsg) (*certificateStatusMsg, bool) {
	msg, ok := targetResponseCache.Get(certStatusCacheKey.Key(chm.serverName))
	if !ok {
		return nil, false
	}
	certStatusMsg, ok := msg.(*certificateStatusMsg)
	return certStatusMsg, ok
}

func targetResponseInCache(chm *clientHelloMsg) (*serverHelloMsg, *certificateMsg, *certificateStatusMsg, error) {
	serverHello, ok := serverHelloInCache(chm)
	if !ok {
		return nil, nil, nil, ErrorCacheNotFound
	}
	if serverHello.vers == VersionTLS13 || serverHello.supportedVersion == VersionTLS13 {
		return serverHello, nil, nil, nil
	}
	certMsg, ok := certMsgInCache(chm)
	if !ok {
		return nil, nil, nil, ErrorCacheNotFound
	}
	if !serverHello.ocspStapling {
		return serverHello, certMsg, nil, nil
	}
	certStatusMsg, ok := certStatusInCache(chm)
	if !ok {
		return nil, nil, nil, ErrorCacheNotFound
	}
	return serverHello, certMsg, certStatusMsg, nil
}

func processTargetConnWithCache(ctx context.Context, config *Config, msg *clientHelloMsg) (*serverHelloMsg, *certificateMsg, *certificateStatusMsg, error) {
	serverHello, certMsg, certStatusMsg, err := targetResponseInCache(msg)
	if err == nil {
		return serverHello, certMsg, certStatusMsg, nil
	}
	targetConnLock.Lock()
	defer targetConnLock.Unlock()
	serverHello, certMsg, certStatusMsg, err = targetResponseInCache(msg)
	if err == nil {
		return serverHello, certMsg, certStatusMsg, nil
	}
	serverHello, certMsg, certStatusMsg, err = processTargetConn(ctx, config, msg)
	if err != nil {
		return nil, nil, nil, err
	}
	go dest.SetLatestServerName(msg.serverName)
	targetResponseCache.Set(serverHelloCacheKey.Key(msg.serverName), serverHello, config.CacheDuration)
	targetResponseCache.Set(certCacheKey.Key(msg.serverName), certMsg, config.CacheDuration)
	targetResponseCache.Set(certStatusCacheKey.Key(msg.serverName), certStatusMsg, config.CacheDuration)
	return serverHello, certMsg, certStatusMsg, nil
}

func processTargetConn(ctx context.Context, config *Config, msg *clientHelloMsg) (*serverHelloMsg, *certificateMsg, *certificateStatusMsg, error) {
	targetConn, err := config.DialContext(ctx, config.Type, fmt.Sprintf("%s:443", msg.serverName))
	if err != nil {
		return nil, nil, nil, err
	}
	c := &Conn{
		conn:     targetConn,
		config:   config,
		isClient: true,
	}
	defer c.Close()
	if _, err := c.writeHandshakeRecord(msg, nil); err != nil {
		c.sendAlert(alertUnexpectedMessage)
		return nil, nil, nil, err
	}

	msgAny, err := c.readHandshake(nil)
	if err != nil {
		c.sendAlert(alertUnexpectedMessage)
		return nil, nil, nil, err
	}
	serverHello, ok := msgAny.(*serverHelloMsg)
	if !ok {
		c.sendAlert(alertUnexpectedMessage)
		return nil, nil, nil, errors.New("msg is not server hello msg")
	}

	if err := c.pickTLSVersion(serverHello); err != nil {
		return nil, nil, nil, err
	}
	maxVers := c.config.maxSupportedVersion(roleClient)
	tls12Downgrade := string(serverHello.random[24:]) == downgradeCanaryTLS12
	tls11Downgrade := string(serverHello.random[24:]) == downgradeCanaryTLS11
	if maxVers == VersionTLS13 && c.vers <= VersionTLS12 && (tls12Downgrade || tls11Downgrade) ||
		maxVers == VersionTLS12 && c.vers <= VersionTLS11 && tls11Downgrade {
		c.sendAlert(alertIllegalParameter)
		return nil, nil, nil, errors.New("illegal parameter")
	}

	ver := serverHello.vers
	if serverHello.supportedVersion != 0 {
		ver = serverHello.supportedVersion
	}

	if ver == VersionTLS13 {
		hs := &clientHandshakeStateTLS13{
			c:           c,
			ctx:         ctx,
			serverHello: serverHello,
			hello:       msg,
		}
		hs.handshake()
		if cipherSuiteTLS13ByID(serverHello.cipherSuite) == nil ||
			serverHello.serverShare.group != X25519 || len(serverHello.serverShare.data) != 32 {
			return nil, nil, nil, errors.New("invalid server hello")
		}
		return serverHello, nil, nil, nil
	}

	suite := mutualCipherSuite(msg.cipherSuites, serverHello.cipherSuite)
	if suite == nil {
		c.sendAlert(alertHandshakeFailure)
		return nil, nil, nil, errors.New("tls: server chose an unconfigured cipher suite")
	}
	fHash := newFinishedHash(c.vers, suite)

	msgAny, err = c.readHandshake(&fHash)
	if err != nil {
		return nil, nil, nil, err
	}

	certMsg, ok := msgAny.(*certificateMsg)
	if !ok || len(certMsg.certificates) == 0 {
		c.sendAlert(alertUnexpectedMessage)
		return nil, nil, nil, errors.New("unexpected message")
	}

	msgAny, err = c.readHandshake(&fHash)
	if err != nil {
		return nil, nil, nil, err
	}

	certStatusMsg, ok := msgAny.(*certificateStatusMsg)
	if ok {
		if !serverHello.ocspStapling {
			// If a server returns a "CertificateStatus" message, then the
			// server MUST have included an extension of type "status_request"
			// with empty "extension_data" in the extended server hello.

			c.sendAlert(alertUnexpectedMessage)
			return nil, nil, nil, errors.New("tls: received unexpected CertificateStatus message")
		}
		msgAny, err = c.readHandshake(&fHash)
		if err != nil {
			return nil, nil, nil, err
		}
	}

	var shd *serverHelloDoneMsg
	for {
		shd, ok = msgAny.(*serverHelloDoneMsg)
		if ok {
			break
		}
		msgAny, err = c.readHandshake(&fHash)
		if err != nil {
			break
		}
	}
	if shd == nil {
		c.sendAlert(alertUnexpectedMessage)
		return serverHello, certMsg, certStatusMsg, nil
	}

	if err := c.writeChangeCipherRecord(); err != nil {
		return serverHello, certMsg, certStatusMsg, nil
	}
	if _, err := c.writeHandshakeRecord(&finishedMsg{}, &fHash); err != nil {
		return serverHello, certMsg, certStatusMsg, nil
	}
	if _, err := c.flush(); err != nil {
		return serverHello, certMsg, certStatusMsg, nil
	}
	c.isHandshakeComplete.Store(true)
	return serverHello, certMsg, certStatusMsg, nil
}

func serverFailHandler(ctx context.Context, conn CloseWriteConn, config *Config, msg *clientHelloMsg) error {
	if msg == nil {
		conn.Close()
		return errors.New("REALITY: client hello msg is nil")
	}
	destTarget := dest.LoadLatestServerName()
	if len(destTarget) == 0 {
		if len(config.Dest) == 0 {
			conn.Close()
			return errors.New("REALITY: destTarget is nil")
		}
		destTarget = config.Dest
	} else {
		destTarget = fmt.Sprintf("%s:443", destTarget)
	}
	target, err := config.DialContext(ctx, config.Type, destTarget)
	if err != nil {
		conn.Close()
		return errors.New("REALITY: failed to dial dest: " + err.Error())
	}
	data, err := msg.marshal()
	if err != nil {
		conn.Close()
		return errors.New("REALITY: failed to marshal client hello msg: " + err.Error())
	}
	var outData = make([]byte, recordHeaderLen)
	vers := msg.vers
	if vers == 0 {
		// Some TLS servers fail if the record version is
		// greater than TLS 1.0 for the initial ClientHello.
		vers = VersionTLS10
	} else if vers == VersionTLS13 {
		// TLS 1.3 froze the record layer version to 1.2.
		// See RFC 8446, Section 5.1.
		vers = VersionTLS12
	}
	outData[0] = byte(recordTypeHandshake)
	outData[1] = byte(vers >> 8)
	outData[2] = byte(vers)
	outData[3] = byte(len(data) >> 8)
	outData[4] = byte(len(data))
	target.Write(append(outData, data...))
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		io.Copy(target, conn)
		wg.Done()
	}()
	go func() {
		io.Copy(conn, target)
		wg.Done()
	}()
	wg.Wait()
	target.Close()
	conn.Close()
	return errors.New("REALITY: processed invalid connection")
}

func certByCertMsg(msg *certificateMsg, config *Config) *Certificate {
	if len(msg.certificates) == 0 {
		return nil
	}
	certificate, _ := x509.ParseCertificates(msg.certificates[0])
	if len(certificate) == 0 {
		return nil
	}
	switch certificate[0].PublicKeyAlgorithm {
	case x509.RSA:
		return &Certificate{
			PrivateKey:  config.RSACertPrivateKey,
			Certificate: [][]byte{config.RSACert},
		}
	case x509.ECDSA:
		return &Certificate{
			PrivateKey:  config.ECDSACertPrivateKey,
			Certificate: [][]byte{config.ECDSACert},
		}
	default:
		return nil
	}
}

// Server returns a new TLS server side connection
// using conn as the underlying transport.
// The configuration config must be non-nil and must include
// at least one certificate or else set GetCertificate.
func Server(ctx context.Context, conn net.Conn, config *Config) (*Conn, error) {
	remoteAddr := conn.RemoteAddr().String()
	if config.Show {
		fmt.Printf("REALITY remoteAddr: %v\n", remoteAddr)
	}

	var (
		err error
		raw = conn
	)
	if pc, ok := conn.(*proxyproto.Conn); ok {
		raw = pc.Raw() // for TCP splicing in io.Copy()
	}
	underlying := raw.(CloseWriteConn) // *net.TCPConn or *net.UnixConn

	c := &Conn{
		conn: &MirrorConn{
			Conn: conn,
		},
		config: config,
	}

	clientHelloMsg, err := processClientHelloMsg(ctx, remoteAddr, c, conn, config)
	if err != nil {
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}

	if config.Show {
		fmt.Printf("REALITY remoteAddr: %v\ths.c.conn == conn: %v\n", remoteAddr, c.conn == conn)
	}
	if c.conn != conn {
		if config.Show && clientHelloMsg != nil {
			fmt.Printf("REALITY remoteAddr: %v\tforwarded SNI: %v\ths.c.ClientTime: %v\ttime since hs.c.ClientTime: %v\n", remoteAddr, clientHelloMsg.serverName, c.ClientTime, time.Since(c.ClientTime).Abs())
		}
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}

	serverHelloMsg, certMsg, certStatusMsg, err := processTargetConnWithCache(ctx, config, clientHelloMsg)
	if err != nil {
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}

	c.vers = serverHelloMsg.vers
	if serverHelloMsg.supportedVersion != 0 {
		c.vers = serverHelloMsg.supportedVersion
	}

	if c.vers == VersionTLS13 {
		hs := serverHandshakeStateTLS13{
			c:   c,
			ctx: context.Background(),
		}
		hs.clientHello = clientHelloMsg
		hs.hello = serverHelloMsg
		err = hs.handshake()
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.handshake() err: %v\n", remoteAddr, err)
		}
		if err != nil {
			fmt.Printf("REALITY remoteAddr: %v\ths.handshake() err: %v\n", remoteAddr, err)
			return nil, serverFailHandler(ctx, underlying, config, hs.clientHello)
		}

		err := hs.readClientFinished()
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.readClientFinished() err: %v\n", remoteAddr, err)
		}
		if err != nil {
			fmt.Printf("REALITY remoteAddr: %v\ths.handshake() err: %v\n", remoteAddr, err)
			return nil, serverFailHandler(ctx, underlying, config, hs.clientHello)
		}
		hs.c.isHandshakeComplete.Store(true)

		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.c.handshakeStatus: %v\n", remoteAddr, hs.c.isHandshakeComplete.Load())
		}

		return hs.c, nil
	}

	cert := certByCertMsg(certMsg, config)
	if cert == nil {
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}
	hs := serverHandshakeState{
		c:    c,
		ctx:  context.Background(),
		cert: cert,
	}
	hs.clientHello = clientHelloMsg
	hs.hello = serverHelloMsg
	err = hs.handshake(certMsg, certStatusMsg)
	if config.Show {
		fmt.Printf("REALITY remoteAddr: %v\ths.readClientFinished() err: %v\n", remoteAddr, err)
	}
	if err != nil {
		fmt.Printf("REALITY remoteAddr: %v\ths.handshake() err: %v\n", remoteAddr, err)
		return nil, serverFailHandler(ctx, underlying, config, hs.clientHello)
	}
	if config.Show {
		fmt.Printf("REALITY remoteAddr: %v\ths.c.handshakeStatus: %v\n", remoteAddr, hs.c.isHandshakeComplete.Load())
	}

	return hs.c, nil
}

// Client returns a new TLS client side connection
// using conn as the underlying transport.
// The config cannot be nil: users must set either ServerName or
// InsecureSkipVerify in the config.
func Client(conn net.Conn, config *Config) *Conn {
	c := &Conn{
		conn:     conn,
		config:   config,
		isClient: true,
	}
	c.handshakeFn = c.clientHandshake
	return c
}

// A listener implements a network listener (net.Listener) for TLS connections.
type listener struct {
	net.Listener
	config *Config
	conns  chan net.Conn
	err    error
}

// Accept waits for and returns the next incoming TLS connection.
// The returned connection is of type *Conn.
func (l *listener) Accept() (net.Conn, error) {
	/*
		c, err := l.Listener.Accept()
		if err != nil {
			return nil, err
		}
		return Server(c, l.config), nil
	*/
	if c, ok := <-l.conns; ok {
		return c, nil
	}
	return nil, l.err
}

// NewListener creates a Listener which accepts connections from an inner
// Listener and wraps each connection with [Server].
// The configuration config must be non-nil and must include
// at least one certificate or else set GetCertificate.
func NewListener(inner net.Listener, config *Config) net.Listener {
	l := new(listener)
	l.Listener = inner
	l.config = config
	{
		l.conns = make(chan net.Conn)
		go func() {
			for {
				c, err := l.Listener.Accept()
				if err != nil {
					l.err = err
					close(l.conns)
					return
				}
				go func() {
					defer recover()
					c, err = Server(context.Background(), c, l.config)
					if err == nil {
						l.conns <- c
					}
				}()
			}
		}()
	}
	return l
}

// Listen creates a TLS listener accepting connections on the
// given network address using net.Listen.
// The configuration config must be non-nil and must include
// at least one certificate or else set GetCertificate.
func Listen(network, laddr string, config *Config) (net.Listener, error) {
	if config == nil || len(config.Certificates) == 0 &&
		config.GetCertificate == nil && config.GetConfigForClient == nil {
		return nil, errors.New("tls: neither Certificates, GetCertificate, nor GetConfigForClient set in Config")
	}
	l, err := net.Listen(network, laddr)
	if err != nil {
		return nil, err
	}
	return NewListener(l, config), nil
}

type timeoutError struct{}

func (timeoutError) Error() string   { return "tls: DialWithDialer timed out" }
func (timeoutError) Timeout() bool   { return true }
func (timeoutError) Temporary() bool { return true }

// DialWithDialer connects to the given network address using dialer.Dial and
// then initiates a TLS handshake, returning the resulting TLS connection. Any
// timeout or deadline given in the dialer apply to connection and TLS
// handshake as a whole.
//
// DialWithDialer interprets a nil configuration as equivalent to the zero
// configuration; see the documentation of [Config] for the defaults.
//
// DialWithDialer uses context.Background internally; to specify the context,
// use [Dialer.DialContext] with NetDialer set to the desired dialer.
func DialWithDialer(dialer *net.Dialer, network, addr string, config *Config) (*Conn, error) {
	return dial(context.Background(), dialer, network, addr, config)
}

func dial(ctx context.Context, netDialer *net.Dialer, network, addr string, config *Config) (*Conn, error) {
	if netDialer.Timeout != 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, netDialer.Timeout)
		defer cancel()
	}

	if !netDialer.Deadline.IsZero() {
		var cancel context.CancelFunc
		ctx, cancel = context.WithDeadline(ctx, netDialer.Deadline)
		defer cancel()
	}

	rawConn, err := netDialer.DialContext(ctx, network, addr)
	if err != nil {
		return nil, err
	}

	colonPos := strings.LastIndex(addr, ":")
	if colonPos == -1 {
		colonPos = len(addr)
	}
	hostname := addr[:colonPos]

	if config == nil {
		config = defaultConfig()
	}
	// If no ServerName is set, infer the ServerName
	// from the hostname we're connecting to.
	if config.ServerName == "" {
		// Make a copy to avoid polluting argument or default.
		c := config.Clone()
		c.ServerName = hostname
		config = c
	}

	conn := Client(rawConn, config)
	if err := conn.HandshakeContext(ctx); err != nil {
		rawConn.Close()
		return nil, err
	}
	return conn, nil
}

// Dial connects to the given network address using net.Dial
// and then initiates a TLS handshake, returning the resulting
// TLS connection.
// Dial interprets a nil configuration as equivalent to
// the zero configuration; see the documentation of Config
// for the defaults.
func Dial(network, addr string, config *Config) (*Conn, error) {
	return DialWithDialer(new(net.Dialer), network, addr, config)
}

// Dialer dials TLS connections given a configuration and a Dialer for the
// underlying connection.
type Dialer struct {
	// NetDialer is the optional dialer to use for the TLS connections'
	// underlying TCP connections.
	// A nil NetDialer is equivalent to the net.Dialer zero value.
	NetDialer *net.Dialer

	// Config is the TLS configuration to use for new connections.
	// A nil configuration is equivalent to the zero
	// configuration; see the documentation of Config for the
	// defaults.
	Config *Config
}

// Dial connects to the given network address and initiates a TLS
// handshake, returning the resulting TLS connection.
//
// The returned [Conn], if any, will always be of type *[Conn].
//
// Dial uses context.Background internally; to specify the context,
// use [Dialer.DialContext].
func (d *Dialer) Dial(network, addr string) (net.Conn, error) {
	return d.DialContext(context.Background(), network, addr)
}

func (d *Dialer) netDialer() *net.Dialer {
	if d.NetDialer != nil {
		return d.NetDialer
	}
	return new(net.Dialer)
}

// DialContext connects to the given network address and initiates a TLS
// handshake, returning the resulting TLS connection.
//
// The provided Context must be non-nil. If the context expires before
// the connection is complete, an error is returned. Once successfully
// connected, any expiration of the context will not affect the
// connection.
//
// The returned [Conn], if any, will always be of type *[Conn].
func (d *Dialer) DialContext(ctx context.Context, network, addr string) (net.Conn, error) {
	c, err := dial(ctx, d.netDialer(), network, addr, d.Config)
	if err != nil {
		// Don't return c (a typed nil) in an interface.
		return nil, err
	}
	return c, nil
}

// LoadX509KeyPair reads and parses a public/private key pair from a pair
// of files. The files must contain PEM encoded data. The certificate file
// may contain intermediate certificates following the leaf certificate to
// form a certificate chain. On successful return, Certificate.Leaf will
// be nil because the parsed form of the certificate is not retained.
func LoadX509KeyPair(certFile, keyFile string) (Certificate, error) {
	certPEMBlock, err := os.ReadFile(certFile)
	if err != nil {
		return Certificate{}, err
	}
	keyPEMBlock, err := os.ReadFile(keyFile)
	if err != nil {
		return Certificate{}, err
	}
	return X509KeyPair(certPEMBlock, keyPEMBlock)
}

// X509KeyPair parses a public/private key pair from a pair of
// PEM encoded data. On successful return, Certificate.Leaf will be nil because
// the parsed form of the certificate is not retained.
func X509KeyPair(certPEMBlock, keyPEMBlock []byte) (Certificate, error) {
	fail := func(err error) (Certificate, error) { return Certificate{}, err }

	var cert Certificate
	var skippedBlockTypes []string
	for {
		var certDERBlock *pem.Block
		certDERBlock, certPEMBlock = pem.Decode(certPEMBlock)
		if certDERBlock == nil {
			break
		}
		if certDERBlock.Type == "CERTIFICATE" {
			cert.Certificate = append(cert.Certificate, certDERBlock.Bytes)
		} else {
			skippedBlockTypes = append(skippedBlockTypes, certDERBlock.Type)
		}
	}

	if len(cert.Certificate) == 0 {
		if len(skippedBlockTypes) == 0 {
			return fail(errors.New("tls: failed to find any PEM data in certificate input"))
		}
		if len(skippedBlockTypes) == 1 && strings.HasSuffix(skippedBlockTypes[0], "PRIVATE KEY") {
			return fail(errors.New("tls: failed to find certificate PEM data in certificate input, but did find a private key; PEM inputs may have been switched"))
		}
		return fail(fmt.Errorf("tls: failed to find \"CERTIFICATE\" PEM block in certificate input after skipping PEM blocks of the following types: %v", skippedBlockTypes))
	}

	skippedBlockTypes = skippedBlockTypes[:0]
	var keyDERBlock *pem.Block
	for {
		keyDERBlock, keyPEMBlock = pem.Decode(keyPEMBlock)
		if keyDERBlock == nil {
			if len(skippedBlockTypes) == 0 {
				return fail(errors.New("tls: failed to find any PEM data in key input"))
			}
			if len(skippedBlockTypes) == 1 && skippedBlockTypes[0] == "CERTIFICATE" {
				return fail(errors.New("tls: found a certificate rather than a key in the PEM for the private key"))
			}
			return fail(fmt.Errorf("tls: failed to find PEM block with type ending in \"PRIVATE KEY\" in key input after skipping PEM blocks of the following types: %v", skippedBlockTypes))
		}
		if keyDERBlock.Type == "PRIVATE KEY" || strings.HasSuffix(keyDERBlock.Type, " PRIVATE KEY") {
			break
		}
		skippedBlockTypes = append(skippedBlockTypes, keyDERBlock.Type)
	}

	// We don't need to parse the public key for TLS, but we so do anyway
	// to check that it looks sane and matches the private key.
	x509Cert, err := x509.ParseCertificate(cert.Certificate[0])
	if err != nil {
		return fail(err)
	}

	cert.PrivateKey, err = parsePrivateKey(keyDERBlock.Bytes)
	if err != nil {
		return fail(err)
	}

	switch pub := x509Cert.PublicKey.(type) {
	case *rsa.PublicKey:
		priv, ok := cert.PrivateKey.(*rsa.PrivateKey)
		if !ok {
			return fail(errors.New("tls: private key type does not match public key type"))
		}
		if pub.N.Cmp(priv.N) != 0 {
			return fail(errors.New("tls: private key does not match public key"))
		}
	case *ecdsa.PublicKey:
		priv, ok := cert.PrivateKey.(*ecdsa.PrivateKey)
		if !ok {
			return fail(errors.New("tls: private key type does not match public key type"))
		}
		if pub.X.Cmp(priv.X) != 0 || pub.Y.Cmp(priv.Y) != 0 {
			return fail(errors.New("tls: private key does not match public key"))
		}
	case ed25519.PublicKey:
		priv, ok := cert.PrivateKey.(ed25519.PrivateKey)
		if !ok {
			return fail(errors.New("tls: private key type does not match public key type"))
		}
		if !bytes.Equal(priv.Public().(ed25519.PublicKey), pub) {
			return fail(errors.New("tls: private key does not match public key"))
		}
	default:
		return fail(errors.New("tls: unknown public key algorithm"))
	}

	return cert, nil
}

// Attempt to parse the given private key DER block. OpenSSL 0.9.8 generates
// PKCS #1 private keys by default, while OpenSSL 1.0.0 generates PKCS #8 keys.
// OpenSSL ecparam generates SEC1 EC private keys for ECDSA. We try all three.
func parsePrivateKey(der []byte) (crypto.PrivateKey, error) {
	if key, err := x509.ParsePKCS1PrivateKey(der); err == nil {
		return key, nil
	}
	if key, err := x509.ParsePKCS8PrivateKey(der); err == nil {
		switch key := key.(type) {
		case *rsa.PrivateKey, *ecdsa.PrivateKey, ed25519.PrivateKey:
			return key, nil
		default:
			return nil, errors.New("tls: found unknown private key type in PKCS#8 wrapping")
		}
	}
	if key, err := x509.ParseECPrivateKey(der); err == nil {
		return key, nil
	}

	return nil, errors.New("tls: failed to parse private key")
}
