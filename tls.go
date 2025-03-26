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
	"crypto/md5"
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/x509"
	"encoding/binary"
	"encoding/hex"
	"encoding/pem"
	"errors"
	"fmt"
	"github.com/patrickmn/go-cache"
	"golang.org/x/crypto/cryptobyte"
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
	sni            string
	isUseFakeSNIIP bool
	lock           sync.RWMutex
}

func (lsn *latestServerName) SetLatestServerName(serverName string, isUseFakeSNIIP bool) {
	lsn.lock.Lock()
	defer lsn.lock.Unlock()
	lsn.sni = serverName
	lsn.isUseFakeSNIIP = isUseFakeSNIIP
}

func (lsn *latestServerName) LoadLatestServerName() (string, bool) {
	lsn.lock.RLock()
	defer lsn.lock.RUnlock()
	return lsn.sni, lsn.isUseFakeSNIIP
}

func processClientHelloMsg(ctx context.Context, remoteAddr string, conn *Conn, sourceConn net.Conn, config *Config) (*clientHelloMsg, error) {
	cHelloMsg, err := conn.readClientHello(ctx)
	if err != nil || !config.isInServerNames(cHelloMsg.serverName) {
		return cHelloMsg, InvalidClientHelloError
	}
	for _, keyShare := range cHelloMsg.keyShares {
		if keyShare.group != X25519 || len(keyShare.data) != 32 {
			continue
		}
		if conn.AuthKey, err = curve25519.X25519(config.PrivateKey, keyShare.data); err != nil {
			return cHelloMsg, err
		}
		if _, err = hkdf.New(sha256.New, conn.AuthKey, cHelloMsg.random[:20], []byte("REALITY")).Read(conn.AuthKey); err != nil {
			return cHelloMsg, err
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
		break
	}
	return cHelloMsg, err
}

type cacheKey string

func (ck cacheKey) Key(serverName string, clientHelloMsgMD5 string) string {
	return fmt.Sprintf(string(ck), serverName, clientHelloMsgMD5)
}

const (
	targetResponseCacheKey cacheKey = "%s:%s"
)

var (
	targetResponseCache = cache.New(5*time.Minute, 10*time.Minute)
	ErrorCacheNotFound  = errors.New("cache not found")
	dest                latestServerName
	cacheLockMap        = sync.Map{}
)

type tls12Response struct {
	certificate       *certificateMsg
	certificateStatus *certificateStatusMsg
}

type tls13Response struct {
	handshakeLen [7]int
}

type targetResponse struct {
	ServerHelloMsg *serverHelloMsg
	tls12Response  *tls12Response
	tls13Response  *tls13Response
}

func targetResponseInCache(chm *clientHelloMsg, chmMD5 string) (*targetResponse, error) {
	response, ok := targetResponseCache.Get(targetResponseCacheKey.Key(chm.serverName, chmMD5))
	if !ok {
		return nil, ErrorCacheNotFound
	}
	cacheResponse, ok := response.(*targetResponse)
	if !ok {
		return nil, ErrorCacheNotFound
	}
	resCopy := *cacheResponse
	shm := *cacheResponse.ServerHelloMsg
	shm.original = nil
	if len(shm.sessionId) != 0 {
		shm.sessionId = chm.sessionId
	}
	shm.random = make([]byte, 32)
	rand.Read(shm.random)
	resCopy.ServerHelloMsg = &shm
	return &resCopy, nil
}

func setCacheForClientHello(chm *clientHelloMsg, config *Config, targetResponse *targetResponse, chmMD5 string) {
	if config.CacheDuration <= 0 {
		return
	}
	lAny, ok := cacheLockMap.Load(targetResponseCacheKey.Key(chm.serverName, chmMD5))
	if !ok {
		lAny = &sync.Mutex{}
		cacheLockMap.Store(targetResponseCacheKey.Key(chm.serverName, chmMD5), lAny)
	}
	lock, _ := lAny.(*sync.Mutex)
	lock.Lock()
	defer lock.Unlock()
	targetResponseCache.Set(targetResponseCacheKey.Key(chm.serverName, chmMD5), targetResponse, config.CacheDuration)
}

func isGREASEUint16(v uint16) bool {
	// First byte is same as second byte
	// and lowest nibble is 0xa
	return ((v >> 8) == v&0xff) && v&0xf == 0xa
}

func clientHelloMsgMD5(msg *clientHelloMsg) string {
	var b cryptobyte.Builder
	for _, cs := range msg.cipherSuites {
		if isGREASEUint16(cs) {
			continue
		}
		b.AddUint16(cs)
	}
	var exts cryptobyte.Builder
	if len(msg.serverName) > 0 {
		exts.AddUint16(extensionServerName)
	}
	if len(msg.supportedPoints) > 0 {
		exts.AddUint16(extensionSupportedPoints)
	}
	if msg.ticketSupported {
		exts.AddUint16(extensionSessionTicket)
	}
	if msg.secureRenegotiationSupported {
		exts.AddUint16(extensionRenegotiationInfo)
	}
	if msg.extendedMasterSecret {
		exts.AddUint16(extensionExtendedMasterSecret)
	}
	if msg.scts {
		exts.AddUint16(extensionSCT)
	}
	if msg.earlyData {
		exts.AddUint16(extensionEarlyData)
	}
	if msg.quicTransportParameters != nil {
		exts.AddUint16(extensionQUICTransportParameters)
	}
	if len(msg.encryptedClientHello) > 0 {
		exts.AddUint16(extensionEncryptedClientHello)
	}
	if msg.ocspStapling {
		exts.AddUint16(extensionStatusRequest)
	}
	if len(msg.supportedCurves) > 0 {
		exts.AddUint16(extensionSupportedCurves)
	}
	if len(msg.supportedSignatureAlgorithms) > 0 {
		exts.AddUint16(extensionSignatureAlgorithms)
	}
	if len(msg.supportedSignatureAlgorithmsCert) > 0 {
		exts.AddUint16(extensionSignatureAlgorithmsCert)
	}
	if len(msg.alpnProtocols) > 0 {
		exts.AddUint16(extensionALPN)
	}
	if len(msg.supportedVersions) > 0 {
		exts.AddUint16(extensionSupportedVersions)
	}
	if len(msg.cookie) > 0 {
		exts.AddUint16(extensionCookie)
	}
	if len(msg.keyShares) > 0 {
		exts.AddUint16(extensionKeyShare)
	}
	if len(msg.pskModes) > 0 {
		exts.AddUint16(extensionPSKModes)
	}
	if len(msg.pskIdentities) > 0 {
		exts.AddUint16(extensionPreSharedKey)
	}
	extBytes, _ := exts.Bytes()
	b.AddUint8LengthPrefixed(func(b *cryptobyte.Builder) {
		b.AddBytes(msg.compressionMethods)
	})
	if len(extBytes) > 0 {
		b.AddUint16LengthPrefixed(func(b *cryptobyte.Builder) {
			b.AddBytes(extBytes)
		})
	}
	clientHelloBytes, _ := b.Bytes()
	hash := md5.Sum(clientHelloBytes)
	return hex.EncodeToString(hash[:])
}

func processTargetConnWithCache(ctx context.Context, config *Config, msg *clientHelloMsg) (*targetResponse, error) {
	if config.CacheDuration == 0 {
		response, _, err := processTargetConn(ctx, config, msg)
		return response, err
	}
	chmMD5 := clientHelloMsgMD5(msg)
	res, err := targetResponseInCache(msg, chmMD5)
	if err == nil {
		return res, nil
	}
	var isUseFakeSNIIP bool
	res, isUseFakeSNIIP, err = processTargetConn(ctx, config, msg)
	if err != nil {
		return res, err
	}
	go dest.SetLatestServerName(msg.serverName, isUseFakeSNIIP)
	go setCacheForClientHello(msg, config, res, chmMD5)
	return res, nil
}

func processTargetConn(ctx context.Context, config *Config, msg *clientHelloMsg) (*targetResponse, bool, error) {
	var isUseFakeSNIIP bool
	targetConn, err := config.DialContext(ctx, config.Type, fmt.Sprintf("%s:443", msg.serverName))
	if err != nil {
		if len(config.FakeSNIIP) == 0 {
			return nil, isUseFakeSNIIP, err
		}
		targetConn, err = config.DialContext(ctx, config.Type, fmt.Sprintf("%s:443", config.FakeSNIIP))
		if err != nil {
			return nil, isUseFakeSNIIP, err
		}
		isUseFakeSNIIP = true
	}
	c := &Conn{
		conn:     targetConn,
		config:   config,
		isClient: true,
	}
	defer c.Close()
	if _, err := c.writeHandshakeRecord(msg, nil); err != nil {
		c.sendAlert(alertUnexpectedMessage)
		return nil, isUseFakeSNIIP, err
	}

	msgAny, err := c.readHandshake(nil)
	if err != nil {
		c.sendAlert(alertUnexpectedMessage)
		return nil, isUseFakeSNIIP, err
	}
	serverHello, ok := msgAny.(*serverHelloMsg)
	if !ok {
		c.sendAlert(alertUnexpectedMessage)
		return nil, isUseFakeSNIIP, errors.New("msg is not server hello msg")
	}

	if err := c.pickTLSVersion(serverHello); err != nil {
		return nil, isUseFakeSNIIP, err
	}
	maxVers := c.config.maxSupportedVersion(roleClient)
	tls12Downgrade := string(serverHello.random[24:]) == downgradeCanaryTLS12
	tls11Downgrade := string(serverHello.random[24:]) == downgradeCanaryTLS11
	if maxVers == VersionTLS13 && c.vers <= VersionTLS12 && (tls12Downgrade || tls11Downgrade) ||
		maxVers == VersionTLS12 && c.vers <= VersionTLS11 && tls11Downgrade {
		c.sendAlert(alertIllegalParameter)
		return nil, isUseFakeSNIIP, errors.New("illegal parameter")
	}

	ver := serverHello.vers
	if serverHello.supportedVersion != 0 {
		ver = serverHello.supportedVersion
	}

	var res targetResponse
	res.ServerHelloMsg = serverHello

	if ver == VersionTLS13 {
		if serverHello.vers != VersionTLS12 || serverHello.supportedVersion != VersionTLS13 ||
			cipherSuiteTLS13ByID(serverHello.cipherSuite) == nil ||
			serverHello.serverShare.group != X25519 || len(serverHello.serverShare.data) != 32 {
			c.sendAlert(alertInternalError)
			return nil, isUseFakeSNIIP, errors.New("invalid server hello")
		}
		res.tls13Response = &tls13Response{}
		var (
			s2cSaved     = c.rawInput.Bytes()
			handshakeLen = 0
			isNeedToRead bool
		)
		for {
			if isNeedToRead {
				var buf = make([]byte, size)
				n, err := targetConn.Read(buf)
				if n == 0 {
					if err != nil {
						break
					}
					break
				}
				s2cSaved = append(s2cSaved, buf[:n]...)
				isNeedToRead = false
			}
			for i, _ := range types {
				if res.tls13Response.handshakeLen[i] != 0 {
					continue
				}
				if i == 0 {
					continue
				}
				if i == 6 && len(s2cSaved) == 0 {
					break
				}
				if handshakeLen == 0 && len(s2cSaved) > recordHeaderLen {
					if Value(s2cSaved[1:3]...) != VersionTLS12 ||
						(i == 1 && (recordType(s2cSaved[0]) != recordTypeChangeCipherSpec || s2cSaved[5] != 1)) ||
						(i > 1 && recordType(s2cSaved[0]) != recordTypeApplicationData) {
						c.sendAlert(alertInternalError)
						return nil, isUseFakeSNIIP, errors.New("get cert len fail")
					}
					handshakeLen = recordHeaderLen + Value(s2cSaved[3:5]...)
				}
				if handshakeLen > size { // too long
					c.sendAlert(alertInternalError)
					return nil, isUseFakeSNIIP, errors.New("handshakeLen too long")
				}
				if i == 1 && handshakeLen > 0 && handshakeLen != 6 {
					c.sendAlert(alertInternalError)
					return nil, isUseFakeSNIIP, errors.New("handshakeLen not right")
				}
				if i == 2 && handshakeLen > 512 {
					res.tls13Response.handshakeLen[i] = handshakeLen
					break
				}
				if i == 6 && handshakeLen > 0 {
					res.tls13Response.handshakeLen[i] = handshakeLen
					break
				}
				if handshakeLen == 0 || len(s2cSaved) < handshakeLen {
					isNeedToRead = true
					break
				}
				res.tls13Response.handshakeLen[i] = handshakeLen
				s2cSaved = s2cSaved[handshakeLen:]
				handshakeLen = 0
			}
			if isNeedToRead {
				continue
			}
			break
		}
		c.sendAlert(alertInternalError)
		return &res, isUseFakeSNIIP, nil
	}

	res.tls12Response = &tls12Response{}
	suite := mutualCipherSuite(msg.cipherSuites, serverHello.cipherSuite)
	if suite == nil {
		c.sendAlert(alertHandshakeFailure)
		return nil, isUseFakeSNIIP, errors.New("tls: server chose an unconfigured cipher suite")
	}
	fHash := newFinishedHash(c.vers, suite)

	msgAny, err = c.readHandshake(&fHash)
	if err != nil {
		return nil, isUseFakeSNIIP, err
	}

	certMsg, ok := msgAny.(*certificateMsg)
	if !ok || len(certMsg.certificates) == 0 {
		c.sendAlert(alertUnexpectedMessage)
		return nil, isUseFakeSNIIP, errors.New("unexpected message")
	}
	res.tls12Response.certificate = certMsg

	msgAny, err = c.readHandshake(&fHash)
	if err != nil {
		return nil, isUseFakeSNIIP, err
	}

	certStatusMsg, ok := msgAny.(*certificateStatusMsg)
	if ok {
		if !serverHello.ocspStapling {
			// If a server returns a "CertificateStatus" message, then the
			// server MUST have included an extension of type "status_request"
			// with empty "extension_data" in the extended server hello.

			c.sendAlert(alertUnexpectedMessage)
			return nil, isUseFakeSNIIP, errors.New("tls: received unexpected CertificateStatus message")
		}
		msgAny, err = c.readHandshake(&fHash)
		if err != nil {
			return nil, isUseFakeSNIIP, err
		}
	}
	res.tls12Response.certificateStatus = certStatusMsg

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
		return &res, isUseFakeSNIIP, nil
	}

	if err := c.writeChangeCipherRecord(); err != nil {
		return &res, isUseFakeSNIIP, nil
	}
	if _, err := c.writeHandshakeRecord(&finishedMsg{}, &fHash); err != nil {
		return &res, isUseFakeSNIIP, nil
	}
	if _, err := c.flush(); err != nil {
		return &res, isUseFakeSNIIP, nil
	}
	c.isHandshakeComplete.Store(true)
	return &res, isUseFakeSNIIP, nil
}

func serverFailHandler(ctx context.Context, conn CloseWriteConn, config *Config, msg *clientHelloMsg) error {
	if msg == nil {
		c := Conn{
			conn:   conn,
			config: config,
		}
		c.sendAlert(alertIllegalParameter)
		c.Close()
		return errors.New("REALITY: client hello msg is nil")
	}
	if config.Show {
		fmt.Printf("REALITY remoteAddr: %v\tforwarded SNI: %v\n", conn.RemoteAddr(), msg.serverName)
	}
	destTarget, isUseFakeSNIIP := dest.LoadLatestServerName()
	switch {
	case len(destTarget) == 0:
		destTarget = config.Dest
	case isUseFakeSNIIP:
		if msg.serverName != destTarget {
			c := Conn{
				conn:   conn,
				config: config,
			}
			c.sendAlert(alertUnrecognizedName)
			c.Close()
			return errors.New("REALITY: client hello msg fake server name is wrong")
		}
		destTarget = fmt.Sprintf("%s:443", config.FakeSNIIP)
	default:
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
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\terror: %v\n", remoteAddr, err)
		}
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

	targetResponse, err := processTargetConnWithCache(ctx, config, clientHelloMsg)
	if err != nil {
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}

	if len(targetResponse.ServerHelloMsg.original) > size {
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}

	tlsVersion := targetResponse.ServerHelloMsg.vers
	if targetResponse.ServerHelloMsg.supportedVersion != 0 {
		tlsVersion = targetResponse.ServerHelloMsg.supportedVersion
	}

	if tlsVersion == VersionTLS13 {
		hs := serverHandshakeStateTLS13{
			c:   c,
			ctx: context.Background(),
		}
		hs.clientHello = clientHelloMsg
		hs.hello = targetResponse.ServerHelloMsg
		copy(hs.c.out.handshakeLen[:], targetResponse.tls13Response.handshakeLen[:])
		if hs.c.out.handshakeLen[2] > 512 {
			hs.c.out.handshakeBuf = make([]byte, 0, size)
		}
		err = hs.handshake()
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.handshake() err: %v\n", remoteAddr, err)
		}
		if err != nil {
			conn.Close()
			return nil, err
		}

		err = hs.readClientFinished()
		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.readClientFinished() err: %v\n", remoteAddr, err)
		}
		if err != nil {
			conn.Close()
			return nil, err
		}
		hs.c.isHandshakeComplete.Store(true)

		if config.Show {
			fmt.Printf("REALITY remoteAddr: %v\ths.c.handshakeStatus: %v\n", remoteAddr, hs.c.isHandshakeComplete.Load())
		}

		return hs.c, nil
	}

	c.vers = tlsVersion
	cert := certByCertMsg(targetResponse.tls12Response.certificate, config)
	if cert == nil {
		return nil, serverFailHandler(ctx, underlying, config, clientHelloMsg)
	}
	hs := serverHandshakeState{
		c:    c,
		ctx:  context.Background(),
		cert: cert,
	}
	hs.clientHello = clientHelloMsg
	hs.hello = targetResponse.ServerHelloMsg
	err = hs.handshake(targetResponse.tls12Response.certificate, targetResponse.tls12Response.certificateStatus)
	if config.Show {
		fmt.Printf("REALITY remoteAddr: %v\ths.readClientFinished() err: %v\n", remoteAddr, err)
	}
	if err != nil {
		conn.Close()
		return nil, err
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
