%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:01 EST 2020

% Result     : Theorem 14.05s
% Output     : Refutation 14.05s
% Verified   : 
% Statistics : Number of formulae       :   79 (1599 expanded)
%              Number of leaves         :   16 ( 576 expanded)
%              Depth                    :   19
%              Number of atoms          :   81 (1601 expanded)
%              Number of equality atoms :   80 (1600 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51079,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50881,f18097])).

fof(f18097,plain,(
    ! [X505,X502,X504,X506,X503] : k2_enumset1(k4_tarski(k4_tarski(X502,X503),X505),k4_tarski(k4_tarski(X502,X503),X506),k4_tarski(k4_tarski(X502,X504),X505),k4_tarski(k4_tarski(X502,X504),X506)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X502,X502,X502,X502),k2_enumset1(X503,X503,X503,X504)),k2_enumset1(X505,X505,X505,X506)) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f29,f37,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f32,f36,f36])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f50881,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(superposition,[],[f40,f43023])).

fof(f43023,plain,(
    ! [X447,X449,X446,X448] : k2_enumset1(X449,X448,X446,X447) = k2_enumset1(X449,X446,X448,X447) ),
    inference(superposition,[],[f42616,f634])).

fof(f634,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X10,X11,X8,X9) = k2_enumset1(X8,X9,X11,X10) ),
    inference(superposition,[],[f58,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f36,f36])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f31,f36,f36])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X6,X6,X6,X7),k2_enumset1(X4,X4,X4,X5)) ),
    inference(superposition,[],[f39,f52])).

fof(f52,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,X3) ),
    inference(superposition,[],[f48,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f24,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f38,f41])).

fof(f42616,plain,(
    ! [X35,X33,X36,X34] : k2_enumset1(X33,X35,X36,X34) = k2_enumset1(X35,X34,X36,X33) ),
    inference(superposition,[],[f2326,f2227])).

fof(f2227,plain,(
    ! [X125,X123,X124,X122] : k4_enumset1(X122,X122,X122,X123,X124,X125) = k2_enumset1(X122,X124,X125,X123) ),
    inference(forward_demodulation,[],[f2181,f1423])).

fof(f1423,plain,(
    ! [X4,X2,X5,X3] : k2_enumset1(X2,X3,X5,X4) = k2_xboole_0(k2_enumset1(X2,X3,X4,X4),k2_enumset1(X5,X5,X5,X5)) ),
    inference(superposition,[],[f47,f508])).

fof(f508,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X1,X0) = k4_enumset1(X2,X2,X3,X0,X0,X1) ),
    inference(forward_demodulation,[],[f468,f154])).

fof(f154,plain,(
    ! [X6,X8,X7,X9] : k2_enumset1(X8,X9,X6,X7) = k2_xboole_0(k2_enumset1(X8,X8,X8,X9),k2_enumset1(X6,X6,X7,X6)) ),
    inference(superposition,[],[f39,f130])).

fof(f130,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X5,X4,X6,X7) = k2_enumset1(X4,X5,X7,X6) ),
    inference(superposition,[],[f56,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X3)) ),
    inference(superposition,[],[f39,f41])).

fof(f468,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X2,X2,X3,X0,X0,X1) = k2_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X0,X1)) ),
    inference(superposition,[],[f46,f142])).

fof(f142,plain,(
    ! [X4,X5] : k2_enumset1(X5,X5,X5,X4) = k2_enumset1(X4,X4,X5,X4) ),
    inference(superposition,[],[f130,f41])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f34,f33,f36,f28])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)) ),
    inference(definition_unfolding,[],[f35,f33,f37])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f2181,plain,(
    ! [X125,X123,X124,X122] : k4_enumset1(X122,X122,X122,X123,X124,X125) = k2_xboole_0(k2_enumset1(X122,X124,X123,X123),k2_enumset1(X125,X125,X125,X125)) ),
    inference(superposition,[],[f47,f1923])).

fof(f1923,plain,(
    ! [X4,X2,X3] : k2_enumset1(X2,X2,X4,X3) = k2_enumset1(X2,X3,X4,X4) ),
    inference(superposition,[],[f1518,f508])).

fof(f1518,plain,(
    ! [X23,X21,X22] : k4_enumset1(X21,X21,X22,X23,X23,X23) = k2_enumset1(X21,X21,X23,X22) ),
    inference(forward_demodulation,[],[f1475,f1504])).

fof(f1504,plain,(
    ! [X10,X11,X9] : k2_enumset1(X9,X9,X11,X10) = k4_enumset1(X9,X9,X9,X9,X10,X11) ),
    inference(forward_demodulation,[],[f1435,f1423])).

fof(f1435,plain,(
    ! [X10,X11,X9] : k4_enumset1(X9,X9,X9,X9,X10,X11) = k2_xboole_0(k2_enumset1(X9,X9,X10,X10),k2_enumset1(X11,X11,X11,X11)) ),
    inference(superposition,[],[f47,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X0,X0,X1,X1) ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f25,f36,f37,f37])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1475,plain,(
    ! [X23,X21,X22] : k4_enumset1(X21,X21,X22,X23,X23,X23) = k4_enumset1(X21,X21,X21,X21,X22,X23) ),
    inference(superposition,[],[f47,f46])).

fof(f2326,plain,(
    ! [X127,X125,X128,X126] : k4_enumset1(X125,X125,X125,X126,X127,X128) = k2_enumset1(X127,X126,X128,X125) ),
    inference(forward_demodulation,[],[f2284,f2096])).

fof(f2096,plain,(
    ! [X103,X105,X102,X104] : k2_enumset1(X102,X103,X105,X104) = k2_xboole_0(k2_enumset1(X103,X103,X104,X102),k2_enumset1(X105,X105,X105,X105)) ),
    inference(forward_demodulation,[],[f2013,f508])).

fof(f2013,plain,(
    ! [X103,X105,X102,X104] : k4_enumset1(X102,X102,X103,X104,X104,X105) = k2_xboole_0(k2_enumset1(X103,X103,X104,X102),k2_enumset1(X105,X105,X105,X105)) ),
    inference(superposition,[],[f47,f1924])).

fof(f1924,plain,(
    ! [X6,X7,X5] : k2_enumset1(X6,X5,X7,X7) = k2_enumset1(X5,X5,X7,X6) ),
    inference(superposition,[],[f1518,f488])).

fof(f488,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X2,X3) = k2_enumset1(X1,X0,X3,X2) ),
    inference(superposition,[],[f46,f112])).

fof(f112,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X10,X11,X8,X9) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X9,X9,X9,X8)) ),
    inference(superposition,[],[f54,f41])).

fof(f2284,plain,(
    ! [X127,X125,X128,X126] : k4_enumset1(X125,X125,X125,X126,X127,X128) = k2_xboole_0(k2_enumset1(X126,X126,X125,X127),k2_enumset1(X128,X128,X128,X128)) ),
    inference(superposition,[],[f47,f1954])).

fof(f1954,plain,(
    ! [X45,X43,X44] : k2_enumset1(X45,X45,X44,X43) = k2_enumset1(X44,X44,X45,X43) ),
    inference(superposition,[],[f1924,f633])).

fof(f633,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X6,X7,X4,X5) = k2_enumset1(X5,X4,X7,X6) ),
    inference(superposition,[],[f58,f112])).

fof(f40,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(definition_unfolding,[],[f20,f26,f37,f36,f36,f27,f27,f27,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (9170)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.44  % (9158)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (9153)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (9155)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (9169)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (9157)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (9163)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (9164)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (9164)Refutation not found, incomplete strategy% (9164)------------------------------
% 0.21/0.48  % (9164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9164)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9164)Memory used [KB]: 10618
% 0.21/0.48  % (9164)Time elapsed: 0.072 s
% 0.21/0.48  % (9164)------------------------------
% 0.21/0.48  % (9164)------------------------------
% 0.21/0.48  % (9162)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (9154)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (9161)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (9156)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (9168)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (9160)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (9166)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (9167)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (9165)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (9159)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 5.46/1.04  % (9157)Time limit reached!
% 5.46/1.04  % (9157)------------------------------
% 5.46/1.04  % (9157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.46/1.04  % (9157)Termination reason: Time limit
% 5.46/1.04  % (9157)Termination phase: Saturation
% 5.46/1.04  
% 5.46/1.04  % (9157)Memory used [KB]: 10874
% 5.46/1.04  % (9157)Time elapsed: 0.600 s
% 5.46/1.04  % (9157)------------------------------
% 5.46/1.04  % (9157)------------------------------
% 12.54/1.94  % (9159)Time limit reached!
% 12.54/1.94  % (9159)------------------------------
% 12.54/1.94  % (9159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.94  % (9159)Termination reason: Time limit
% 12.54/1.94  % (9159)Termination phase: Saturation
% 12.54/1.94  
% 12.54/1.94  % (9159)Memory used [KB]: 17142
% 12.54/1.94  % (9159)Time elapsed: 1.500 s
% 12.54/1.94  % (9159)------------------------------
% 12.54/1.94  % (9159)------------------------------
% 12.54/1.97  % (9158)Time limit reached!
% 12.54/1.97  % (9158)------------------------------
% 12.54/1.97  % (9158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.97  % (9158)Termination reason: Time limit
% 12.54/1.97  
% 12.54/1.97  % (9158)Memory used [KB]: 47461
% 12.54/1.97  % (9158)Time elapsed: 1.522 s
% 12.54/1.97  % (9158)------------------------------
% 12.54/1.97  % (9158)------------------------------
% 14.05/2.14  % (9162)Refutation found. Thanks to Tanya!
% 14.05/2.14  % SZS status Theorem for theBenchmark
% 14.05/2.14  % SZS output start Proof for theBenchmark
% 14.05/2.14  fof(f51079,plain,(
% 14.05/2.14    $false),
% 14.05/2.14    inference(subsumption_resolution,[],[f50881,f18097])).
% 14.05/2.14  fof(f18097,plain,(
% 14.05/2.14    ( ! [X505,X502,X504,X506,X503] : (k2_enumset1(k4_tarski(k4_tarski(X502,X503),X505),k4_tarski(k4_tarski(X502,X503),X506),k4_tarski(k4_tarski(X502,X504),X505),k4_tarski(k4_tarski(X502,X504),X506)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X502,X502,X502,X502),k2_enumset1(X503,X503,X503,X504)),k2_enumset1(X505,X505,X505,X506))) )),
% 14.05/2.14    inference(superposition,[],[f45,f44])).
% 14.05/2.14  fof(f44,plain,(
% 14.05/2.14    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f29,f37,f36,f36])).
% 14.05/2.14  fof(f36,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 14.05/2.14    inference(definition_unfolding,[],[f23,f28])).
% 14.05/2.14  fof(f28,plain,(
% 14.05/2.14    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f8])).
% 14.05/2.14  fof(f8,axiom,(
% 14.05/2.14    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 14.05/2.14  fof(f23,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f7])).
% 14.05/2.14  fof(f7,axiom,(
% 14.05/2.14    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 14.05/2.14  fof(f37,plain,(
% 14.05/2.14    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 14.05/2.14    inference(definition_unfolding,[],[f21,f36])).
% 14.05/2.14  fof(f21,plain,(
% 14.05/2.14    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f6])).
% 14.05/2.14  fof(f6,axiom,(
% 14.05/2.14    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 14.05/2.14  fof(f29,plain,(
% 14.05/2.14    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 14.05/2.14    inference(cnf_transformation,[],[f12])).
% 14.05/2.14  fof(f12,axiom,(
% 14.05/2.14    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 14.05/2.14  fof(f45,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f32,f36,f36])).
% 14.05/2.14  fof(f32,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 14.05/2.14    inference(cnf_transformation,[],[f11])).
% 14.05/2.14  fof(f11,axiom,(
% 14.05/2.14    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 14.05/2.14  fof(f50881,plain,(
% 14.05/2.14    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 14.05/2.14    inference(superposition,[],[f40,f43023])).
% 14.05/2.14  fof(f43023,plain,(
% 14.05/2.14    ( ! [X447,X449,X446,X448] : (k2_enumset1(X449,X448,X446,X447) = k2_enumset1(X449,X446,X448,X447)) )),
% 14.05/2.14    inference(superposition,[],[f42616,f634])).
% 14.05/2.14  fof(f634,plain,(
% 14.05/2.14    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X11,X8,X9) = k2_enumset1(X8,X9,X11,X10)) )),
% 14.05/2.14    inference(superposition,[],[f58,f56])).
% 14.05/2.14  fof(f56,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X0))) )),
% 14.05/2.14    inference(superposition,[],[f39,f41])).
% 14.05/2.14  fof(f41,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 14.05/2.14    inference(definition_unfolding,[],[f22,f36,f36])).
% 14.05/2.14  fof(f22,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f1])).
% 14.05/2.14  fof(f1,axiom,(
% 14.05/2.14    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 14.05/2.14  fof(f39,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f31,f36,f36])).
% 14.05/2.14  fof(f31,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 14.05/2.14    inference(cnf_transformation,[],[f2])).
% 14.05/2.14  fof(f2,axiom,(
% 14.05/2.14    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 14.05/2.14  fof(f58,plain,(
% 14.05/2.14    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X6,X6,X6,X7),k2_enumset1(X4,X4,X4,X5))) )),
% 14.05/2.14    inference(superposition,[],[f39,f52])).
% 14.05/2.14  fof(f52,plain,(
% 14.05/2.14    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,X3)) )),
% 14.05/2.14    inference(superposition,[],[f48,f38])).
% 14.05/2.14  fof(f38,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f24,f36])).
% 14.05/2.14  fof(f24,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f10])).
% 14.05/2.14  fof(f10,axiom,(
% 14.05/2.14    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 14.05/2.14  fof(f48,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 14.05/2.14    inference(superposition,[],[f38,f41])).
% 14.05/2.14  fof(f42616,plain,(
% 14.05/2.14    ( ! [X35,X33,X36,X34] : (k2_enumset1(X33,X35,X36,X34) = k2_enumset1(X35,X34,X36,X33)) )),
% 14.05/2.14    inference(superposition,[],[f2326,f2227])).
% 14.05/2.14  fof(f2227,plain,(
% 14.05/2.14    ( ! [X125,X123,X124,X122] : (k4_enumset1(X122,X122,X122,X123,X124,X125) = k2_enumset1(X122,X124,X125,X123)) )),
% 14.05/2.14    inference(forward_demodulation,[],[f2181,f1423])).
% 14.05/2.14  fof(f1423,plain,(
% 14.05/2.14    ( ! [X4,X2,X5,X3] : (k2_enumset1(X2,X3,X5,X4) = k2_xboole_0(k2_enumset1(X2,X3,X4,X4),k2_enumset1(X5,X5,X5,X5))) )),
% 14.05/2.14    inference(superposition,[],[f47,f508])).
% 14.05/2.14  fof(f508,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X1,X0) = k4_enumset1(X2,X2,X3,X0,X0,X1)) )),
% 14.05/2.14    inference(forward_demodulation,[],[f468,f154])).
% 14.05/2.14  fof(f154,plain,(
% 14.05/2.14    ( ! [X6,X8,X7,X9] : (k2_enumset1(X8,X9,X6,X7) = k2_xboole_0(k2_enumset1(X8,X8,X8,X9),k2_enumset1(X6,X6,X7,X6))) )),
% 14.05/2.14    inference(superposition,[],[f39,f130])).
% 14.05/2.14  fof(f130,plain,(
% 14.05/2.14    ( ! [X6,X4,X7,X5] : (k2_enumset1(X5,X4,X6,X7) = k2_enumset1(X4,X5,X7,X6)) )),
% 14.05/2.14    inference(superposition,[],[f56,f54])).
% 14.05/2.14  fof(f54,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X3))) )),
% 14.05/2.14    inference(superposition,[],[f39,f41])).
% 14.05/2.14  fof(f468,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k4_enumset1(X2,X2,X3,X0,X0,X1) = k2_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X0,X1))) )),
% 14.05/2.14    inference(superposition,[],[f46,f142])).
% 14.05/2.14  fof(f142,plain,(
% 14.05/2.14    ( ! [X4,X5] : (k2_enumset1(X5,X5,X5,X4) = k2_enumset1(X4,X4,X5,X4)) )),
% 14.05/2.14    inference(superposition,[],[f130,f41])).
% 14.05/2.14  fof(f46,plain,(
% 14.05/2.14    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f34,f33,f36,f28])).
% 14.05/2.14  fof(f33,plain,(
% 14.05/2.14    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f9])).
% 14.05/2.14  fof(f9,axiom,(
% 14.05/2.14    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 14.05/2.14  fof(f34,plain,(
% 14.05/2.14    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 14.05/2.14    inference(cnf_transformation,[],[f4])).
% 14.05/2.14  fof(f4,axiom,(
% 14.05/2.14    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 14.05/2.14  fof(f47,plain,(
% 14.05/2.14    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f35,f33,f37])).
% 14.05/2.14  fof(f35,plain,(
% 14.05/2.14    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 14.05/2.14    inference(cnf_transformation,[],[f5])).
% 14.05/2.14  fof(f5,axiom,(
% 14.05/2.14    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 14.05/2.14  fof(f2181,plain,(
% 14.05/2.14    ( ! [X125,X123,X124,X122] : (k4_enumset1(X122,X122,X122,X123,X124,X125) = k2_xboole_0(k2_enumset1(X122,X124,X123,X123),k2_enumset1(X125,X125,X125,X125))) )),
% 14.05/2.14    inference(superposition,[],[f47,f1923])).
% 14.05/2.14  fof(f1923,plain,(
% 14.05/2.14    ( ! [X4,X2,X3] : (k2_enumset1(X2,X2,X4,X3) = k2_enumset1(X2,X3,X4,X4)) )),
% 14.05/2.14    inference(superposition,[],[f1518,f508])).
% 14.05/2.14  fof(f1518,plain,(
% 14.05/2.14    ( ! [X23,X21,X22] : (k4_enumset1(X21,X21,X22,X23,X23,X23) = k2_enumset1(X21,X21,X23,X22)) )),
% 14.05/2.14    inference(forward_demodulation,[],[f1475,f1504])).
% 14.05/2.14  fof(f1504,plain,(
% 14.05/2.14    ( ! [X10,X11,X9] : (k2_enumset1(X9,X9,X11,X10) = k4_enumset1(X9,X9,X9,X9,X10,X11)) )),
% 14.05/2.14    inference(forward_demodulation,[],[f1435,f1423])).
% 14.05/2.14  fof(f1435,plain,(
% 14.05/2.14    ( ! [X10,X11,X9] : (k4_enumset1(X9,X9,X9,X9,X10,X11) = k2_xboole_0(k2_enumset1(X9,X9,X10,X10),k2_enumset1(X11,X11,X11,X11))) )),
% 14.05/2.14    inference(superposition,[],[f47,f62])).
% 14.05/2.14  fof(f62,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X0,X0,X1,X1)) )),
% 14.05/2.14    inference(superposition,[],[f42,f39])).
% 14.05/2.14  fof(f42,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 14.05/2.14    inference(definition_unfolding,[],[f25,f36,f37,f37])).
% 14.05/2.14  fof(f25,plain,(
% 14.05/2.14    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 14.05/2.14    inference(cnf_transformation,[],[f3])).
% 14.05/2.14  fof(f3,axiom,(
% 14.05/2.14    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 14.05/2.14  fof(f1475,plain,(
% 14.05/2.14    ( ! [X23,X21,X22] : (k4_enumset1(X21,X21,X22,X23,X23,X23) = k4_enumset1(X21,X21,X21,X21,X22,X23)) )),
% 14.05/2.14    inference(superposition,[],[f47,f46])).
% 14.05/2.14  fof(f2326,plain,(
% 14.05/2.14    ( ! [X127,X125,X128,X126] : (k4_enumset1(X125,X125,X125,X126,X127,X128) = k2_enumset1(X127,X126,X128,X125)) )),
% 14.05/2.14    inference(forward_demodulation,[],[f2284,f2096])).
% 14.05/2.14  fof(f2096,plain,(
% 14.05/2.14    ( ! [X103,X105,X102,X104] : (k2_enumset1(X102,X103,X105,X104) = k2_xboole_0(k2_enumset1(X103,X103,X104,X102),k2_enumset1(X105,X105,X105,X105))) )),
% 14.05/2.14    inference(forward_demodulation,[],[f2013,f508])).
% 14.05/2.14  fof(f2013,plain,(
% 14.05/2.14    ( ! [X103,X105,X102,X104] : (k4_enumset1(X102,X102,X103,X104,X104,X105) = k2_xboole_0(k2_enumset1(X103,X103,X104,X102),k2_enumset1(X105,X105,X105,X105))) )),
% 14.05/2.14    inference(superposition,[],[f47,f1924])).
% 14.05/2.14  fof(f1924,plain,(
% 14.05/2.14    ( ! [X6,X7,X5] : (k2_enumset1(X6,X5,X7,X7) = k2_enumset1(X5,X5,X7,X6)) )),
% 14.05/2.14    inference(superposition,[],[f1518,f488])).
% 14.05/2.14  fof(f488,plain,(
% 14.05/2.14    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X2,X3) = k2_enumset1(X1,X0,X3,X2)) )),
% 14.05/2.14    inference(superposition,[],[f46,f112])).
% 14.05/2.14  fof(f112,plain,(
% 14.05/2.14    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X11,X8,X9) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X9,X9,X9,X8))) )),
% 14.05/2.14    inference(superposition,[],[f54,f41])).
% 14.05/2.14  fof(f2284,plain,(
% 14.05/2.14    ( ! [X127,X125,X128,X126] : (k4_enumset1(X125,X125,X125,X126,X127,X128) = k2_xboole_0(k2_enumset1(X126,X126,X125,X127),k2_enumset1(X128,X128,X128,X128))) )),
% 14.05/2.14    inference(superposition,[],[f47,f1954])).
% 14.05/2.14  fof(f1954,plain,(
% 14.05/2.14    ( ! [X45,X43,X44] : (k2_enumset1(X45,X45,X44,X43) = k2_enumset1(X44,X44,X45,X43)) )),
% 14.05/2.14    inference(superposition,[],[f1924,f633])).
% 14.05/2.14  fof(f633,plain,(
% 14.05/2.14    ( ! [X6,X4,X7,X5] : (k2_enumset1(X6,X7,X4,X5) = k2_enumset1(X5,X4,X7,X6)) )),
% 14.05/2.14    inference(superposition,[],[f58,f112])).
% 14.05/2.14  fof(f40,plain,(
% 14.05/2.14    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 14.05/2.14    inference(definition_unfolding,[],[f20,f26,f37,f36,f36,f27,f27,f27,f27])).
% 14.05/2.14  fof(f27,plain,(
% 14.05/2.14    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f13])).
% 14.05/2.14  fof(f13,axiom,(
% 14.05/2.14    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 14.05/2.14  fof(f26,plain,(
% 14.05/2.14    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 14.05/2.14    inference(cnf_transformation,[],[f14])).
% 14.05/2.14  fof(f14,axiom,(
% 14.05/2.14    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 14.05/2.14  fof(f20,plain,(
% 14.05/2.14    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 14.05/2.14    inference(cnf_transformation,[],[f19])).
% 14.05/2.14  fof(f19,plain,(
% 14.05/2.14    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 14.05/2.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 14.05/2.14  fof(f18,plain,(
% 14.05/2.14    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 14.05/2.14    introduced(choice_axiom,[])).
% 14.05/2.14  fof(f17,plain,(
% 14.05/2.14    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 14.05/2.14    inference(ennf_transformation,[],[f16])).
% 14.05/2.14  fof(f16,negated_conjecture,(
% 14.05/2.14    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 14.05/2.14    inference(negated_conjecture,[],[f15])).
% 14.05/2.14  fof(f15,conjecture,(
% 14.05/2.14    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 14.05/2.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
% 14.05/2.14  % SZS output end Proof for theBenchmark
% 14.05/2.14  % (9162)------------------------------
% 14.05/2.14  % (9162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.05/2.14  % (9162)Termination reason: Refutation
% 14.05/2.14  
% 14.05/2.14  % (9162)Memory used [KB]: 26865
% 14.05/2.14  % (9162)Time elapsed: 1.736 s
% 14.05/2.14  % (9162)------------------------------
% 14.05/2.14  % (9162)------------------------------
% 14.05/2.15  % (9152)Success in time 1.788 s
%------------------------------------------------------------------------------
