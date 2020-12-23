%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:49 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  104 (17958 expanded)
%              Number of leaves         :   13 (6667 expanded)
%              Depth                    :   35
%              Number of atoms          :  108 (17963 expanded)
%              Number of equality atoms :  101 (17955 expanded)
%              Maximal formula depth    :   10 (   7 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1010,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f1000])).

fof(f1000,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f976])).

fof(f976,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f40,f699])).

fof(f699,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X7,X8,X9,X10,X11,X12)) = k2_xboole_0(k2_tarski(X6,X6),k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X7,X8,X9,X10,X11,X12))) ),
    inference(superposition,[],[f541,f525])).

fof(f525,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X6))) ),
    inference(forward_demodulation,[],[f512,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X2,X2,X3,X0,X1,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(definition_unfolding,[],[f18,f17,f17])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4))) ),
    inference(forward_demodulation,[],[f65,f31])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4))) ),
    inference(superposition,[],[f44,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X5))) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(X3,X3)),k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6))) ),
    inference(definition_unfolding,[],[f24,f27,f29,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(X3,X3)) ),
    inference(definition_unfolding,[],[f20,f28,f17])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f512,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_enumset1(X3,X3,X4,X5,X6,X6)) ),
    inference(backward_demodulation,[],[f183,f508])).

fof(f508,plain,(
    ! [X14,X17,X15,X13,X16] : k4_enumset1(X13,X13,X14,X15,X16,X17) = k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))) ),
    inference(forward_demodulation,[],[f507,f238])).

fof(f238,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X0,X1)))) = k4_enumset1(X2,X3,X4,X5,X0,X1) ),
    inference(backward_demodulation,[],[f198,f236])).

fof(f236,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(backward_demodulation,[],[f209,f234])).

fof(f234,plain,(
    ! [X23,X21,X19,X22,X20,X18] : k2_xboole_0(k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) = k4_enumset1(X18,X19,X20,X21,X22,X23) ),
    inference(backward_demodulation,[],[f132,f233])).

fof(f233,plain,(
    ! [X30,X35,X33,X31,X34,X32] : k2_xboole_0(k2_xboole_0(k2_tarski(X35,X35),k2_tarski(X30,X31)),k2_xboole_0(k2_tarski(X32,X33),k2_tarski(X34,X34))) = k4_enumset1(X35,X30,X31,X32,X33,X34) ),
    inference(forward_demodulation,[],[f175,f222])).

fof(f222,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)))) ),
    inference(forward_demodulation,[],[f221,f126])).

fof(f126,plain,(
    ! [X26,X24,X23,X27,X25,X22] : k2_xboole_0(k2_xboole_0(k2_tarski(X27,X22),k2_tarski(X23,X23)),k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26))) = k4_enumset1(X27,X22,X23,X24,X25,X26) ),
    inference(backward_demodulation,[],[f97,f121])).

fof(f121,plain,(
    ! [X30,X28,X33,X31,X29,X32] : k2_xboole_0(k2_tarski(X33,X33),k2_xboole_0(k2_tarski(X28,X29),k2_xboole_0(k2_tarski(X30,X30),k2_tarski(X31,X32)))) = k4_enumset1(X33,X28,X29,X30,X31,X32) ),
    inference(backward_demodulation,[],[f98,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5))) ),
    inference(forward_demodulation,[],[f105,f31])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5))) ),
    inference(superposition,[],[f53,f32])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X6,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5))) ),
    inference(forward_demodulation,[],[f49,f31])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X6,X6),k2_tarski(X0,X0)),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5))) = k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f36,f32])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(X3,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))) ),
    inference(definition_unfolding,[],[f26,f30,f29,f29])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f25,f17,f27])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f98,plain,(
    ! [X30,X28,X33,X31,X29,X32] : k2_xboole_0(k2_tarski(X33,X28),k2_xboole_0(k2_xboole_0(k2_tarski(X29,X29),k2_tarski(X30,X31)),k2_tarski(X32,X32))) = k2_xboole_0(k2_tarski(X33,X33),k2_xboole_0(k2_tarski(X28,X29),k2_xboole_0(k2_tarski(X30,X30),k2_tarski(X31,X32)))) ),
    inference(superposition,[],[f42,f76])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5))) ),
    inference(superposition,[],[f34,f31])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_xboole_0(k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X5)),k2_tarski(X6,X6))) ),
    inference(definition_unfolding,[],[f23,f27,f28,f29])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f97,plain,(
    ! [X26,X24,X23,X27,X25,X22] : k2_xboole_0(k2_xboole_0(k2_tarski(X27,X22),k2_tarski(X23,X23)),k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26))) = k2_xboole_0(k2_tarski(X27,X27),k2_xboole_0(k2_tarski(X22,X23),k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26)))) ),
    inference(superposition,[],[f44,f76])).

fof(f221,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X5,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4))) = k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)))) ),
    inference(forward_demodulation,[],[f220,f31])).

fof(f220,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)))) = k2_xboole_0(k2_xboole_0(k2_tarski(X5,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X4)))) ),
    inference(forward_demodulation,[],[f171,f181])).

fof(f181,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X0,X1)) = k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X0,X1))) ),
    inference(backward_demodulation,[],[f58,f169])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k4_enumset1(X2,X3,X0,X0,X0,X1) ),
    inference(superposition,[],[f148,f31])).

fof(f148,plain,(
    ! [X14,X12,X15,X13,X11] : k4_enumset1(X11,X12,X13,X14,X14,X15) = k2_xboole_0(k2_tarski(X11,X12),k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15))) ),
    inference(forward_demodulation,[],[f141,f31])).

fof(f141,plain,(
    ! [X14,X12,X15,X13,X11] : k4_enumset1(X11,X12,X13,X14,X14,X15) = k2_xboole_0(k2_xboole_0(k2_tarski(X11,X11),k2_tarski(X12,X12)),k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15))) ),
    inference(superposition,[],[f129,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X1,X1,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X5,X5))) ),
    inference(superposition,[],[f34,f31])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)) ),
    inference(backward_demodulation,[],[f44,f126])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X0,X0,X1)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f43,f31])).

fof(f171,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X5,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4))) = k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)))) ),
    inference(superposition,[],[f53,f148])).

fof(f175,plain,(
    ! [X30,X35,X33,X31,X34,X32] : k2_xboole_0(k2_xboole_0(k2_tarski(X35,X35),k2_tarski(X30,X31)),k2_xboole_0(k2_tarski(X32,X33),k2_tarski(X34,X34))) = k2_xboole_0(k2_tarski(X35,X35),k2_xboole_0(k2_tarski(X30,X31),k2_xboole_0(k2_tarski(X32,X33),k2_tarski(X34,X34)))) ),
    inference(superposition,[],[f43,f148])).

fof(f132,plain,(
    ! [X23,X21,X19,X22,X20,X18] : k2_xboole_0(k2_xboole_0(k2_tarski(X18,X18),k2_tarski(X19,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) = k2_xboole_0(k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) ),
    inference(forward_demodulation,[],[f108,f31])).

fof(f108,plain,(
    ! [X23,X21,X19,X22,X20,X18] : k2_xboole_0(k2_xboole_0(k2_tarski(X18,X18),k2_tarski(X19,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) = k2_xboole_0(k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X20)),k2_xboole_0(k2_xboole_0(k2_tarski(X21,X21),k2_tarski(X22,X22)),k2_tarski(X23,X23))) ),
    inference(superposition,[],[f53,f43])).

fof(f209,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_tarski(X27,X28),k2_tarski(X29,X29))) ),
    inference(forward_demodulation,[],[f208,f92])).

fof(f208,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k4_enumset1(X27,X27,X28,X29,X29,X29)) ),
    inference(forward_demodulation,[],[f207,f148])).

fof(f207,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_tarski(X27,X27),k2_xboole_0(k2_tarski(X28,X29),k2_tarski(X29,X29)))) ),
    inference(forward_demodulation,[],[f191,f181])).

fof(f191,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_xboole_0(k2_tarski(X27,X27),k2_tarski(X28,X29)),k2_tarski(X29,X29))) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) ),
    inference(backward_demodulation,[],[f109,f181])).

fof(f109,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26)),k2_tarski(X27,X27)),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_xboole_0(k2_tarski(X27,X27),k2_tarski(X28,X29)),k2_tarski(X29,X29))) ),
    inference(superposition,[],[f53,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X5,X0,X1,X1)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f35,f31])).

fof(f198,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X0,X1)))) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X5))),k2_tarski(X0,X1)) ),
    inference(backward_demodulation,[],[f180,f181])).

fof(f180,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_tarski(X0,X1)) = k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X0,X1)))) ),
    inference(backward_demodulation,[],[f160,f169])).

fof(f160,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_tarski(X0,X1)) = k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k4_enumset1(X4,X5,X0,X0,X0,X1))) ),
    inference(superposition,[],[f52,f31])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k4_enumset1(X4,X5,X0,X1,X1,X6))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X6,X6))) ),
    inference(superposition,[],[f36,f31])).

fof(f507,plain,(
    ! [X14,X17,X15,X13,X16] : k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))) = k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)))) ),
    inference(forward_demodulation,[],[f488,f181])).

fof(f488,plain,(
    ! [X14,X17,X15,X13,X16] : k2_xboole_0(k2_xboole_0(k2_tarski(X13,X13),k2_tarski(X14,X15)),k2_tarski(X16,X17)) = k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_xboole_0(k2_tarski(X13,X13),k2_tarski(X14,X15)),k2_tarski(X16,X17))) ),
    inference(superposition,[],[f32,f295])).

fof(f295,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X0,X1)) = k4_enumset1(X2,X3,X4,X0,X1,X1) ),
    inference(superposition,[],[f253,f31])).

fof(f253,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X2,X3,X4,X5,X0,X1) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f249,f237])).

fof(f237,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X1,X1,X5)) = k4_enumset1(X2,X3,X4,X0,X1,X5) ),
    inference(backward_demodulation,[],[f111,f234])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X1,X1,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)),k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X5,X5))) ),
    inference(superposition,[],[f53,f31])).

fof(f249,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X5,X0,X0,X1)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X0,X1))) ),
    inference(superposition,[],[f183,f31])).

fof(f183,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X6)))) ),
    inference(backward_demodulation,[],[f34,f181])).

fof(f541,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(forward_demodulation,[],[f540,f92])).

fof(f540,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(forward_demodulation,[],[f539,f92])).

fof(f539,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X3),k4_enumset1(X4,X4,X5,X6,X7,X7)) ),
    inference(forward_demodulation,[],[f516,f528])).

fof(f528,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X5))) ),
    inference(forward_demodulation,[],[f515,f92])).

fof(f515,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X2,X3,X4,X5,X5)) ),
    inference(backward_demodulation,[],[f193,f508])).

fof(f193,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X5)))) ),
    inference(backward_demodulation,[],[f120,f181])).

fof(f516,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X3),k2_xboole_0(k2_tarski(X4,X4),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X7)))) ),
    inference(backward_demodulation,[],[f202,f508])).

fof(f202,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3))),k2_xboole_0(k2_tarski(X4,X4),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X7)))) ),
    inference(forward_demodulation,[],[f185,f181])).

fof(f185,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3))),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7))) ),
    inference(backward_demodulation,[],[f36,f181])).

fof(f40,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl7_1
  <=> k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) = k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f41,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f33,f38])).

fof(f33,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))) ),
    inference(definition_unfolding,[],[f16,f27,f30])).

fof(f16,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (21015)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.46  % (21015)Refutation not found, incomplete strategy% (21015)------------------------------
% 0.22/0.46  % (21015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (21015)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (21015)Memory used [KB]: 10618
% 0.22/0.46  % (21015)Time elapsed: 0.037 s
% 0.22/0.46  % (21015)------------------------------
% 0.22/0.46  % (21015)------------------------------
% 0.22/0.47  % (21005)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (21009)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (21008)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (21003)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (21016)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (21014)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (21013)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (21017)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (21018)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (21011)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (21006)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (21010)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (21004)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (21020)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (21019)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (21022)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (21012)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.60/0.60  % (21019)Refutation found. Thanks to Tanya!
% 1.60/0.60  % SZS status Theorem for theBenchmark
% 1.60/0.60  % SZS output start Proof for theBenchmark
% 1.60/0.61  fof(f1010,plain,(
% 1.60/0.61    $false),
% 1.60/0.61    inference(avatar_sat_refutation,[],[f41,f1000])).
% 1.60/0.61  fof(f1000,plain,(
% 1.60/0.61    spl7_1),
% 1.60/0.61    inference(avatar_contradiction_clause,[],[f976])).
% 1.60/0.61  fof(f976,plain,(
% 1.60/0.61    $false | spl7_1),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f40,f699])).
% 1.60/0.61  fof(f699,plain,(
% 1.60/0.61    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X7,X8,X9,X10,X11,X12)) = k2_xboole_0(k2_tarski(X6,X6),k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X7,X8,X9,X10,X11,X12)))) )),
% 1.60/0.61    inference(superposition,[],[f541,f525])).
% 1.60/0.61  fof(f525,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X6)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f512,f92])).
% 1.60/0.61  fof(f92,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k4_enumset1(X2,X2,X3,X0,X1,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 1.60/0.61    inference(superposition,[],[f76,f31])).
% 1.60/0.61  fof(f31,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f18,f17,f17])).
% 1.60/0.61  fof(f17,plain,(
% 1.60/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f9])).
% 1.60/0.61  fof(f9,axiom,(
% 1.60/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.61  fof(f18,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f3])).
% 1.60/0.61  fof(f3,axiom,(
% 1.60/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.60/0.61  fof(f76,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f65,f31])).
% 1.60/0.61  fof(f65,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)))) )),
% 1.60/0.61    inference(superposition,[],[f44,f32])).
% 1.60/0.61  fof(f32,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f21,f27])).
% 1.60/0.61  fof(f27,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f22,f17])).
% 1.60/0.61  fof(f22,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f6])).
% 1.60/0.61  fof(f6,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 1.60/0.61  fof(f21,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f10])).
% 1.60/0.61  fof(f10,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.60/0.61  fof(f44,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X5)))) )),
% 1.60/0.61    inference(superposition,[],[f35,f31])).
% 1.60/0.61  fof(f35,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(X3,X3)),k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f24,f27,f29,f28])).
% 1.60/0.61  fof(f28,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f19,f17])).
% 1.60/0.61  fof(f19,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f4])).
% 1.60/0.61  fof(f4,axiom,(
% 1.60/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.60/0.61  fof(f29,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(X3,X3))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f20,f28,f17])).
% 1.60/0.61  fof(f20,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f5])).
% 1.60/0.61  fof(f5,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.60/0.61  fof(f24,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f1])).
% 1.60/0.61  fof(f1,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 1.60/0.61  fof(f512,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_enumset1(X3,X3,X4,X5,X6,X6))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f183,f508])).
% 1.60/0.61  fof(f508,plain,(
% 1.60/0.61    ( ! [X14,X17,X15,X13,X16] : (k4_enumset1(X13,X13,X14,X15,X16,X17) = k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f507,f238])).
% 1.60/0.61  fof(f238,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X0,X1)))) = k4_enumset1(X2,X3,X4,X5,X0,X1)) )),
% 1.60/0.61    inference(backward_demodulation,[],[f198,f236])).
% 1.60/0.61  fof(f236,plain,(
% 1.60/0.61    ( ! [X28,X26,X24,X29,X27,X25] : (k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k4_enumset1(X24,X25,X26,X27,X28,X29)) )),
% 1.60/0.61    inference(backward_demodulation,[],[f209,f234])).
% 1.60/0.61  fof(f234,plain,(
% 1.60/0.61    ( ! [X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) = k4_enumset1(X18,X19,X20,X21,X22,X23)) )),
% 1.60/0.61    inference(backward_demodulation,[],[f132,f233])).
% 1.60/0.61  fof(f233,plain,(
% 1.60/0.61    ( ! [X30,X35,X33,X31,X34,X32] : (k2_xboole_0(k2_xboole_0(k2_tarski(X35,X35),k2_tarski(X30,X31)),k2_xboole_0(k2_tarski(X32,X33),k2_tarski(X34,X34))) = k4_enumset1(X35,X30,X31,X32,X33,X34)) )),
% 1.60/0.61    inference(forward_demodulation,[],[f175,f222])).
% 1.60/0.61  fof(f222,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4))))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f221,f126])).
% 1.60/0.61  fof(f126,plain,(
% 1.60/0.61    ( ! [X26,X24,X23,X27,X25,X22] : (k2_xboole_0(k2_xboole_0(k2_tarski(X27,X22),k2_tarski(X23,X23)),k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26))) = k4_enumset1(X27,X22,X23,X24,X25,X26)) )),
% 1.60/0.61    inference(backward_demodulation,[],[f97,f121])).
% 1.60/0.61  fof(f121,plain,(
% 1.60/0.61    ( ! [X30,X28,X33,X31,X29,X32] : (k2_xboole_0(k2_tarski(X33,X33),k2_xboole_0(k2_tarski(X28,X29),k2_xboole_0(k2_tarski(X30,X30),k2_tarski(X31,X32)))) = k4_enumset1(X33,X28,X29,X30,X31,X32)) )),
% 1.60/0.61    inference(backward_demodulation,[],[f98,f120])).
% 1.60/0.61  fof(f120,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f105,f31])).
% 1.60/0.61  fof(f105,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)))) )),
% 1.60/0.61    inference(superposition,[],[f53,f32])).
% 1.60/0.61  fof(f53,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X6,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f49,f31])).
% 1.60/0.61  fof(f49,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X6,X6),k2_tarski(X0,X0)),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5))) = k2_xboole_0(k2_tarski(X6,X6),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.60/0.61    inference(superposition,[],[f36,f32])).
% 1.60/0.61  fof(f36,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_tarski(X3,X3)),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f26,f30,f29,f29])).
% 1.60/0.61  fof(f30,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f25,f17,f27])).
% 1.60/0.61  fof(f25,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f8])).
% 1.60/0.61  fof(f8,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 1.60/0.61  fof(f26,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f2])).
% 1.60/0.61  fof(f2,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 1.60/0.61  fof(f98,plain,(
% 1.60/0.61    ( ! [X30,X28,X33,X31,X29,X32] : (k2_xboole_0(k2_tarski(X33,X28),k2_xboole_0(k2_xboole_0(k2_tarski(X29,X29),k2_tarski(X30,X31)),k2_tarski(X32,X32))) = k2_xboole_0(k2_tarski(X33,X33),k2_xboole_0(k2_tarski(X28,X29),k2_xboole_0(k2_tarski(X30,X30),k2_tarski(X31,X32))))) )),
% 1.60/0.61    inference(superposition,[],[f42,f76])).
% 1.60/0.61  fof(f42,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)))) )),
% 1.60/0.61    inference(superposition,[],[f34,f31])).
% 1.60/0.61  fof(f34,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_xboole_0(k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X5)),k2_tarski(X6,X6)))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f23,f27,f28,f29])).
% 1.60/0.61  fof(f23,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f7])).
% 1.60/0.61  fof(f7,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 1.60/0.61  fof(f97,plain,(
% 1.60/0.61    ( ! [X26,X24,X23,X27,X25,X22] : (k2_xboole_0(k2_xboole_0(k2_tarski(X27,X22),k2_tarski(X23,X23)),k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26))) = k2_xboole_0(k2_tarski(X27,X27),k2_xboole_0(k2_tarski(X22,X23),k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26))))) )),
% 1.60/0.61    inference(superposition,[],[f44,f76])).
% 1.60/0.61  fof(f221,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X5,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4))) = k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4))))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f220,f31])).
% 1.60/0.61  fof(f220,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)))) = k2_xboole_0(k2_xboole_0(k2_tarski(X5,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X4,X4))))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f171,f181])).
% 1.60/0.61  fof(f181,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X0,X1)) = k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X0,X1)))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f58,f169])).
% 1.60/0.61  fof(f169,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k4_enumset1(X2,X3,X0,X0,X0,X1)) )),
% 1.60/0.61    inference(superposition,[],[f148,f31])).
% 1.60/0.61  fof(f148,plain,(
% 1.60/0.61    ( ! [X14,X12,X15,X13,X11] : (k4_enumset1(X11,X12,X13,X14,X14,X15) = k2_xboole_0(k2_tarski(X11,X12),k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f141,f31])).
% 1.60/0.61  fof(f141,plain,(
% 1.60/0.61    ( ! [X14,X12,X15,X13,X11] : (k4_enumset1(X11,X12,X13,X14,X14,X15) = k2_xboole_0(k2_xboole_0(k2_tarski(X11,X11),k2_tarski(X12,X12)),k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X15)))) )),
% 1.60/0.61    inference(superposition,[],[f129,f43])).
% 1.60/0.61  fof(f43,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X1,X1,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X5,X5)))) )),
% 1.60/0.61    inference(superposition,[],[f34,f31])).
% 1.60/0.61  fof(f129,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f44,f126])).
% 1.60/0.61  fof(f58,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X0,X0,X1)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X0,X1))) )),
% 1.60/0.61    inference(superposition,[],[f43,f31])).
% 1.60/0.61  fof(f171,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X5,X0),k2_tarski(X1,X1)),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X3)),k2_tarski(X4,X4))) = k2_xboole_0(k2_tarski(X5,X5),k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4))))) )),
% 1.60/0.61    inference(superposition,[],[f53,f148])).
% 1.60/0.61  fof(f175,plain,(
% 1.60/0.61    ( ! [X30,X35,X33,X31,X34,X32] : (k2_xboole_0(k2_xboole_0(k2_tarski(X35,X35),k2_tarski(X30,X31)),k2_xboole_0(k2_tarski(X32,X33),k2_tarski(X34,X34))) = k2_xboole_0(k2_tarski(X35,X35),k2_xboole_0(k2_tarski(X30,X31),k2_xboole_0(k2_tarski(X32,X33),k2_tarski(X34,X34))))) )),
% 1.60/0.61    inference(superposition,[],[f43,f148])).
% 1.60/0.61  fof(f132,plain,(
% 1.60/0.61    ( ! [X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k2_xboole_0(k2_tarski(X18,X18),k2_tarski(X19,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) = k2_xboole_0(k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f108,f31])).
% 1.60/0.61  fof(f108,plain,(
% 1.60/0.61    ( ! [X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k2_xboole_0(k2_tarski(X18,X18),k2_tarski(X19,X20)),k2_xboole_0(k2_tarski(X21,X22),k2_tarski(X23,X23))) = k2_xboole_0(k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X20)),k2_xboole_0(k2_xboole_0(k2_tarski(X21,X21),k2_tarski(X22,X22)),k2_tarski(X23,X23)))) )),
% 1.60/0.61    inference(superposition,[],[f53,f43])).
% 1.60/0.61  fof(f209,plain,(
% 1.60/0.61    ( ! [X28,X26,X24,X29,X27,X25] : (k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_tarski(X27,X28),k2_tarski(X29,X29)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f208,f92])).
% 1.60/0.61  fof(f208,plain,(
% 1.60/0.61    ( ! [X28,X26,X24,X29,X27,X25] : (k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k4_enumset1(X27,X27,X28,X29,X29,X29))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f207,f148])).
% 1.60/0.61  fof(f207,plain,(
% 1.60/0.61    ( ! [X28,X26,X24,X29,X27,X25] : (k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_tarski(X27,X27),k2_xboole_0(k2_tarski(X28,X29),k2_tarski(X29,X29))))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f191,f181])).
% 1.60/0.61  fof(f191,plain,(
% 1.60/0.61    ( ! [X28,X26,X24,X29,X27,X25] : (k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_xboole_0(k2_tarski(X27,X27),k2_tarski(X28,X29)),k2_tarski(X29,X29))) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_xboole_0(k2_tarski(X25,X26),k2_tarski(X27,X27))),k2_tarski(X28,X29))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f109,f181])).
% 1.60/0.61  fof(f109,plain,(
% 1.60/0.61    ( ! [X28,X26,X24,X29,X27,X25] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X24,X24),k2_tarski(X25,X26)),k2_tarski(X27,X27)),k2_tarski(X28,X29)) = k2_xboole_0(k2_xboole_0(k2_tarski(X24,X25),k2_tarski(X26,X26)),k2_xboole_0(k2_xboole_0(k2_tarski(X27,X27),k2_tarski(X28,X29)),k2_tarski(X29,X29)))) )),
% 1.60/0.61    inference(superposition,[],[f53,f45])).
% 1.60/0.61  fof(f45,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X5,X0,X1,X1)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_tarski(X0,X1))) )),
% 1.60/0.61    inference(superposition,[],[f35,f31])).
% 1.60/0.61  fof(f198,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X0,X1)))) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X5))),k2_tarski(X0,X1))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f180,f181])).
% 1.60/0.61  fof(f180,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_tarski(X0,X1)) = k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X0,X1))))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f160,f169])).
% 1.60/0.61  fof(f160,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_tarski(X0,X1)) = k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k4_enumset1(X4,X5,X0,X0,X0,X1)))) )),
% 1.60/0.61    inference(superposition,[],[f52,f31])).
% 1.60/0.61  fof(f52,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X3),k4_enumset1(X4,X5,X0,X1,X1,X6))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)),k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X6,X6)))) )),
% 1.60/0.61    inference(superposition,[],[f36,f31])).
% 1.60/0.61  fof(f507,plain,(
% 1.60/0.61    ( ! [X14,X17,X15,X13,X16] : (k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))) = k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f488,f181])).
% 1.60/0.61  fof(f488,plain,(
% 1.60/0.61    ( ! [X14,X17,X15,X13,X16] : (k2_xboole_0(k2_xboole_0(k2_tarski(X13,X13),k2_tarski(X14,X15)),k2_tarski(X16,X17)) = k2_xboole_0(k2_tarski(X13,X13),k2_xboole_0(k2_xboole_0(k2_tarski(X13,X13),k2_tarski(X14,X15)),k2_tarski(X16,X17)))) )),
% 1.60/0.61    inference(superposition,[],[f32,f295])).
% 1.60/0.61  fof(f295,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_tarski(X0,X1)) = k4_enumset1(X2,X3,X4,X0,X1,X1)) )),
% 1.60/0.61    inference(superposition,[],[f253,f31])).
% 1.60/0.61  fof(f253,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X2,X3,X4,X5,X0,X1) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X0,X1)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f249,f237])).
% 1.60/0.61  fof(f237,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X1,X1,X5)) = k4_enumset1(X2,X3,X4,X0,X1,X5)) )),
% 1.60/0.61    inference(backward_demodulation,[],[f111,f234])).
% 1.60/0.61  fof(f111,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X0,X1,X1,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X4)),k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X5,X5)))) )),
% 1.60/0.61    inference(superposition,[],[f53,f31])).
% 1.60/0.61  fof(f249,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X2,X2),k4_enumset1(X3,X4,X5,X0,X0,X1)) = k2_xboole_0(k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X5),k2_tarski(X0,X1)))) )),
% 1.60/0.61    inference(superposition,[],[f183,f31])).
% 1.60/0.61  fof(f183,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k2_xboole_0(k2_tarski(X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X6))))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f34,f181])).
% 1.60/0.61  fof(f541,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f540,f92])).
% 1.60/0.61  fof(f540,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X3),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f539,f92])).
% 1.60/0.61  fof(f539,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X3),k4_enumset1(X4,X4,X5,X6,X7,X7))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f516,f528])).
% 1.60/0.61  fof(f528,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X5)))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f515,f92])).
% 1.60/0.61  fof(f515,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X2,X3,X4,X5,X5))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f193,f508])).
% 1.60/0.61  fof(f193,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k2_tarski(X2,X2),k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X5))))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f120,f181])).
% 1.60/0.61  fof(f516,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X3),k2_xboole_0(k2_tarski(X4,X4),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X7))))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f202,f508])).
% 1.60/0.61  fof(f202,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3))),k2_xboole_0(k2_tarski(X4,X4),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X7))))) )),
% 1.60/0.61    inference(forward_demodulation,[],[f185,f181])).
% 1.60/0.61  fof(f185,plain,(
% 1.60/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X3))),k2_xboole_0(k2_xboole_0(k2_tarski(X4,X4),k2_tarski(X5,X6)),k2_tarski(X7,X7)))) )),
% 1.60/0.61    inference(backward_demodulation,[],[f36,f181])).
% 1.60/0.61  fof(f40,plain,(
% 1.60/0.61    k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))) | spl7_1),
% 1.60/0.61    inference(avatar_component_clause,[],[f38])).
% 1.60/0.61  fof(f38,plain,(
% 1.60/0.61    spl7_1 <=> k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) = k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.60/0.61  fof(f41,plain,(
% 1.60/0.61    ~spl7_1),
% 1.60/0.61    inference(avatar_split_clause,[],[f33,f38])).
% 1.60/0.61  fof(f33,plain,(
% 1.60/0.61    k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)))),
% 1.60/0.61    inference(definition_unfolding,[],[f16,f27,f30])).
% 1.60/0.61  fof(f16,plain,(
% 1.60/0.61    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 1.60/0.61    inference(cnf_transformation,[],[f15])).
% 1.60/0.61  fof(f15,plain,(
% 1.60/0.61    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 1.60/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f14])).
% 1.60/0.61  fof(f14,plain,(
% 1.60/0.61    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 1.60/0.61    introduced(choice_axiom,[])).
% 1.60/0.61  fof(f13,plain,(
% 1.60/0.61    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.60/0.61    inference(ennf_transformation,[],[f12])).
% 1.60/0.61  fof(f12,negated_conjecture,(
% 1.60/0.61    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.60/0.61    inference(negated_conjecture,[],[f11])).
% 1.60/0.61  fof(f11,conjecture,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.60/0.61  % SZS output end Proof for theBenchmark
% 1.60/0.61  % (21019)------------------------------
% 1.60/0.61  % (21019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.61  % (21019)Termination reason: Refutation
% 1.60/0.61  
% 1.60/0.61  % (21019)Memory used [KB]: 11513
% 1.60/0.61  % (21019)Time elapsed: 0.163 s
% 1.60/0.61  % (21019)------------------------------
% 1.60/0.61  % (21019)------------------------------
% 1.60/0.61  % (21002)Success in time 0.25 s
%------------------------------------------------------------------------------
