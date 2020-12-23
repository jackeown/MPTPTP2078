%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:09 EST 2020

% Result     : Theorem 51.32s
% Output     : Refutation 51.32s
% Verified   : 
% Statistics : Number of formulae       :  134 (2005 expanded)
%              Number of leaves         :   21 ( 664 expanded)
%              Depth                    :   28
%              Number of atoms          :  169 (2064 expanded)
%              Number of equality atoms :  168 (2063 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29433,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19564,f29421])).

fof(f29421,plain,(
    ! [X35,X33,X34] : k5_xboole_0(k2_zfmisc_1(X35,X34),k2_zfmisc_1(k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35)),X34)) = k2_zfmisc_1(k5_xboole_0(X35,k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35))),X34) ),
    inference(backward_demodulation,[],[f1006,f29420])).

fof(f29420,plain,(
    ! [X41,X42,X40] : k2_zfmisc_1(X41,X42) = k5_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(k5_xboole_0(X40,X41),X42)) ),
    inference(forward_demodulation,[],[f29381,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f29381,plain,(
    ! [X41,X42,X40] : k5_xboole_0(k2_zfmisc_1(X41,X42),k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(k5_xboole_0(X40,X41),X42)) ),
    inference(superposition,[],[f413,f1039])).

fof(f1039,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1038,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1038,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k1_xboole_0,X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1037,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1037,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1036,f108])).

fof(f108,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f94,f72])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f71,f63])).

fof(f63,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f62,f30])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1036,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1035,f423])).

fof(f423,plain,(
    ! [X24,X23,X25,X22] : k5_xboole_0(X24,k5_xboole_0(X23,k5_xboole_0(X22,X25))) = k5_xboole_0(X24,k5_xboole_0(X22,k5_xboole_0(X23,X25))) ),
    inference(forward_demodulation,[],[f422,f44])).

fof(f422,plain,(
    ! [X24,X23,X25,X22] : k5_xboole_0(X24,k5_xboole_0(k5_xboole_0(X22,X23),X25)) = k5_xboole_0(X24,k5_xboole_0(X23,k5_xboole_0(X22,X25))) ),
    inference(forward_demodulation,[],[f389,f421])).

fof(f421,plain,(
    ! [X21,X19,X20,X18] : k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X18,X20)),X21) = k5_xboole_0(X20,k5_xboole_0(X18,k5_xboole_0(X19,X21))) ),
    inference(forward_demodulation,[],[f388,f44])).

fof(f388,plain,(
    ! [X21,X19,X20,X18] : k5_xboole_0(X20,k5_xboole_0(k5_xboole_0(X18,X19),X21)) = k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X18,X20)),X21) ),
    inference(superposition,[],[f96,f96])).

fof(f96,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f44,f34])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f389,plain,(
    ! [X24,X23,X25,X22] : k5_xboole_0(X24,k5_xboole_0(k5_xboole_0(X22,X23),X25)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X23,X24)),X25) ),
    inference(superposition,[],[f96,f44])).

fof(f1035,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1034,f221])).

fof(f221,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f217,f44])).

fof(f217,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f44,f116])).

fof(f116,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f108,f34])).

fof(f1034,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1033,f423])).

fof(f1033,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1032,f34])).

fof(f1032,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1031,f44])).

fof(f1031,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6))) ),
    inference(forward_demodulation,[],[f1030,f213])).

fof(f213,plain,(
    ! [X19,X17,X18] : k5_xboole_0(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X18)) = k5_xboole_0(k2_zfmisc_1(k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X19)),X18),k2_zfmisc_1(k5_xboole_0(X17,k5_xboole_0(X19,k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X19)))),X18)) ),
    inference(superposition,[],[f116,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) ),
    inference(backward_demodulation,[],[f79,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f47,f58,f58])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X2) ),
    inference(forward_demodulation,[],[f66,f44])).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ),
    inference(definition_unfolding,[],[f45,f59,f59])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f1030,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),X6),k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6))) ),
    inference(forward_demodulation,[],[f992,f34])).

fof(f992,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6),k2_zfmisc_1(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),X6))) ),
    inference(superposition,[],[f176,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) ),
    inference(backward_demodulation,[],[f64,f44])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f39,f58,f58,f59])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f176,plain,(
    ! [X4,X5,X3] : k5_xboole_0(k2_zfmisc_1(X3,X4),k5_xboole_0(k2_zfmisc_1(X5,X4),k2_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5)),X4))) = k2_zfmisc_1(k5_xboole_0(X3,k5_xboole_0(X5,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5)))),X4) ),
    inference(superposition,[],[f82,f44])).

fof(f413,plain,(
    ! [X30,X31,X29] : k5_xboole_0(X29,X30) = k5_xboole_0(X31,k5_xboole_0(X30,k5_xboole_0(X29,X31))) ),
    inference(superposition,[],[f116,f96])).

fof(f1006,plain,(
    ! [X35,X33,X34] : k5_xboole_0(k2_zfmisc_1(X35,X34),k2_zfmisc_1(k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35)),X34)) = k5_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(k5_xboole_0(X33,k5_xboole_0(X35,k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35)))),X34)) ),
    inference(superposition,[],[f108,f176])).

fof(f19564,plain,(
    k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(subsumption_resolution,[],[f112,f19544])).

fof(f19544,plain,(
    ! [X35,X33,X34] : k5_xboole_0(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X33,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)))) = k2_zfmisc_1(X33,k5_xboole_0(X35,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)))) ),
    inference(backward_demodulation,[],[f718,f19543])).

fof(f19543,plain,(
    ! [X41,X42,X40] : k2_zfmisc_1(X40,X42) = k5_xboole_0(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k5_xboole_0(X41,X42))) ),
    inference(forward_demodulation,[],[f19417,f31])).

fof(f19417,plain,(
    ! [X41,X42,X40] : k5_xboole_0(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k5_xboole_0(X41,X42))) = k5_xboole_0(k2_zfmisc_1(X40,X42),k1_xboole_0) ),
    inference(superposition,[],[f413,f750])).

fof(f750,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f749,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f749,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f748,f30])).

fof(f748,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f747,f108])).

fof(f747,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f746,f423])).

fof(f746,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f745,f221])).

fof(f745,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f744,f423])).

fof(f744,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f743,f34])).

fof(f743,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f742,f44])).

fof(f742,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5))) ),
    inference(forward_demodulation,[],[f741,f212])).

fof(f212,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16)) = k5_xboole_0(k2_zfmisc_1(X14,k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16))),k2_zfmisc_1(X14,k5_xboole_0(X15,k5_xboole_0(X16,k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)))))) ),
    inference(superposition,[],[f116,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(backward_demodulation,[],[f78,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f58,f58])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(forward_demodulation,[],[f65,f44])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ),
    inference(definition_unfolding,[],[f46,f59,f59])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f741,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))),k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))))) ),
    inference(forward_demodulation,[],[f704,f34])).

fof(f704,plain,(
    ! [X6,X4,X5] : k2_zfmisc_1(X6,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),k2_zfmisc_1(X6,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) ),
    inference(superposition,[],[f139,f74])).

fof(f139,plain,(
    ! [X4,X5,X3] : k5_xboole_0(k2_zfmisc_1(X3,X4),k5_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k2_zfmisc_1(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) ),
    inference(superposition,[],[f81,f44])).

fof(f718,plain,(
    ! [X35,X33,X34] : k5_xboole_0(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X33,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)))) = k5_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X33,k5_xboole_0(X34,k5_xboole_0(X35,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)))))) ),
    inference(superposition,[],[f108,f139])).

fof(f112,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f111,f108])).

fof(f111,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2))
    | k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f110,f108])).

fof(f110,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)))) ),
    inference(forward_demodulation,[],[f109,f108])).

fof(f109,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)))) ),
    inference(backward_demodulation,[],[f83,f108])).

fof(f83,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2))))
    | k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f80,f68])).

fof(f80,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) ),
    inference(backward_demodulation,[],[f77,f67])).

fof(f77,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
    | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(forward_demodulation,[],[f76,f44])).

fof(f76,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))))
    | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(forward_demodulation,[],[f75,f44])).

fof(f75,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) ),
    inference(forward_demodulation,[],[f73,f44])).

fof(f73,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))))
    | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) ),
    inference(backward_demodulation,[],[f61,f44])).

fof(f61,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))
    | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))) ),
    inference(definition_unfolding,[],[f29,f60,f60,f60,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
   => ( k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
      | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (28743)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (28732)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (28743)Refutation not found, incomplete strategy% (28743)------------------------------
% 0.20/0.51  % (28743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28741)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (28743)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28743)Memory used [KB]: 6140
% 0.20/0.51  % (28743)Time elapsed: 0.004 s
% 0.20/0.51  % (28743)------------------------------
% 0.20/0.51  % (28743)------------------------------
% 0.20/0.52  % (28734)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (28745)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (28751)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (28751)Refutation not found, incomplete strategy% (28751)------------------------------
% 0.20/0.52  % (28751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28736)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (28751)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28751)Memory used [KB]: 1663
% 0.20/0.52  % (28751)Time elapsed: 0.111 s
% 0.20/0.52  % (28751)------------------------------
% 0.20/0.52  % (28751)------------------------------
% 0.20/0.52  % (28754)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (28729)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (28754)Refutation not found, incomplete strategy% (28754)------------------------------
% 0.20/0.52  % (28754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28754)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28754)Memory used [KB]: 10746
% 0.20/0.52  % (28754)Time elapsed: 0.128 s
% 0.20/0.52  % (28754)------------------------------
% 0.20/0.52  % (28754)------------------------------
% 0.20/0.53  % (28730)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (28742)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (28730)Refutation not found, incomplete strategy% (28730)------------------------------
% 0.20/0.53  % (28730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28730)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28730)Memory used [KB]: 10746
% 0.20/0.53  % (28730)Time elapsed: 0.123 s
% 0.20/0.53  % (28730)------------------------------
% 0.20/0.53  % (28730)------------------------------
% 0.20/0.53  % (28732)Refutation not found, incomplete strategy% (28732)------------------------------
% 0.20/0.53  % (28732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28732)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28732)Memory used [KB]: 6268
% 0.20/0.53  % (28732)Time elapsed: 0.126 s
% 0.20/0.53  % (28732)------------------------------
% 0.20/0.53  % (28732)------------------------------
% 0.20/0.53  % (28733)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (28753)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (28756)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (28731)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (28753)Refutation not found, incomplete strategy% (28753)------------------------------
% 0.20/0.53  % (28753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28753)Memory used [KB]: 6268
% 0.20/0.53  % (28753)Time elapsed: 0.124 s
% 0.20/0.53  % (28753)------------------------------
% 0.20/0.53  % (28753)------------------------------
% 0.20/0.53  % (28750)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (28745)Refutation not found, incomplete strategy% (28745)------------------------------
% 0.20/0.53  % (28745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28745)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28745)Memory used [KB]: 10618
% 0.20/0.53  % (28745)Time elapsed: 0.134 s
% 0.20/0.53  % (28745)------------------------------
% 0.20/0.53  % (28745)------------------------------
% 0.20/0.53  % (28746)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (28750)Refutation not found, incomplete strategy% (28750)------------------------------
% 0.20/0.54  % (28750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28750)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28750)Memory used [KB]: 10746
% 0.20/0.54  % (28750)Time elapsed: 0.097 s
% 0.20/0.54  % (28750)------------------------------
% 0.20/0.54  % (28750)------------------------------
% 0.20/0.54  % (28748)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.54  % (28748)Refutation not found, incomplete strategy% (28748)------------------------------
% 1.44/0.54  % (28748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (28748)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (28748)Memory used [KB]: 10746
% 1.44/0.54  % (28748)Time elapsed: 0.139 s
% 1.44/0.54  % (28748)------------------------------
% 1.44/0.54  % (28748)------------------------------
% 1.44/0.54  % (28757)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.54  % (28747)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.54  % (28728)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.54  % (28739)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.54  % (28728)Refutation not found, incomplete strategy% (28728)------------------------------
% 1.44/0.54  % (28728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (28728)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (28728)Memory used [KB]: 1663
% 1.44/0.54  % (28728)Time elapsed: 0.133 s
% 1.44/0.54  % (28728)------------------------------
% 1.44/0.54  % (28728)------------------------------
% 1.44/0.54  % (28737)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.54  % (28736)Refutation not found, incomplete strategy% (28736)------------------------------
% 1.44/0.54  % (28736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (28736)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (28736)Memory used [KB]: 10746
% 1.44/0.54  % (28736)Time elapsed: 0.135 s
% 1.44/0.54  % (28736)------------------------------
% 1.44/0.54  % (28736)------------------------------
% 1.44/0.54  % (28737)Refutation not found, incomplete strategy% (28737)------------------------------
% 1.44/0.54  % (28737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (28737)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (28737)Memory used [KB]: 10618
% 1.44/0.54  % (28737)Time elapsed: 0.138 s
% 1.44/0.54  % (28737)------------------------------
% 1.44/0.54  % (28737)------------------------------
% 1.44/0.54  % (28752)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.54  % (28749)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (28749)Refutation not found, incomplete strategy% (28749)------------------------------
% 1.44/0.55  % (28749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (28749)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (28749)Memory used [KB]: 1791
% 1.44/0.55  % (28749)Time elapsed: 0.148 s
% 1.44/0.55  % (28749)------------------------------
% 1.44/0.55  % (28749)------------------------------
% 1.44/0.55  % (28738)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.55  % (28738)Refutation not found, incomplete strategy% (28738)------------------------------
% 1.44/0.55  % (28738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (28738)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (28738)Memory used [KB]: 10618
% 1.44/0.55  % (28738)Time elapsed: 0.147 s
% 1.44/0.55  % (28738)------------------------------
% 1.44/0.55  % (28738)------------------------------
% 1.44/0.55  % (28740)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.55  % (28755)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (28735)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.56  % (28744)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.95/0.63  % (28758)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.95/0.63  % (28758)Refutation not found, incomplete strategy% (28758)------------------------------
% 1.95/0.63  % (28758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.63  % (28758)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.63  
% 1.95/0.63  % (28758)Memory used [KB]: 6140
% 1.95/0.63  % (28758)Time elapsed: 0.090 s
% 1.95/0.63  % (28758)------------------------------
% 1.95/0.63  % (28758)------------------------------
% 1.95/0.64  % (28760)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.95/0.64  % (28759)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.95/0.66  % (28762)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.18/0.67  % (28763)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.18/0.67  % (28761)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.18/0.68  % (28768)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.18/0.68  % (28767)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.18/0.68  % (28768)Refutation not found, incomplete strategy% (28768)------------------------------
% 2.18/0.68  % (28768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.68  % (28768)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.68  
% 2.18/0.68  % (28768)Memory used [KB]: 6268
% 2.18/0.68  % (28768)Time elapsed: 0.112 s
% 2.18/0.68  % (28768)------------------------------
% 2.18/0.68  % (28768)------------------------------
% 2.18/0.68  % (28770)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.18/0.68  % (28765)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.18/0.68  % (28771)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.18/0.69  % (28771)Refutation not found, incomplete strategy% (28771)------------------------------
% 2.18/0.69  % (28771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (28771)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (28771)Memory used [KB]: 1663
% 2.18/0.69  % (28771)Time elapsed: 0.118 s
% 2.18/0.69  % (28771)------------------------------
% 2.18/0.69  % (28771)------------------------------
% 2.18/0.69  % (28769)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.18/0.69  % (28769)Refutation not found, incomplete strategy% (28769)------------------------------
% 2.18/0.69  % (28769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (28769)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (28769)Memory used [KB]: 1791
% 2.18/0.69  % (28769)Time elapsed: 0.121 s
% 2.18/0.69  % (28769)------------------------------
% 2.18/0.69  % (28769)------------------------------
% 2.18/0.69  % (28766)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.18/0.69  % (28766)Refutation not found, incomplete strategy% (28766)------------------------------
% 2.18/0.69  % (28766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (28766)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (28766)Memory used [KB]: 1663
% 2.18/0.69  % (28766)Time elapsed: 0.122 s
% 2.18/0.69  % (28766)------------------------------
% 2.18/0.69  % (28766)------------------------------
% 2.18/0.69  % (28764)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.79/0.77  % (28772)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.79/0.80  % (28773)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 2.79/0.81  % (28733)Time limit reached!
% 2.79/0.81  % (28733)------------------------------
% 2.79/0.81  % (28733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.79/0.81  % (28733)Termination reason: Time limit
% 2.79/0.81  
% 2.79/0.81  % (28733)Memory used [KB]: 10106
% 2.79/0.81  % (28733)Time elapsed: 0.404 s
% 2.79/0.81  % (28733)------------------------------
% 2.79/0.81  % (28733)------------------------------
% 3.05/0.83  % (28775)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.05/0.83  % (28775)Refutation not found, incomplete strategy% (28775)------------------------------
% 3.05/0.83  % (28775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.83  % (28775)Termination reason: Refutation not found, incomplete strategy
% 3.05/0.83  
% 3.05/0.83  % (28775)Memory used [KB]: 6140
% 3.05/0.83  % (28775)Time elapsed: 0.118 s
% 3.05/0.83  % (28775)------------------------------
% 3.05/0.83  % (28775)------------------------------
% 3.05/0.83  % (28773)Refutation not found, incomplete strategy% (28773)------------------------------
% 3.05/0.83  % (28773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.83  % (28773)Termination reason: Refutation not found, incomplete strategy
% 3.05/0.83  
% 3.05/0.83  % (28773)Memory used [KB]: 6268
% 3.05/0.83  % (28773)Time elapsed: 0.118 s
% 3.05/0.83  % (28773)------------------------------
% 3.05/0.83  % (28773)------------------------------
% 3.05/0.83  % (28776)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.05/0.84  % (28774)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.54/0.93  % (28740)Time limit reached!
% 3.54/0.93  % (28740)------------------------------
% 3.54/0.93  % (28740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.54/0.93  % (28740)Termination reason: Time limit
% 3.54/0.93  % (28740)Termination phase: Saturation
% 3.54/0.93  
% 3.54/0.93  % (28740)Memory used [KB]: 10874
% 3.54/0.93  % (28740)Time elapsed: 0.530 s
% 3.54/0.93  % (28740)------------------------------
% 3.54/0.93  % (28740)------------------------------
% 3.54/0.93  % (28729)Time limit reached!
% 3.54/0.93  % (28729)------------------------------
% 3.54/0.93  % (28729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.54/0.93  % (28729)Termination reason: Time limit
% 3.54/0.93  
% 3.54/0.93  % (28729)Memory used [KB]: 9594
% 3.54/0.93  % (28729)Time elapsed: 0.526 s
% 3.54/0.93  % (28729)------------------------------
% 3.54/0.93  % (28729)------------------------------
% 3.54/0.94  % (28777)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 3.54/0.96  % (28761)Time limit reached!
% 3.54/0.96  % (28761)------------------------------
% 3.54/0.96  % (28761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.54/0.96  % (28761)Termination reason: Time limit
% 3.54/0.96  
% 3.54/0.96  % (28761)Memory used [KB]: 7675
% 3.54/0.96  % (28761)Time elapsed: 0.402 s
% 3.54/0.96  % (28761)------------------------------
% 3.54/0.96  % (28761)------------------------------
% 3.54/0.96  % (28779)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 3.75/0.97  % (28778)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 3.75/0.99  % (28762)Time limit reached!
% 3.75/0.99  % (28762)------------------------------
% 3.75/0.99  % (28762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.99  % (28762)Termination reason: Time limit
% 3.75/0.99  
% 3.75/0.99  % (28762)Memory used [KB]: 14456
% 3.75/0.99  % (28762)Time elapsed: 0.428 s
% 3.75/0.99  % (28762)------------------------------
% 3.75/0.99  % (28762)------------------------------
% 3.75/1.00  % (28744)Time limit reached!
% 3.75/1.00  % (28744)------------------------------
% 3.75/1.00  % (28744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/1.00  % (28744)Termination reason: Time limit
% 3.75/1.00  % (28744)Termination phase: Saturation
% 3.75/1.00  
% 3.75/1.00  % (28744)Memory used [KB]: 15735
% 3.75/1.00  % (28744)Time elapsed: 0.600 s
% 3.75/1.00  % (28744)------------------------------
% 3.75/1.00  % (28744)------------------------------
% 3.75/1.01  % (28756)Time limit reached!
% 3.75/1.01  % (28756)------------------------------
% 3.75/1.01  % (28756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/1.01  % (28756)Termination reason: Time limit
% 3.75/1.01  
% 3.75/1.01  % (28756)Memory used [KB]: 9722
% 3.75/1.01  % (28756)Time elapsed: 0.611 s
% 3.75/1.01  % (28756)------------------------------
% 3.75/1.01  % (28756)------------------------------
% 4.26/1.06  % (28735)Time limit reached!
% 4.26/1.06  % (28735)------------------------------
% 4.26/1.06  % (28735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/1.06  % (28735)Termination reason: Time limit
% 4.26/1.06  
% 4.26/1.06  % (28735)Memory used [KB]: 12025
% 4.26/1.06  % (28735)Time elapsed: 0.629 s
% 4.26/1.06  % (28735)------------------------------
% 4.26/1.06  % (28735)------------------------------
% 4.26/1.06  % (28781)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 4.26/1.07  % (28780)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.64/1.09  % (28770)Time limit reached!
% 5.64/1.09  % (28770)------------------------------
% 5.64/1.09  % (28770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.64/1.09  % (28770)Termination reason: Time limit
% 5.64/1.09  % (28770)Termination phase: Saturation
% 5.64/1.09  
% 5.64/1.09  % (28770)Memory used [KB]: 5628
% 5.64/1.09  % (28770)Time elapsed: 0.500 s
% 5.64/1.09  % (28770)------------------------------
% 5.64/1.09  % (28770)------------------------------
% 5.64/1.10  % (28782)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.64/1.12  % (28774)Time limit reached!
% 5.64/1.12  % (28774)------------------------------
% 5.64/1.12  % (28774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.64/1.12  % (28774)Termination reason: Time limit
% 5.64/1.12  
% 5.64/1.12  % (28774)Memory used [KB]: 4221
% 5.64/1.12  % (28774)Time elapsed: 0.411 s
% 5.64/1.12  % (28774)------------------------------
% 5.64/1.12  % (28774)------------------------------
% 5.64/1.12  % (28784)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.64/1.12  % (28784)Refutation not found, incomplete strategy% (28784)------------------------------
% 5.64/1.12  % (28784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.64/1.12  % (28784)Termination reason: Refutation not found, incomplete strategy
% 5.64/1.12  
% 5.64/1.12  % (28784)Memory used [KB]: 6140
% 5.64/1.12  % (28784)Time elapsed: 0.086 s
% 5.64/1.12  % (28784)------------------------------
% 5.64/1.12  % (28784)------------------------------
% 5.64/1.14  % (28783)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 6.15/1.14  % (28783)Refutation not found, incomplete strategy% (28783)------------------------------
% 6.15/1.14  % (28783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.15/1.14  % (28783)Termination reason: Refutation not found, incomplete strategy
% 6.15/1.14  
% 6.15/1.14  % (28783)Memory used [KB]: 6140
% 6.15/1.14  % (28783)Time elapsed: 0.109 s
% 6.15/1.14  % (28783)------------------------------
% 6.15/1.14  % (28783)------------------------------
% 6.15/1.16  % (28785)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 6.15/1.16  % (28785)Refutation not found, incomplete strategy% (28785)------------------------------
% 6.15/1.16  % (28785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.15/1.16  % (28785)Termination reason: Refutation not found, incomplete strategy
% 6.15/1.16  
% 6.15/1.16  % (28785)Memory used [KB]: 10746
% 6.15/1.16  % (28785)Time elapsed: 0.081 s
% 6.15/1.16  % (28785)------------------------------
% 6.15/1.16  % (28785)------------------------------
% 6.83/1.24  % (28777)Time limit reached!
% 6.83/1.24  % (28777)------------------------------
% 6.83/1.24  % (28777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.83/1.24  % (28777)Termination reason: Time limit
% 6.83/1.24  % (28777)Termination phase: Saturation
% 6.83/1.24  
% 6.83/1.24  % (28777)Memory used [KB]: 5500
% 6.83/1.24  % (28777)Time elapsed: 0.400 s
% 6.83/1.24  % (28777)------------------------------
% 6.83/1.24  % (28777)------------------------------
% 8.72/1.47  % (28782)Time limit reached!
% 8.72/1.47  % (28782)------------------------------
% 8.72/1.47  % (28782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.72/1.47  % (28782)Termination reason: Time limit
% 8.72/1.47  
% 8.72/1.47  % (28782)Memory used [KB]: 11385
% 8.72/1.47  % (28782)Time elapsed: 0.430 s
% 8.72/1.47  % (28782)------------------------------
% 8.72/1.47  % (28782)------------------------------
% 10.47/1.74  % (28752)Time limit reached!
% 10.47/1.74  % (28752)------------------------------
% 10.47/1.74  % (28752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.47/1.74  % (28752)Termination reason: Time limit
% 10.47/1.74  
% 10.47/1.74  % (28752)Memory used [KB]: 24178
% 10.47/1.74  % (28752)Time elapsed: 1.317 s
% 10.47/1.74  % (28752)------------------------------
% 10.47/1.74  % (28752)------------------------------
% 11.18/1.78  % (28764)Time limit reached!
% 11.18/1.78  % (28764)------------------------------
% 11.18/1.78  % (28764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.18/1.78  % (28764)Termination reason: Time limit
% 11.18/1.78  % (28764)Termination phase: Saturation
% 11.18/1.78  
% 11.18/1.78  % (28764)Memory used [KB]: 19189
% 11.18/1.78  % (28764)Time elapsed: 1.200 s
% 11.18/1.78  % (28764)------------------------------
% 11.18/1.78  % (28764)------------------------------
% 11.87/1.91  % (28755)Time limit reached!
% 11.87/1.91  % (28755)------------------------------
% 11.87/1.91  % (28755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.87/1.91  % (28755)Termination reason: Time limit
% 11.87/1.91  % (28755)Termination phase: Saturation
% 11.87/1.91  
% 11.87/1.91  % (28755)Memory used [KB]: 25202
% 11.87/1.91  % (28755)Time elapsed: 1.500 s
% 11.87/1.91  % (28755)------------------------------
% 11.87/1.91  % (28755)------------------------------
% 12.90/2.01  % (28776)Time limit reached!
% 12.90/2.01  % (28776)------------------------------
% 12.90/2.01  % (28776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.90/2.01  % (28776)Termination reason: Time limit
% 12.90/2.01  % (28776)Termination phase: Saturation
% 12.90/2.01  
% 12.90/2.01  % (28776)Memory used [KB]: 25202
% 12.90/2.01  % (28776)Time elapsed: 1.300 s
% 12.90/2.01  % (28776)------------------------------
% 12.90/2.01  % (28776)------------------------------
% 12.90/2.04  % (28739)Time limit reached!
% 12.90/2.04  % (28739)------------------------------
% 12.90/2.04  % (28739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.90/2.04  % (28739)Termination reason: Time limit
% 12.90/2.04  
% 12.90/2.04  % (28739)Memory used [KB]: 25074
% 12.90/2.04  % (28739)Time elapsed: 1.645 s
% 12.90/2.04  % (28739)------------------------------
% 12.90/2.04  % (28739)------------------------------
% 15.04/2.27  % (28760)Time limit reached!
% 15.04/2.27  % (28760)------------------------------
% 15.04/2.27  % (28760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.04/2.27  % (28760)Termination reason: Time limit
% 15.04/2.27  % (28760)Termination phase: Saturation
% 15.04/2.27  
% 15.04/2.27  % (28760)Memory used [KB]: 37355
% 15.04/2.27  % (28760)Time elapsed: 1.700 s
% 15.04/2.27  % (28760)------------------------------
% 15.04/2.27  % (28760)------------------------------
% 15.41/2.32  % (28742)Time limit reached!
% 15.41/2.32  % (28742)------------------------------
% 15.41/2.32  % (28742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.41/2.32  % (28742)Termination reason: Time limit
% 15.41/2.32  % (28742)Termination phase: Saturation
% 15.41/2.32  
% 15.41/2.32  % (28742)Memory used [KB]: 32110
% 15.41/2.32  % (28742)Time elapsed: 1.800 s
% 15.41/2.32  % (28742)------------------------------
% 15.41/2.32  % (28742)------------------------------
% 16.71/2.45  % (28746)Time limit reached!
% 16.71/2.45  % (28746)------------------------------
% 16.71/2.45  % (28746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.71/2.45  % (28746)Termination reason: Time limit
% 16.71/2.45  
% 16.71/2.45  % (28746)Memory used [KB]: 40553
% 16.71/2.45  % (28746)Time elapsed: 2.050 s
% 16.71/2.45  % (28746)------------------------------
% 16.71/2.45  % (28746)------------------------------
% 16.71/2.46  % (28734)Time limit reached!
% 16.71/2.46  % (28734)------------------------------
% 16.71/2.46  % (28734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.71/2.46  % (28734)Termination reason: Time limit
% 16.71/2.46  % (28734)Termination phase: Saturation
% 16.71/2.46  
% 16.71/2.46  % (28734)Memory used [KB]: 39274
% 16.71/2.46  % (28734)Time elapsed: 2.0000 s
% 16.71/2.46  % (28734)------------------------------
% 16.71/2.46  % (28734)------------------------------
% 21.16/3.04  % (28747)Time limit reached!
% 21.16/3.04  % (28747)------------------------------
% 21.16/3.04  % (28747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.16/3.04  % (28747)Termination reason: Time limit
% 21.16/3.04  
% 21.16/3.04  % (28747)Memory used [KB]: 54370
% 21.16/3.04  % (28747)Time elapsed: 2.636 s
% 21.16/3.04  % (28747)------------------------------
% 21.16/3.04  % (28747)------------------------------
% 24.14/3.40  % (28741)Time limit reached!
% 24.14/3.40  % (28741)------------------------------
% 24.14/3.40  % (28741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.14/3.42  % (28741)Termination reason: Time limit
% 24.14/3.42  % (28741)Termination phase: Saturation
% 24.14/3.42  
% 24.14/3.42  % (28741)Memory used [KB]: 15735
% 24.14/3.42  % (28741)Time elapsed: 3.0000 s
% 24.14/3.42  % (28741)------------------------------
% 24.14/3.42  % (28741)------------------------------
% 24.14/3.44  % (28759)Time limit reached!
% 24.14/3.44  % (28759)------------------------------
% 24.14/3.44  % (28759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.14/3.44  % (28759)Termination reason: Time limit
% 24.14/3.44  % (28759)Termination phase: Saturation
% 24.14/3.44  
% 24.14/3.44  % (28759)Memory used [KB]: 51811
% 24.14/3.44  % (28759)Time elapsed: 2.800 s
% 24.14/3.44  % (28759)------------------------------
% 24.14/3.44  % (28759)------------------------------
% 30.27/4.17  % (28772)Time limit reached!
% 30.27/4.17  % (28772)------------------------------
% 30.27/4.17  % (28772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.27/4.17  % (28772)Termination reason: Time limit
% 30.27/4.17  % (28772)Termination phase: Saturation
% 30.27/4.17  
% 30.27/4.17  % (28772)Memory used [KB]: 93516
% 30.27/4.17  % (28772)Time elapsed: 3.500 s
% 30.27/4.17  % (28772)------------------------------
% 30.27/4.17  % (28772)------------------------------
% 31.30/4.32  % (28757)Time limit reached!
% 31.30/4.32  % (28757)------------------------------
% 31.30/4.32  % (28757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.30/4.32  % (28757)Termination reason: Time limit
% 31.30/4.32  % (28757)Termination phase: Saturation
% 31.30/4.32  
% 31.30/4.32  % (28757)Memory used [KB]: 80595
% 31.30/4.32  % (28757)Time elapsed: 3.900 s
% 31.30/4.32  % (28757)------------------------------
% 31.30/4.32  % (28757)------------------------------
% 41.78/5.62  % (28731)Time limit reached!
% 41.78/5.62  % (28731)------------------------------
% 41.78/5.62  % (28731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.78/5.62  % (28731)Termination reason: Time limit
% 41.78/5.62  % (28731)Termination phase: Saturation
% 41.78/5.62  
% 41.78/5.62  % (28731)Memory used [KB]: 153259
% 41.78/5.62  % (28731)Time elapsed: 5.200 s
% 41.78/5.62  % (28731)------------------------------
% 41.78/5.62  % (28731)------------------------------
% 45.10/6.07  % (28765)Time limit reached!
% 45.10/6.07  % (28765)------------------------------
% 45.10/6.07  % (28765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 45.10/6.07  % (28765)Termination reason: Time limit
% 45.10/6.07  % (28765)Termination phase: Saturation
% 45.10/6.07  
% 45.10/6.07  % (28765)Memory used [KB]: 161575
% 45.10/6.07  % (28765)Time elapsed: 5.500 s
% 45.10/6.07  % (28765)------------------------------
% 45.10/6.07  % (28765)------------------------------
% 49.34/6.77  % (28778)Time limit reached!
% 49.34/6.77  % (28778)------------------------------
% 49.34/6.77  % (28778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 49.34/6.77  % (28778)Termination reason: Time limit
% 49.34/6.77  % (28778)Termination phase: Saturation
% 49.34/6.77  
% 49.34/6.77  % (28778)Memory used [KB]: 246776
% 49.34/6.77  % (28778)Time elapsed: 5.900 s
% 49.34/6.77  % (28778)------------------------------
% 49.34/6.77  % (28778)------------------------------
% 51.32/7.23  % (28779)Refutation found. Thanks to Tanya!
% 51.32/7.23  % SZS status Theorem for theBenchmark
% 51.32/7.23  % SZS output start Proof for theBenchmark
% 51.32/7.23  fof(f29433,plain,(
% 51.32/7.23    $false),
% 51.32/7.23    inference(subsumption_resolution,[],[f19564,f29421])).
% 51.32/7.23  fof(f29421,plain,(
% 51.32/7.23    ( ! [X35,X33,X34] : (k5_xboole_0(k2_zfmisc_1(X35,X34),k2_zfmisc_1(k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35)),X34)) = k2_zfmisc_1(k5_xboole_0(X35,k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35))),X34)) )),
% 51.32/7.23    inference(backward_demodulation,[],[f1006,f29420])).
% 51.32/7.23  fof(f29420,plain,(
% 51.32/7.23    ( ! [X41,X42,X40] : (k2_zfmisc_1(X41,X42) = k5_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(k5_xboole_0(X40,X41),X42))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f29381,f31])).
% 51.32/7.23  fof(f31,plain,(
% 51.32/7.23    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.32/7.23    inference(cnf_transformation,[],[f5])).
% 51.32/7.23  fof(f5,axiom,(
% 51.32/7.23    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 51.32/7.23  fof(f29381,plain,(
% 51.32/7.23    ( ! [X41,X42,X40] : (k5_xboole_0(k2_zfmisc_1(X41,X42),k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(X40,X42),k2_zfmisc_1(k5_xboole_0(X40,X41),X42))) )),
% 51.32/7.23    inference(superposition,[],[f413,f1039])).
% 51.32/7.23  fof(f1039,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1038,f70])).
% 51.32/7.23  fof(f70,plain,(
% 51.32/7.23    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 51.32/7.23    inference(equality_resolution,[],[f41])).
% 51.32/7.23  fof(f41,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 51.32/7.23    inference(cnf_transformation,[],[f28])).
% 51.32/7.23  fof(f28,plain,(
% 51.32/7.23    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 51.32/7.23    inference(flattening,[],[f27])).
% 51.32/7.23  fof(f27,plain,(
% 51.32/7.23    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 51.32/7.23    inference(nnf_transformation,[],[f17])).
% 51.32/7.23  fof(f17,axiom,(
% 51.32/7.23    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 51.32/7.23  fof(f1038,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k1_xboole_0,X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1037,f30])).
% 51.32/7.23  fof(f30,plain,(
% 51.32/7.23    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f7])).
% 51.32/7.23  fof(f7,axiom,(
% 51.32/7.23    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 51.32/7.23  fof(f1037,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1036,f108])).
% 51.32/7.23  fof(f108,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 51.32/7.23    inference(forward_demodulation,[],[f94,f72])).
% 51.32/7.23  fof(f72,plain,(
% 51.32/7.23    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 51.32/7.23    inference(backward_demodulation,[],[f71,f63])).
% 51.32/7.23  fof(f63,plain,(
% 51.32/7.23    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 51.32/7.23    inference(definition_unfolding,[],[f33,f58])).
% 51.32/7.23  fof(f58,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f35,f57])).
% 51.32/7.23  fof(f57,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.32/7.23    inference(definition_unfolding,[],[f36,f56])).
% 51.32/7.23  fof(f56,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.32/7.23    inference(definition_unfolding,[],[f43,f55])).
% 51.32/7.23  fof(f55,plain,(
% 51.32/7.23    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.32/7.23    inference(definition_unfolding,[],[f49,f54])).
% 51.32/7.23  fof(f54,plain,(
% 51.32/7.23    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.32/7.23    inference(definition_unfolding,[],[f50,f53])).
% 51.32/7.23  fof(f53,plain,(
% 51.32/7.23    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.32/7.23    inference(definition_unfolding,[],[f51,f52])).
% 51.32/7.23  fof(f52,plain,(
% 51.32/7.23    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f15])).
% 51.32/7.23  fof(f15,axiom,(
% 51.32/7.23    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 51.32/7.23  fof(f51,plain,(
% 51.32/7.23    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f14])).
% 51.32/7.23  fof(f14,axiom,(
% 51.32/7.23    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 51.32/7.23  fof(f50,plain,(
% 51.32/7.23    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f13])).
% 51.32/7.23  fof(f13,axiom,(
% 51.32/7.23    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 51.32/7.23  fof(f49,plain,(
% 51.32/7.23    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f12])).
% 51.32/7.23  fof(f12,axiom,(
% 51.32/7.23    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 51.32/7.23  fof(f43,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f11])).
% 51.32/7.23  fof(f11,axiom,(
% 51.32/7.23    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 51.32/7.23  fof(f36,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f10])).
% 51.32/7.23  fof(f10,axiom,(
% 51.32/7.23    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 51.32/7.23  fof(f35,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f16])).
% 51.32/7.23  fof(f16,axiom,(
% 51.32/7.23    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 51.32/7.23  fof(f33,plain,(
% 51.32/7.23    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 51.32/7.23    inference(cnf_transformation,[],[f23])).
% 51.32/7.23  fof(f23,plain,(
% 51.32/7.23    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 51.32/7.23    inference(rectify,[],[f2])).
% 51.32/7.23  fof(f2,axiom,(
% 51.32/7.23    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 51.32/7.23  fof(f71,plain,(
% 51.32/7.23    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 51.32/7.23    inference(forward_demodulation,[],[f62,f30])).
% 51.32/7.23  fof(f62,plain,(
% 51.32/7.23    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 51.32/7.23    inference(definition_unfolding,[],[f32,f59])).
% 51.32/7.23  fof(f59,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f38,f58])).
% 51.32/7.23  fof(f38,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f9])).
% 51.32/7.23  fof(f9,axiom,(
% 51.32/7.23    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 51.32/7.23  fof(f32,plain,(
% 51.32/7.23    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 51.32/7.23    inference(cnf_transformation,[],[f22])).
% 51.32/7.23  fof(f22,plain,(
% 51.32/7.23    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 51.32/7.23    inference(rectify,[],[f3])).
% 51.32/7.23  fof(f3,axiom,(
% 51.32/7.23    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 51.32/7.23  fof(f94,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 51.32/7.23    inference(superposition,[],[f44,f30])).
% 51.32/7.23  fof(f44,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f6])).
% 51.32/7.23  fof(f6,axiom,(
% 51.32/7.23    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 51.32/7.23  fof(f1036,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1035,f423])).
% 51.32/7.23  fof(f423,plain,(
% 51.32/7.23    ( ! [X24,X23,X25,X22] : (k5_xboole_0(X24,k5_xboole_0(X23,k5_xboole_0(X22,X25))) = k5_xboole_0(X24,k5_xboole_0(X22,k5_xboole_0(X23,X25)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f422,f44])).
% 51.32/7.23  fof(f422,plain,(
% 51.32/7.23    ( ! [X24,X23,X25,X22] : (k5_xboole_0(X24,k5_xboole_0(k5_xboole_0(X22,X23),X25)) = k5_xboole_0(X24,k5_xboole_0(X23,k5_xboole_0(X22,X25)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f389,f421])).
% 51.32/7.23  fof(f421,plain,(
% 51.32/7.23    ( ! [X21,X19,X20,X18] : (k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X18,X20)),X21) = k5_xboole_0(X20,k5_xboole_0(X18,k5_xboole_0(X19,X21)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f388,f44])).
% 51.32/7.23  fof(f388,plain,(
% 51.32/7.23    ( ! [X21,X19,X20,X18] : (k5_xboole_0(X20,k5_xboole_0(k5_xboole_0(X18,X19),X21)) = k5_xboole_0(k5_xboole_0(X19,k5_xboole_0(X18,X20)),X21)) )),
% 51.32/7.23    inference(superposition,[],[f96,f96])).
% 51.32/7.23  fof(f96,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6)) )),
% 51.32/7.23    inference(superposition,[],[f44,f34])).
% 51.32/7.23  fof(f34,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 51.32/7.23    inference(cnf_transformation,[],[f1])).
% 51.32/7.23  fof(f1,axiom,(
% 51.32/7.23    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 51.32/7.23  fof(f389,plain,(
% 51.32/7.23    ( ! [X24,X23,X25,X22] : (k5_xboole_0(X24,k5_xboole_0(k5_xboole_0(X22,X23),X25)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X23,X24)),X25)) )),
% 51.32/7.23    inference(superposition,[],[f96,f44])).
% 51.32/7.23  fof(f1035,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1034,f221])).
% 51.32/7.23  fof(f221,plain,(
% 51.32/7.23    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f217,f44])).
% 51.32/7.23  fof(f217,plain,(
% 51.32/7.23    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) )),
% 51.32/7.23    inference(superposition,[],[f44,f116])).
% 51.32/7.23  fof(f116,plain,(
% 51.32/7.23    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 51.32/7.23    inference(superposition,[],[f108,f34])).
% 51.32/7.23  fof(f1034,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1033,f423])).
% 51.32/7.23  fof(f1033,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1032,f34])).
% 51.32/7.23  fof(f1032,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1031,f44])).
% 51.32/7.23  fof(f1031,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f1030,f213])).
% 51.32/7.23  fof(f213,plain,(
% 51.32/7.23    ( ! [X19,X17,X18] : (k5_xboole_0(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X18)) = k5_xboole_0(k2_zfmisc_1(k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X19)),X18),k2_zfmisc_1(k5_xboole_0(X17,k5_xboole_0(X19,k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X19)))),X18))) )),
% 51.32/7.23    inference(superposition,[],[f116,f82])).
% 51.32/7.23  fof(f82,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) )),
% 51.32/7.23    inference(backward_demodulation,[],[f79,f68])).
% 51.32/7.23  fof(f68,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 51.32/7.23    inference(definition_unfolding,[],[f47,f58,f58])).
% 51.32/7.23  fof(f47,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f18])).
% 51.32/7.23  fof(f18,axiom,(
% 51.32/7.23    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 51.32/7.23  fof(f79,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X2)) )),
% 51.32/7.23    inference(forward_demodulation,[],[f66,f44])).
% 51.32/7.23  fof(f66,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f45,f59,f59])).
% 51.32/7.23  fof(f45,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f19])).
% 51.32/7.23  fof(f19,axiom,(
% 51.32/7.23    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 51.32/7.23  fof(f1030,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),X6),k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f992,f34])).
% 51.32/7.23  fof(f992,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6) = k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,X5),X6),k5_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),X6),k2_zfmisc_1(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),X6)))) )),
% 51.32/7.23    inference(superposition,[],[f176,f74])).
% 51.32/7.23  fof(f74,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))))) )),
% 51.32/7.23    inference(backward_demodulation,[],[f64,f44])).
% 51.32/7.23  fof(f64,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f39,f58,f58,f59])).
% 51.32/7.23  fof(f39,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f8])).
% 51.32/7.23  fof(f8,axiom,(
% 51.32/7.23    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 51.32/7.23  fof(f176,plain,(
% 51.32/7.23    ( ! [X4,X5,X3] : (k5_xboole_0(k2_zfmisc_1(X3,X4),k5_xboole_0(k2_zfmisc_1(X5,X4),k2_zfmisc_1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5)),X4))) = k2_zfmisc_1(k5_xboole_0(X3,k5_xboole_0(X5,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5)))),X4)) )),
% 51.32/7.23    inference(superposition,[],[f82,f44])).
% 51.32/7.23  fof(f413,plain,(
% 51.32/7.23    ( ! [X30,X31,X29] : (k5_xboole_0(X29,X30) = k5_xboole_0(X31,k5_xboole_0(X30,k5_xboole_0(X29,X31)))) )),
% 51.32/7.23    inference(superposition,[],[f116,f96])).
% 51.32/7.23  fof(f1006,plain,(
% 51.32/7.23    ( ! [X35,X33,X34] : (k5_xboole_0(k2_zfmisc_1(X35,X34),k2_zfmisc_1(k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35)),X34)) = k5_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(k5_xboole_0(X33,k5_xboole_0(X35,k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X35)))),X34))) )),
% 51.32/7.23    inference(superposition,[],[f108,f176])).
% 51.32/7.23  fof(f19564,plain,(
% 51.32/7.23    k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 51.32/7.23    inference(subsumption_resolution,[],[f112,f19544])).
% 51.32/7.23  fof(f19544,plain,(
% 51.32/7.23    ( ! [X35,X33,X34] : (k5_xboole_0(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X33,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)))) = k2_zfmisc_1(X33,k5_xboole_0(X35,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35))))) )),
% 51.32/7.23    inference(backward_demodulation,[],[f718,f19543])).
% 51.32/7.23  fof(f19543,plain,(
% 51.32/7.23    ( ! [X41,X42,X40] : (k2_zfmisc_1(X40,X42) = k5_xboole_0(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k5_xboole_0(X41,X42)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f19417,f31])).
% 51.32/7.23  fof(f19417,plain,(
% 51.32/7.23    ( ! [X41,X42,X40] : (k5_xboole_0(k2_zfmisc_1(X40,X41),k2_zfmisc_1(X40,k5_xboole_0(X41,X42))) = k5_xboole_0(k2_zfmisc_1(X40,X42),k1_xboole_0)) )),
% 51.32/7.23    inference(superposition,[],[f413,f750])).
% 51.32/7.23  fof(f750,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k1_xboole_0 = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f749,f69])).
% 51.32/7.23  fof(f69,plain,(
% 51.32/7.23    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 51.32/7.23    inference(equality_resolution,[],[f42])).
% 51.32/7.23  fof(f42,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 51.32/7.23    inference(cnf_transformation,[],[f28])).
% 51.32/7.23  fof(f749,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k1_xboole_0) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f748,f30])).
% 51.32/7.23  fof(f748,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f747,f108])).
% 51.32/7.23  fof(f747,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f746,f423])).
% 51.32/7.23  fof(f746,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f745,f221])).
% 51.32/7.23  fof(f745,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f744,f423])).
% 51.32/7.23  fof(f744,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f743,f34])).
% 51.32/7.23  fof(f743,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f742,f44])).
% 51.32/7.23  fof(f742,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,X4),k2_zfmisc_1(X6,X5)))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f741,f212])).
% 51.32/7.23  fof(f212,plain,(
% 51.32/7.23    ( ! [X14,X15,X16] : (k5_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16)) = k5_xboole_0(k2_zfmisc_1(X14,k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16))),k2_zfmisc_1(X14,k5_xboole_0(X15,k5_xboole_0(X16,k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16))))))) )),
% 51.32/7.23    inference(superposition,[],[f116,f81])).
% 51.32/7.23  fof(f81,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 51.32/7.23    inference(backward_demodulation,[],[f78,f67])).
% 51.32/7.23  fof(f67,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f48,f58,f58])).
% 51.32/7.23  fof(f48,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f18])).
% 51.32/7.23  fof(f78,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f65,f44])).
% 51.32/7.23  fof(f65,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f46,f59,f59])).
% 51.32/7.23  fof(f46,plain,(
% 51.32/7.23    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f19])).
% 51.32/7.23  fof(f741,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))),k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))))) )),
% 51.32/7.23    inference(forward_demodulation,[],[f704,f34])).
% 51.32/7.23  fof(f704,plain,(
% 51.32/7.23    ( ! [X6,X4,X5] : (k2_zfmisc_1(X6,k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,X5)),k5_xboole_0(k2_zfmisc_1(X6,k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))),k2_zfmisc_1(X6,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) )),
% 51.32/7.23    inference(superposition,[],[f139,f74])).
% 51.32/7.23  fof(f139,plain,(
% 51.32/7.23    ( ! [X4,X5,X3] : (k5_xboole_0(k2_zfmisc_1(X3,X4),k5_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))) = k2_zfmisc_1(X3,k5_xboole_0(X4,k5_xboole_0(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))))) )),
% 51.32/7.23    inference(superposition,[],[f81,f44])).
% 51.32/7.23  fof(f718,plain,(
% 51.32/7.23    ( ! [X35,X33,X34] : (k5_xboole_0(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X33,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)))) = k5_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X33,k5_xboole_0(X34,k5_xboole_0(X35,k3_tarski(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35))))))) )),
% 51.32/7.23    inference(superposition,[],[f108,f139])).
% 51.32/7.23  fof(f112,plain,(
% 51.32/7.23    k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) != k2_zfmisc_1(k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 51.32/7.23    inference(forward_demodulation,[],[f111,f108])).
% 51.32/7.23  fof(f111,plain,(
% 51.32/7.23    k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)) | k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 51.32/7.23    inference(forward_demodulation,[],[f110,f108])).
% 51.32/7.23  fof(f110,plain,(
% 51.32/7.23    k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k2_zfmisc_1(sK2,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2))))),
% 51.32/7.23    inference(forward_demodulation,[],[f109,f108])).
% 51.32/7.23  fof(f109,plain,(
% 51.32/7.23    k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2))))),
% 51.32/7.23    inference(backward_demodulation,[],[f83,f108])).
% 51.32/7.23  fof(f83,plain,(
% 51.32/7.23    k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)))) | k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))),
% 51.32/7.23    inference(backward_demodulation,[],[f80,f68])).
% 51.32/7.23  fof(f80,plain,(
% 51.32/7.23    k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) | k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)),
% 51.32/7.23    inference(backward_demodulation,[],[f77,f67])).
% 51.32/7.23  fof(f77,plain,(
% 51.32/7.23    k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))),
% 51.32/7.23    inference(forward_demodulation,[],[f76,f44])).
% 51.32/7.23  fof(f76,plain,(
% 51.32/7.23    k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k2_zfmisc_1(sK1,sK2),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))) | k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))),
% 51.32/7.23    inference(forward_demodulation,[],[f75,f44])).
% 51.32/7.23  fof(f75,plain,(
% 51.32/7.23    k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) != k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))),
% 51.32/7.23    inference(forward_demodulation,[],[f73,f44])).
% 51.32/7.23  fof(f73,plain,(
% 51.32/7.23    k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k2_zfmisc_1(sK2,sK1),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))))) | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))),
% 51.32/7.23    inference(backward_demodulation,[],[f61,f44])).
% 51.32/7.23  fof(f61,plain,(
% 51.32/7.23    k2_zfmisc_1(sK2,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != k5_xboole_0(k2_zfmisc_1(sK2,sK0),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))) | k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) != k5_xboole_0(k2_zfmisc_1(sK0,sK2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))))),
% 51.32/7.23    inference(definition_unfolding,[],[f29,f60,f60,f60,f60])).
% 51.32/7.23  fof(f60,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 51.32/7.23    inference(definition_unfolding,[],[f37,f59])).
% 51.32/7.23  fof(f37,plain,(
% 51.32/7.23    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.32/7.23    inference(cnf_transformation,[],[f4])).
% 51.32/7.23  fof(f4,axiom,(
% 51.32/7.23    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 51.32/7.23  fof(f29,plain,(
% 51.32/7.23    k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),
% 51.32/7.23    inference(cnf_transformation,[],[f26])).
% 51.32/7.23  fof(f26,plain,(
% 51.32/7.23    k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),
% 51.32/7.23    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).
% 51.32/7.23  fof(f25,plain,(
% 51.32/7.23    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) => (k2_zfmisc_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),
% 51.32/7.23    introduced(choice_axiom,[])).
% 51.32/7.23  fof(f24,plain,(
% 51.32/7.23    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k2_zfmisc_1(k4_xboole_0(X0,X1),X2) != k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 51.32/7.23    inference(ennf_transformation,[],[f21])).
% 51.32/7.23  fof(f21,negated_conjecture,(
% 51.32/7.23    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 51.32/7.23    inference(negated_conjecture,[],[f20])).
% 51.32/7.23  fof(f20,conjecture,(
% 51.32/7.23    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 51.32/7.23    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 51.32/7.23  % SZS output end Proof for theBenchmark
% 51.32/7.23  % (28779)------------------------------
% 51.32/7.23  % (28779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 51.32/7.23  % (28779)Termination reason: Refutation
% 51.32/7.23  
% 51.32/7.23  % (28779)Memory used [KB]: 166308
% 51.32/7.23  % (28779)Time elapsed: 6.361 s
% 51.32/7.23  % (28779)------------------------------
% 51.32/7.23  % (28779)------------------------------
% 51.73/7.24  % (28727)Success in time 6.892 s
%------------------------------------------------------------------------------
