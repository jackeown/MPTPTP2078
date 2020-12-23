%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:56 EST 2020

% Result     : Theorem 35.74s
% Output     : Refutation 35.74s
% Verified   : 
% Statistics : Number of formulae       :  156 (9309 expanded)
%              Number of leaves         :   20 (3103 expanded)
%              Depth                    :   44
%              Number of atoms          :  158 (9311 expanded)
%              Number of equality atoms :  157 (9310 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41771,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41770,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f41770,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f41769,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f41769,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f41665,f1134])).

fof(f1134,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1121,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1121,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f139,f31])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f133,f31])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f36,f31])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f41665,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f41424,f37837])).

fof(f37837,plain,(
    ! [X146,X147,X145,X148] : k2_enumset1(X146,X145,X147,X148) = k2_enumset1(X146,X145,X148,X147) ),
    inference(superposition,[],[f33142,f22102])).

fof(f22102,plain,(
    ! [X109,X107,X110,X108] : k2_enumset1(X107,X108,X109,X110) = k2_enumset1(X108,X107,X109,X110) ),
    inference(superposition,[],[f22049,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f22049,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X4,X5,X6,X7) = k2_enumset1(X5,X4,X6,X7) ),
    inference(forward_demodulation,[],[f21907,f21950])).

fof(f21950,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f21906,f35])).

fof(f21906,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f1770,f1065])).

fof(f1065,plain,(
    ! [X2,X1] : k2_tarski(X2,X1) = k1_enumset1(X1,X1,X2) ),
    inference(superposition,[],[f1036,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f1036,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X0,X1,X0) ),
    inference(forward_demodulation,[],[f1029,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f1029,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f1005,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f1005,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k1_enumset1(X0,X2,X1) ),
    inference(forward_demodulation,[],[f1000,f32])).

fof(f1000,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f986,f35])).

fof(f986,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(forward_demodulation,[],[f980,f35])).

fof(f980,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X0,X1,X3,X2) ),
    inference(superposition,[],[f965,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f965,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X4) = k3_enumset1(X0,X1,X2,X4,X3) ),
    inference(forward_demodulation,[],[f962,f37])).

fof(f962,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X4,X3) ),
    inference(superposition,[],[f961,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f961,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X0,X5) ),
    inference(backward_demodulation,[],[f621,f959])).

fof(f959,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X5,X4) ),
    inference(forward_demodulation,[],[f954,f38])).

fof(f954,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k5_enumset1(X0,X0,X1,X2,X3,X5,X4) ),
    inference(superposition,[],[f860,f37])).

fof(f860,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) = k5_enumset1(X1,X2,X3,X4,X5,X0,X6) ),
    inference(backward_demodulation,[],[f170,f858])).

fof(f858,plain,(
    ! [X30,X35,X33,X31,X36,X34,X32] : k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k5_enumset1(X32,X33,X34,X35,X36,X31,X30) ),
    inference(forward_demodulation,[],[f849,f180])).

fof(f180,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f169,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f169,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f40,f37])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f849,plain,(
    ! [X30,X35,X33,X31,X36,X34,X32] : k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k2_tarski(X31,X30)) ),
    inference(superposition,[],[f289,f49])).

fof(f289,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(backward_demodulation,[],[f241,f288])).

fof(f288,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f276,f40])).

fof(f276,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f43,f38])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f241,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f42,f37])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f170,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) ),
    inference(superposition,[],[f40,f25])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f621,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f180,f25])).

fof(f1770,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f1742,f37])).

fof(f1742,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f635,f32])).

fof(f635,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f620,f38])).

fof(f620,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f180,f35])).

fof(f21907,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f1770,f27])).

fof(f33142,plain,(
    ! [X127,X125,X126,X124] : k2_enumset1(X124,X125,X127,X126) = k2_enumset1(X125,X124,X126,X127) ),
    inference(superposition,[],[f22055,f986])).

fof(f22055,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X2,X1,X3,X0) ),
    inference(forward_demodulation,[],[f21926,f21957])).

fof(f21957,plain,(
    ! [X47,X45,X48,X46] : k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) = k2_enumset1(X46,X45,X47,X48) ),
    inference(backward_demodulation,[],[f5381,f21951])).

fof(f21951,plain,(
    ! [X26,X24,X23,X25] : k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)) = k2_enumset1(X24,X23,X26,X25) ),
    inference(backward_demodulation,[],[f5858,f21950])).

fof(f5858,plain,(
    ! [X26,X24,X23,X25] : k2_xboole_0(k2_tarski(X23,X24),k2_tarski(X26,X25)) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)) ),
    inference(forward_demodulation,[],[f5840,f3716])).

fof(f3716,plain,(
    ! [X50,X48,X51,X49] : k5_enumset1(X48,X48,X48,X48,X49,X50,X51) = k2_xboole_0(k1_tarski(X48),k1_enumset1(X49,X50,X51)) ),
    inference(superposition,[],[f855,f2030])).

fof(f2030,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(backward_demodulation,[],[f1963,f2028])).

fof(f2028,plain,(
    ! [X4] : k1_tarski(X4) = k3_tarski(k1_tarski(k1_tarski(X4))) ),
    inference(forward_demodulation,[],[f2007,f25])).

fof(f2007,plain,(
    ! [X4] : k2_tarski(X4,X4) = k3_tarski(k1_tarski(k1_tarski(X4))) ),
    inference(superposition,[],[f1963,f1459])).

fof(f1459,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_enumset1(X2,X3,X2,X3) ),
    inference(forward_demodulation,[],[f1443,f27])).

fof(f1443,plain,(
    ! [X2,X3] : k1_enumset1(X2,X2,X3) = k2_enumset1(X2,X3,X2,X3) ),
    inference(superposition,[],[f1309,f1005])).

fof(f1309,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X1) = k2_enumset1(X0,X1,X2,X0) ),
    inference(superposition,[],[f1233,f35])).

fof(f1233,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X2) = k2_enumset1(X0,X2,X3,X1) ),
    inference(forward_demodulation,[],[f1222,f35])).

fof(f1222,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X2) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(superposition,[],[f1186,f37])).

fof(f1186,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X3) = k3_enumset1(X0,X1,X3,X4,X2) ),
    inference(forward_demodulation,[],[f1179,f37])).

fof(f1179,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X3) = k4_enumset1(X0,X0,X1,X3,X4,X2) ),
    inference(superposition,[],[f988,f38])).

fof(f988,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k4_enumset1(X4,X5,X6,X8,X9,X7) ),
    inference(forward_demodulation,[],[f982,f959])).

fof(f982,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k2_xboole_0(k3_enumset1(X4,X5,X6,X8,X7),k1_tarski(X9)) ),
    inference(superposition,[],[f860,f965])).

fof(f1963,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f1894,f35])).

fof(f1894,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f1880,f25])).

fof(f1880,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f1876,f37])).

fof(f1876,plain,(
    ! [X4,X3] : k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_tarski(X4,X3))) ),
    inference(forward_demodulation,[],[f1875,f49])).

fof(f1875,plain,(
    ! [X4,X3] : k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k1_enumset1(X3,X4,X4))) ),
    inference(forward_demodulation,[],[f1867,f32])).

fof(f1867,plain,(
    ! [X4,X3] : k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_enumset1(X3,X3,X4,X4))) ),
    inference(superposition,[],[f972,f960])).

fof(f960,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) = k4_enumset1(X0,X1,X2,X3,X5,X4) ),
    inference(backward_demodulation,[],[f687,f959])).

fof(f687,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f170,f37])).

fof(f972,plain,(
    ! [X10,X8,X11,X9] : k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11) ),
    inference(superposition,[],[f290,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f290,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(backward_demodulation,[],[f195,f288])).

fof(f195,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(superposition,[],[f41,f35])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f855,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(forward_demodulation,[],[f844,f39])).

fof(f844,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f289,f35])).

fof(f5840,plain,(
    ! [X26,X24,X23,X25] : k2_xboole_0(k2_tarski(X23,X24),k2_tarski(X26,X25)) = k5_enumset1(X23,X23,X23,X23,X24,X25,X26) ),
    inference(superposition,[],[f622,f5322])).

fof(f5322,plain,(
    ! [X8,X7] : k2_tarski(X7,X8) = k3_enumset1(X7,X7,X7,X7,X8) ),
    inference(superposition,[],[f4971,f5046])).

fof(f5046,plain,(
    ! [X2,X1] : k2_tarski(X2,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X1)) ),
    inference(superposition,[],[f4969,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4969,plain,(
    ! [X2,X1] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X1)) ),
    inference(superposition,[],[f2046,f2977])).

fof(f2977,plain,(
    ! [X2,X1] : k2_tarski(X1,X2) = k4_enumset1(X1,X1,X1,X1,X2,X1) ),
    inference(backward_demodulation,[],[f2031,f2976])).

fof(f2976,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f2942,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f29,f27])).

fof(f2942,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f2908,f32])).

fof(f2908,plain,(
    ! [X4,X5] : k2_enumset1(X4,X4,X5,X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(superposition,[],[f2842,f1233])).

fof(f2842,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_enumset1(X0,X0,X0,X1,X0) ),
    inference(superposition,[],[f2031,f37])).

fof(f2031,plain,(
    ! [X2,X1] : k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(backward_demodulation,[],[f1968,f2028])).

fof(f1968,plain,(
    ! [X2,X1] : k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X1))),k1_tarski(X2)) ),
    inference(superposition,[],[f959,f1894])).

fof(f2046,plain,(
    ! [X6,X4,X5] : k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k1_tarski(X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f2016,f2028])).

fof(f2016,plain,(
    ! [X6,X4,X5] : k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X4))),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f635,f1963])).

fof(f4971,plain,(
    ! [X10,X8,X9] : k3_enumset1(X8,X8,X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10)) ),
    inference(superposition,[],[f2046,f37])).

fof(f622,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k5_enumset1(X8,X9,X10,X11,X12,X6,X7) = k2_xboole_0(k3_enumset1(X8,X9,X10,X11,X12),k2_tarski(X7,X6)) ),
    inference(superposition,[],[f180,f26])).

fof(f5381,plain,(
    ! [X47,X45,X48,X46] : k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47)) ),
    inference(backward_demodulation,[],[f4996,f5370])).

fof(f5370,plain,(
    ! [X30,X31,X32] : k1_enumset1(X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32)) ),
    inference(forward_demodulation,[],[f5298,f32])).

fof(f5298,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32)) ),
    inference(superposition,[],[f4971,f35])).

fof(f4996,plain,(
    ! [X47,X45,X48,X46] : k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47)) ),
    inference(forward_demodulation,[],[f4984,f3716])).

fof(f4984,plain,(
    ! [X47,X45,X48,X46] : k5_enumset1(X45,X45,X45,X45,X46,X48,X47) = k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48)) ),
    inference(superposition,[],[f860,f2046])).

fof(f21926,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f1770,f25])).

fof(f41424,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f24,f37840])).

fof(f37840,plain,(
    ! [X158,X159,X157,X160] : k2_enumset1(X158,X160,X159,X157) = k2_enumset1(X158,X157,X160,X159) ),
    inference(superposition,[],[f33142,f28903])).

fof(f28903,plain,(
    ! [X99,X97,X100,X98] : k2_enumset1(X97,X100,X99,X98) = k2_enumset1(X98,X97,X99,X100) ),
    inference(superposition,[],[f22102,f15780])).

fof(f15780,plain,(
    ! [X78,X76,X79,X77] : k2_enumset1(X76,X77,X78,X79) = k2_enumset1(X76,X79,X78,X77) ),
    inference(superposition,[],[f14698,f1234])).

fof(f1234,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X7,X7,X6) = k2_enumset1(X4,X5,X7,X6) ),
    inference(forward_demodulation,[],[f1223,f986])).

fof(f1223,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X4,X5,X7,X7,X6) ),
    inference(superposition,[],[f1186,f965])).

fof(f14698,plain,(
    ! [X47,X50,X48,X49] : k3_enumset1(X47,X48,X49,X49,X50) = k2_enumset1(X47,X50,X49,X48) ),
    inference(forward_demodulation,[],[f14611,f3625])).

fof(f3625,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k3_enumset1(X8,X10,X9,X10,X11) ),
    inference(forward_demodulation,[],[f3606,f1234])).

fof(f3606,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X9,X10,X10,X11) = k3_enumset1(X8,X10,X9,X10,X11) ),
    inference(superposition,[],[f1771,f1187])).

fof(f1187,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X9,X9,X8) = k3_enumset1(X5,X6,X7,X9,X8) ),
    inference(forward_demodulation,[],[f1180,f965])).

fof(f1180,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X8,X9,X9) = k4_enumset1(X5,X6,X7,X9,X9,X8) ),
    inference(superposition,[],[f988,f961])).

fof(f1771,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X7,X8,X9) = k3_enumset1(X5,X7,X6,X8,X9) ),
    inference(forward_demodulation,[],[f1743,f1770])).

fof(f1743,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X7,X8,X9) = k2_xboole_0(k1_enumset1(X5,X7,X6),k2_tarski(X8,X9)) ),
    inference(superposition,[],[f635,f1005])).

fof(f14611,plain,(
    ! [X47,X50,X48,X49] : k3_enumset1(X47,X48,X49,X49,X50) = k3_enumset1(X47,X49,X50,X49,X48) ),
    inference(superposition,[],[f1808,f965])).

fof(f1808,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X10,X11,X12,X13,X14,X12) = k3_enumset1(X10,X12,X13,X14,X11) ),
    inference(forward_demodulation,[],[f1801,f1773])).

fof(f1773,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) = k3_enumset1(X1,X2,X3,X0,X4) ),
    inference(forward_demodulation,[],[f1754,f965])).

fof(f1754,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) ),
    inference(superposition,[],[f635,f25])).

fof(f1801,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X10,X11,X12,X13,X14,X12) = k2_xboole_0(k2_enumset1(X10,X12,X13,X11),k1_tarski(X14)) ),
    inference(superposition,[],[f959,f1233])).

fof(f24,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (514)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (505)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (516)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (521)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (510)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (508)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (507)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (513)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (515)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (515)Refutation not found, incomplete strategy% (515)------------------------------
% 0.21/0.48  % (515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (515)Memory used [KB]: 10618
% 0.21/0.48  % (515)Time elapsed: 0.069 s
% 0.21/0.48  % (515)------------------------------
% 0.21/0.48  % (515)------------------------------
% 0.21/0.48  % (512)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (519)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (509)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (511)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (504)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (517)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (506)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (520)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (518)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 5.24/1.07  % (508)Time limit reached!
% 5.24/1.07  % (508)------------------------------
% 5.24/1.07  % (508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.07  % (508)Termination reason: Time limit
% 5.24/1.07  % (508)Termination phase: Saturation
% 5.24/1.07  
% 5.24/1.07  % (508)Memory used [KB]: 11257
% 5.24/1.07  % (508)Time elapsed: 0.600 s
% 5.24/1.07  % (508)------------------------------
% 5.24/1.07  % (508)------------------------------
% 12.37/1.92  % (509)Time limit reached!
% 12.37/1.92  % (509)------------------------------
% 12.37/1.92  % (509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.37/1.93  % (509)Termination reason: Time limit
% 12.37/1.93  % (509)Termination phase: Saturation
% 12.37/1.93  
% 12.37/1.93  % (509)Memory used [KB]: 33517
% 12.37/1.93  % (509)Time elapsed: 1.500 s
% 12.37/1.93  % (509)------------------------------
% 12.37/1.93  % (509)------------------------------
% 12.37/1.93  % (510)Time limit reached!
% 12.37/1.93  % (510)------------------------------
% 12.37/1.93  % (510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.37/1.95  % (510)Termination reason: Time limit
% 12.37/1.95  % (510)Termination phase: Saturation
% 12.37/1.95  
% 12.37/1.95  % (510)Memory used [KB]: 24434
% 12.37/1.95  % (510)Time elapsed: 1.500 s
% 12.37/1.95  % (510)------------------------------
% 12.37/1.95  % (510)------------------------------
% 14.83/2.22  % (506)Time limit reached!
% 14.83/2.22  % (506)------------------------------
% 14.83/2.22  % (506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.83/2.22  % (506)Termination reason: Time limit
% 14.83/2.22  % (506)Termination phase: Saturation
% 14.83/2.22  
% 14.83/2.22  % (506)Memory used [KB]: 27121
% 14.83/2.22  % (506)Time elapsed: 1.800 s
% 14.83/2.22  % (506)------------------------------
% 14.83/2.22  % (506)------------------------------
% 17.88/2.67  % (516)Time limit reached!
% 17.88/2.67  % (516)------------------------------
% 17.88/2.67  % (516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.88/2.67  % (516)Termination reason: Time limit
% 17.88/2.67  % (516)Termination phase: Saturation
% 17.88/2.67  
% 17.88/2.67  % (516)Memory used [KB]: 20340
% 17.88/2.67  % (516)Time elapsed: 2.200 s
% 17.88/2.67  % (516)------------------------------
% 17.88/2.67  % (516)------------------------------
% 35.74/4.90  % (507)Refutation found. Thanks to Tanya!
% 35.74/4.90  % SZS status Theorem for theBenchmark
% 35.74/4.91  % SZS output start Proof for theBenchmark
% 35.74/4.91  fof(f41771,plain,(
% 35.74/4.91    $false),
% 35.74/4.91    inference(subsumption_resolution,[],[f41770,f30])).
% 35.74/4.91  fof(f30,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f18])).
% 35.74/4.91  fof(f18,axiom,(
% 35.74/4.91    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 35.74/4.91  fof(f41770,plain,(
% 35.74/4.91    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 35.74/4.91    inference(forward_demodulation,[],[f41769,f34])).
% 35.74/4.91  fof(f34,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 35.74/4.91    inference(cnf_transformation,[],[f16])).
% 35.74/4.91  fof(f16,axiom,(
% 35.74/4.91    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 35.74/4.91  fof(f41769,plain,(
% 35.74/4.91    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 35.74/4.91    inference(superposition,[],[f41665,f1134])).
% 35.74/4.91  fof(f1134,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1121,f31])).
% 35.74/4.91  fof(f31,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f17])).
% 35.74/4.91  fof(f17,axiom,(
% 35.74/4.91    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 35.74/4.91  fof(f1121,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 35.74/4.91    inference(superposition,[],[f139,f31])).
% 35.74/4.91  fof(f139,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f133,f31])).
% 35.74/4.91  fof(f133,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 35.74/4.91    inference(superposition,[],[f36,f31])).
% 35.74/4.91  fof(f36,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 35.74/4.91    inference(cnf_transformation,[],[f15])).
% 35.74/4.91  fof(f15,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 35.74/4.91  fof(f41665,plain,(
% 35.74/4.91    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 35.74/4.91    inference(superposition,[],[f41424,f37837])).
% 35.74/4.91  fof(f37837,plain,(
% 35.74/4.91    ( ! [X146,X147,X145,X148] : (k2_enumset1(X146,X145,X147,X148) = k2_enumset1(X146,X145,X148,X147)) )),
% 35.74/4.91    inference(superposition,[],[f33142,f22102])).
% 35.74/4.91  fof(f22102,plain,(
% 35.74/4.91    ( ! [X109,X107,X110,X108] : (k2_enumset1(X107,X108,X109,X110) = k2_enumset1(X108,X107,X109,X110)) )),
% 35.74/4.91    inference(superposition,[],[f22049,f35])).
% 35.74/4.91  fof(f35,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f10])).
% 35.74/4.91  fof(f10,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 35.74/4.91  fof(f22049,plain,(
% 35.74/4.91    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X4,X5,X6,X7) = k2_enumset1(X5,X4,X6,X7)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f21907,f21950])).
% 35.74/4.91  fof(f21950,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f21906,f35])).
% 35.74/4.91  fof(f21906,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3))) )),
% 35.74/4.91    inference(superposition,[],[f1770,f1065])).
% 35.74/4.91  fof(f1065,plain,(
% 35.74/4.91    ( ! [X2,X1] : (k2_tarski(X2,X1) = k1_enumset1(X1,X1,X2)) )),
% 35.74/4.91    inference(superposition,[],[f1036,f29])).
% 35.74/4.91  fof(f29,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f2])).
% 35.74/4.91  fof(f2,axiom,(
% 35.74/4.91    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 35.74/4.91  fof(f1036,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X0)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1029,f49])).
% 35.74/4.91  fof(f49,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 35.74/4.91    inference(superposition,[],[f29,f27])).
% 35.74/4.91  fof(f27,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f8])).
% 35.74/4.91  fof(f8,axiom,(
% 35.74/4.91    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 35.74/4.91  fof(f1029,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 35.74/4.91    inference(superposition,[],[f1005,f32])).
% 35.74/4.91  fof(f32,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f9])).
% 35.74/4.91  fof(f9,axiom,(
% 35.74/4.91    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 35.74/4.91  fof(f1005,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k1_enumset1(X0,X2,X1)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1000,f32])).
% 35.74/4.91  fof(f1000,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 35.74/4.91    inference(superposition,[],[f986,f35])).
% 35.74/4.91  fof(f986,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f980,f35])).
% 35.74/4.91  fof(f980,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X0,X1,X3,X2)) )),
% 35.74/4.91    inference(superposition,[],[f965,f37])).
% 35.74/4.91  fof(f37,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f11])).
% 35.74/4.91  fof(f11,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 35.74/4.91  fof(f965,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X4) = k3_enumset1(X0,X1,X2,X4,X3)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f962,f37])).
% 35.74/4.91  fof(f962,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X4,X3)) )),
% 35.74/4.91    inference(superposition,[],[f961,f38])).
% 35.74/4.91  fof(f38,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f12])).
% 35.74/4.91  fof(f12,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 35.74/4.91  fof(f961,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X0,X5)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f621,f959])).
% 35.74/4.91  fof(f959,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X5,X4)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f954,f38])).
% 35.74/4.91  fof(f954,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k5_enumset1(X0,X0,X1,X2,X3,X5,X4)) )),
% 35.74/4.91    inference(superposition,[],[f860,f37])).
% 35.74/4.91  fof(f860,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) = k5_enumset1(X1,X2,X3,X4,X5,X0,X6)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f170,f858])).
% 35.74/4.91  fof(f858,plain,(
% 35.74/4.91    ( ! [X30,X35,X33,X31,X36,X34,X32] : (k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k5_enumset1(X32,X33,X34,X35,X36,X31,X30)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f849,f180])).
% 35.74/4.91  fof(f180,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f169,f39])).
% 35.74/4.91  fof(f39,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f13])).
% 35.74/4.91  fof(f13,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 35.74/4.91  fof(f169,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 35.74/4.91    inference(superposition,[],[f40,f37])).
% 35.74/4.91  fof(f40,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 35.74/4.91    inference(cnf_transformation,[],[f6])).
% 35.74/4.91  fof(f6,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 35.74/4.91  fof(f849,plain,(
% 35.74/4.91    ( ! [X30,X35,X33,X31,X36,X34,X32] : (k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k2_tarski(X31,X30))) )),
% 35.74/4.91    inference(superposition,[],[f289,f49])).
% 35.74/4.91  fof(f289,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 35.74/4.91    inference(backward_demodulation,[],[f241,f288])).
% 35.74/4.91  fof(f288,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f276,f40])).
% 35.74/4.91  fof(f276,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 35.74/4.91    inference(superposition,[],[f43,f38])).
% 35.74/4.91  fof(f43,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 35.74/4.91    inference(cnf_transformation,[],[f5])).
% 35.74/4.91  fof(f5,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 35.74/4.91  fof(f241,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 35.74/4.91    inference(superposition,[],[f42,f37])).
% 35.74/4.91  fof(f42,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 35.74/4.91    inference(cnf_transformation,[],[f4])).
% 35.74/4.91  fof(f4,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 35.74/4.91  fof(f170,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) )),
% 35.74/4.91    inference(superposition,[],[f40,f25])).
% 35.74/4.91  fof(f25,plain,(
% 35.74/4.91    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f7])).
% 35.74/4.91  fof(f7,axiom,(
% 35.74/4.91    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 35.74/4.91  fof(f621,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 35.74/4.91    inference(superposition,[],[f180,f25])).
% 35.74/4.91  fof(f1770,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1742,f37])).
% 35.74/4.91  fof(f1742,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 35.74/4.91    inference(superposition,[],[f635,f32])).
% 35.74/4.91  fof(f635,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f620,f38])).
% 35.74/4.91  fof(f620,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 35.74/4.91    inference(superposition,[],[f180,f35])).
% 35.74/4.91  fof(f21907,plain,(
% 35.74/4.91    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) )),
% 35.74/4.91    inference(superposition,[],[f1770,f27])).
% 35.74/4.91  fof(f33142,plain,(
% 35.74/4.91    ( ! [X127,X125,X126,X124] : (k2_enumset1(X124,X125,X127,X126) = k2_enumset1(X125,X124,X126,X127)) )),
% 35.74/4.91    inference(superposition,[],[f22055,f986])).
% 35.74/4.91  fof(f22055,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X2,X1,X3,X0)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f21926,f21957])).
% 35.74/4.91  fof(f21957,plain,(
% 35.74/4.91    ( ! [X47,X45,X48,X46] : (k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) = k2_enumset1(X46,X45,X47,X48)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f5381,f21951])).
% 35.74/4.91  fof(f21951,plain,(
% 35.74/4.91    ( ! [X26,X24,X23,X25] : (k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)) = k2_enumset1(X24,X23,X26,X25)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f5858,f21950])).
% 35.74/4.91  fof(f5858,plain,(
% 35.74/4.91    ( ! [X26,X24,X23,X25] : (k2_xboole_0(k2_tarski(X23,X24),k2_tarski(X26,X25)) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f5840,f3716])).
% 35.74/4.91  fof(f3716,plain,(
% 35.74/4.91    ( ! [X50,X48,X51,X49] : (k5_enumset1(X48,X48,X48,X48,X49,X50,X51) = k2_xboole_0(k1_tarski(X48),k1_enumset1(X49,X50,X51))) )),
% 35.74/4.91    inference(superposition,[],[f855,f2030])).
% 35.74/4.91  fof(f2030,plain,(
% 35.74/4.91    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f1963,f2028])).
% 35.74/4.91  fof(f2028,plain,(
% 35.74/4.91    ( ! [X4] : (k1_tarski(X4) = k3_tarski(k1_tarski(k1_tarski(X4)))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f2007,f25])).
% 35.74/4.91  fof(f2007,plain,(
% 35.74/4.91    ( ! [X4] : (k2_tarski(X4,X4) = k3_tarski(k1_tarski(k1_tarski(X4)))) )),
% 35.74/4.91    inference(superposition,[],[f1963,f1459])).
% 35.74/4.91  fof(f1459,plain,(
% 35.74/4.91    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_enumset1(X2,X3,X2,X3)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1443,f27])).
% 35.74/4.91  fof(f1443,plain,(
% 35.74/4.91    ( ! [X2,X3] : (k1_enumset1(X2,X2,X3) = k2_enumset1(X2,X3,X2,X3)) )),
% 35.74/4.91    inference(superposition,[],[f1309,f1005])).
% 35.74/4.91  fof(f1309,plain,(
% 35.74/4.91    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X1) = k2_enumset1(X0,X1,X2,X0)) )),
% 35.74/4.91    inference(superposition,[],[f1233,f35])).
% 35.74/4.91  fof(f1233,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X2) = k2_enumset1(X0,X2,X3,X1)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1222,f35])).
% 35.74/4.91  fof(f1222,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X2) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 35.74/4.91    inference(superposition,[],[f1186,f37])).
% 35.74/4.91  fof(f1186,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X3) = k3_enumset1(X0,X1,X3,X4,X2)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1179,f37])).
% 35.74/4.91  fof(f1179,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X3) = k4_enumset1(X0,X0,X1,X3,X4,X2)) )),
% 35.74/4.91    inference(superposition,[],[f988,f38])).
% 35.74/4.91  fof(f988,plain,(
% 35.74/4.91    ( ! [X6,X4,X8,X7,X5,X9] : (k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k4_enumset1(X4,X5,X6,X8,X9,X7)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f982,f959])).
% 35.74/4.91  fof(f982,plain,(
% 35.74/4.91    ( ! [X6,X4,X8,X7,X5,X9] : (k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k2_xboole_0(k3_enumset1(X4,X5,X6,X8,X7),k1_tarski(X9))) )),
% 35.74/4.91    inference(superposition,[],[f860,f965])).
% 35.74/4.91  fof(f1963,plain,(
% 35.74/4.91    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 35.74/4.91    inference(superposition,[],[f1894,f35])).
% 35.74/4.91  fof(f1894,plain,(
% 35.74/4.91    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1880,f25])).
% 35.74/4.91  fof(f1880,plain,(
% 35.74/4.91    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0)))) )),
% 35.74/4.91    inference(superposition,[],[f1876,f37])).
% 35.74/4.91  fof(f1876,plain,(
% 35.74/4.91    ( ! [X4,X3] : (k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_tarski(X4,X3)))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1875,f49])).
% 35.74/4.91  fof(f1875,plain,(
% 35.74/4.91    ( ! [X4,X3] : (k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k1_enumset1(X3,X4,X4)))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1867,f32])).
% 35.74/4.91  fof(f1867,plain,(
% 35.74/4.91    ( ! [X4,X3] : (k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_enumset1(X3,X3,X4,X4)))) )),
% 35.74/4.91    inference(superposition,[],[f972,f960])).
% 35.74/4.91  fof(f960,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) = k4_enumset1(X0,X1,X2,X3,X5,X4)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f687,f959])).
% 35.74/4.91  fof(f687,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5)) )),
% 35.74/4.91    inference(superposition,[],[f170,f37])).
% 35.74/4.91  fof(f972,plain,(
% 35.74/4.91    ( ! [X10,X8,X11,X9] : (k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11)) )),
% 35.74/4.91    inference(superposition,[],[f290,f44])).
% 35.74/4.91  fof(f44,plain,(
% 35.74/4.91    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 35.74/4.91    inference(superposition,[],[f28,f25])).
% 35.74/4.91  fof(f28,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f14])).
% 35.74/4.91  fof(f14,axiom,(
% 35.74/4.91    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 35.74/4.91  fof(f290,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 35.74/4.91    inference(backward_demodulation,[],[f195,f288])).
% 35.74/4.91  fof(f195,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 35.74/4.91    inference(superposition,[],[f41,f35])).
% 35.74/4.91  fof(f41,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 35.74/4.91    inference(cnf_transformation,[],[f3])).
% 35.74/4.91  fof(f3,axiom,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 35.74/4.91  fof(f855,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f844,f39])).
% 35.74/4.91  fof(f844,plain,(
% 35.74/4.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 35.74/4.91    inference(superposition,[],[f289,f35])).
% 35.74/4.91  fof(f5840,plain,(
% 35.74/4.91    ( ! [X26,X24,X23,X25] : (k2_xboole_0(k2_tarski(X23,X24),k2_tarski(X26,X25)) = k5_enumset1(X23,X23,X23,X23,X24,X25,X26)) )),
% 35.74/4.91    inference(superposition,[],[f622,f5322])).
% 35.74/4.91  fof(f5322,plain,(
% 35.74/4.91    ( ! [X8,X7] : (k2_tarski(X7,X8) = k3_enumset1(X7,X7,X7,X7,X8)) )),
% 35.74/4.91    inference(superposition,[],[f4971,f5046])).
% 35.74/4.91  fof(f5046,plain,(
% 35.74/4.91    ( ! [X2,X1] : (k2_tarski(X2,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X2,X1))) )),
% 35.74/4.91    inference(superposition,[],[f4969,f26])).
% 35.74/4.91  fof(f26,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 35.74/4.91    inference(cnf_transformation,[],[f1])).
% 35.74/4.91  fof(f1,axiom,(
% 35.74/4.91    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 35.74/4.91  fof(f4969,plain,(
% 35.74/4.91    ( ! [X2,X1] : (k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X1))) )),
% 35.74/4.91    inference(superposition,[],[f2046,f2977])).
% 35.74/4.91  fof(f2977,plain,(
% 35.74/4.91    ( ! [X2,X1] : (k2_tarski(X1,X2) = k4_enumset1(X1,X1,X1,X1,X2,X1)) )),
% 35.74/4.91    inference(backward_demodulation,[],[f2031,f2976])).
% 35.74/4.91  fof(f2976,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f2942,f47])).
% 35.74/4.91  fof(f47,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 35.74/4.91    inference(superposition,[],[f29,f27])).
% 35.74/4.91  fof(f2942,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 35.74/4.91    inference(superposition,[],[f2908,f32])).
% 35.74/4.91  fof(f2908,plain,(
% 35.74/4.91    ( ! [X4,X5] : (k2_enumset1(X4,X4,X5,X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 35.74/4.91    inference(superposition,[],[f2842,f1233])).
% 35.74/4.91  fof(f2842,plain,(
% 35.74/4.91    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_enumset1(X0,X0,X0,X1,X0)) )),
% 35.74/4.91    inference(superposition,[],[f2031,f37])).
% 35.74/4.91  fof(f2031,plain,(
% 35.74/4.91    ( ! [X2,X1] : (k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) )),
% 35.74/4.91    inference(backward_demodulation,[],[f1968,f2028])).
% 35.74/4.91  fof(f1968,plain,(
% 35.74/4.91    ( ! [X2,X1] : (k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X1))),k1_tarski(X2))) )),
% 35.74/4.91    inference(superposition,[],[f959,f1894])).
% 35.74/4.91  fof(f2046,plain,(
% 35.74/4.91    ( ! [X6,X4,X5] : (k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k1_tarski(X4),k2_tarski(X5,X6))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f2016,f2028])).
% 35.74/4.91  fof(f2016,plain,(
% 35.74/4.91    ( ! [X6,X4,X5] : (k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X4))),k2_tarski(X5,X6))) )),
% 35.74/4.91    inference(superposition,[],[f635,f1963])).
% 35.74/4.91  fof(f4971,plain,(
% 35.74/4.91    ( ! [X10,X8,X9] : (k3_enumset1(X8,X8,X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10))) )),
% 35.74/4.91    inference(superposition,[],[f2046,f37])).
% 35.74/4.91  fof(f622,plain,(
% 35.74/4.91    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k5_enumset1(X8,X9,X10,X11,X12,X6,X7) = k2_xboole_0(k3_enumset1(X8,X9,X10,X11,X12),k2_tarski(X7,X6))) )),
% 35.74/4.91    inference(superposition,[],[f180,f26])).
% 35.74/4.91  fof(f5381,plain,(
% 35.74/4.91    ( ! [X47,X45,X48,X46] : (k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47))) )),
% 35.74/4.91    inference(backward_demodulation,[],[f4996,f5370])).
% 35.74/4.91  fof(f5370,plain,(
% 35.74/4.91    ( ! [X30,X31,X32] : (k1_enumset1(X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f5298,f32])).
% 35.74/4.91  fof(f5298,plain,(
% 35.74/4.91    ( ! [X30,X31,X32] : (k2_enumset1(X30,X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32))) )),
% 35.74/4.91    inference(superposition,[],[f4971,f35])).
% 35.74/4.91  fof(f4996,plain,(
% 35.74/4.91    ( ! [X47,X45,X48,X46] : (k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47))) )),
% 35.74/4.91    inference(forward_demodulation,[],[f4984,f3716])).
% 35.74/4.91  fof(f4984,plain,(
% 35.74/4.91    ( ! [X47,X45,X48,X46] : (k5_enumset1(X45,X45,X45,X45,X46,X48,X47) = k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48))) )),
% 35.74/4.91    inference(superposition,[],[f860,f2046])).
% 35.74/4.91  fof(f21926,plain,(
% 35.74/4.91    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 35.74/4.91    inference(superposition,[],[f1770,f25])).
% 35.74/4.91  fof(f41424,plain,(
% 35.74/4.91    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3))),
% 35.74/4.91    inference(superposition,[],[f24,f37840])).
% 35.74/4.91  fof(f37840,plain,(
% 35.74/4.91    ( ! [X158,X159,X157,X160] : (k2_enumset1(X158,X160,X159,X157) = k2_enumset1(X158,X157,X160,X159)) )),
% 35.74/4.91    inference(superposition,[],[f33142,f28903])).
% 35.74/4.91  fof(f28903,plain,(
% 35.74/4.91    ( ! [X99,X97,X100,X98] : (k2_enumset1(X97,X100,X99,X98) = k2_enumset1(X98,X97,X99,X100)) )),
% 35.74/4.91    inference(superposition,[],[f22102,f15780])).
% 35.74/4.91  fof(f15780,plain,(
% 35.74/4.91    ( ! [X78,X76,X79,X77] : (k2_enumset1(X76,X77,X78,X79) = k2_enumset1(X76,X79,X78,X77)) )),
% 35.74/4.91    inference(superposition,[],[f14698,f1234])).
% 35.74/4.91  fof(f1234,plain,(
% 35.74/4.91    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X7,X7,X6) = k2_enumset1(X4,X5,X7,X6)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1223,f986])).
% 35.74/4.91  fof(f1223,plain,(
% 35.74/4.91    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X4,X5,X7,X7,X6)) )),
% 35.74/4.91    inference(superposition,[],[f1186,f965])).
% 35.74/4.91  fof(f14698,plain,(
% 35.74/4.91    ( ! [X47,X50,X48,X49] : (k3_enumset1(X47,X48,X49,X49,X50) = k2_enumset1(X47,X50,X49,X48)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f14611,f3625])).
% 35.74/4.91  fof(f3625,plain,(
% 35.74/4.91    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k3_enumset1(X8,X10,X9,X10,X11)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f3606,f1234])).
% 35.74/4.91  fof(f3606,plain,(
% 35.74/4.91    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X9,X10,X10,X11) = k3_enumset1(X8,X10,X9,X10,X11)) )),
% 35.74/4.91    inference(superposition,[],[f1771,f1187])).
% 35.74/4.91  fof(f1187,plain,(
% 35.74/4.91    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X9,X9,X8) = k3_enumset1(X5,X6,X7,X9,X8)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1180,f965])).
% 35.74/4.91  fof(f1180,plain,(
% 35.74/4.91    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X8,X9,X9) = k4_enumset1(X5,X6,X7,X9,X9,X8)) )),
% 35.74/4.91    inference(superposition,[],[f988,f961])).
% 35.74/4.91  fof(f1771,plain,(
% 35.74/4.91    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X7,X8,X9) = k3_enumset1(X5,X7,X6,X8,X9)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1743,f1770])).
% 35.74/4.91  fof(f1743,plain,(
% 35.74/4.91    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X7,X8,X9) = k2_xboole_0(k1_enumset1(X5,X7,X6),k2_tarski(X8,X9))) )),
% 35.74/4.91    inference(superposition,[],[f635,f1005])).
% 35.74/4.91  fof(f14611,plain,(
% 35.74/4.91    ( ! [X47,X50,X48,X49] : (k3_enumset1(X47,X48,X49,X49,X50) = k3_enumset1(X47,X49,X50,X49,X48)) )),
% 35.74/4.91    inference(superposition,[],[f1808,f965])).
% 35.74/4.91  fof(f1808,plain,(
% 35.74/4.91    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X10,X11,X12,X13,X14,X12) = k3_enumset1(X10,X12,X13,X14,X11)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1801,f1773])).
% 35.74/4.91  fof(f1773,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) = k3_enumset1(X1,X2,X3,X0,X4)) )),
% 35.74/4.91    inference(forward_demodulation,[],[f1754,f965])).
% 35.74/4.91  fof(f1754,plain,(
% 35.74/4.91    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) )),
% 35.74/4.91    inference(superposition,[],[f635,f25])).
% 35.74/4.91  fof(f1801,plain,(
% 35.74/4.91    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X10,X11,X12,X13,X14,X12) = k2_xboole_0(k2_enumset1(X10,X12,X13,X11),k1_tarski(X14))) )),
% 35.74/4.91    inference(superposition,[],[f959,f1233])).
% 35.74/4.91  fof(f24,plain,(
% 35.74/4.91    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 35.74/4.91    inference(cnf_transformation,[],[f23])).
% 35.74/4.91  fof(f23,plain,(
% 35.74/4.91    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 35.74/4.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).
% 35.74/4.91  fof(f22,plain,(
% 35.74/4.91    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 35.74/4.91    introduced(choice_axiom,[])).
% 35.74/4.91  fof(f21,plain,(
% 35.74/4.91    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 35.74/4.91    inference(ennf_transformation,[],[f20])).
% 35.74/4.91  fof(f20,negated_conjecture,(
% 35.74/4.91    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 35.74/4.91    inference(negated_conjecture,[],[f19])).
% 35.74/4.91  fof(f19,conjecture,(
% 35.74/4.91    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 35.74/4.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 35.74/4.91  % SZS output end Proof for theBenchmark
% 35.74/4.91  % (507)------------------------------
% 35.74/4.91  % (507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.74/4.91  % (507)Termination reason: Refutation
% 35.74/4.91  
% 35.74/4.91  % (507)Memory used [KB]: 82898
% 35.74/4.91  % (507)Time elapsed: 4.496 s
% 35.74/4.91  % (507)------------------------------
% 35.74/4.91  % (507)------------------------------
% 36.35/4.92  % (503)Success in time 4.56 s
%------------------------------------------------------------------------------
