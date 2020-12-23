%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:41 EST 2020

% Result     : Theorem 5.02s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 349 expanded)
%              Number of leaves         :   20 ( 111 expanded)
%              Depth                    :   25
%              Number of atoms          :  159 ( 498 expanded)
%              Number of equality atoms :  105 ( 355 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4686,plain,(
    $false ),
    inference(global_subsumption,[],[f108,f4685])).

fof(f4685,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f4507,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4507,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f74,f4445])).

fof(f4445,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f3794,f4036,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4036,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f4035,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f4035,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(global_subsumption,[],[f3443,f4006])).

fof(f4006,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f3864,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f3864,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f3847,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f75,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_xboole_0)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f58,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f3847,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(global_subsumption,[],[f27,f3833])).

fof(f3833,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f3794,f1282])).

fof(f1282,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X4,X3) = X4
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f1261,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1261,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,X9) = X9
      | ~ r1_tarski(X8,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f1219,f63])).

fof(f63,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f31,f30])).

fof(f1219,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X9)) = X9
      | ~ r1_tarski(X8,k1_xboole_0) ) ),
    inference(superposition,[],[f214,f28])).

fof(f214,plain,(
    ! [X12,X10,X11] :
      ( k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X10,X11),X12)) = X12
      | ~ r1_tarski(X10,X11) ) ),
    inference(forward_demodulation,[],[f199,f63])).

fof(f199,plain,(
    ! [X12,X10,X11] :
      ( k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X10,X11),X12)) = k5_xboole_0(k1_xboole_0,X12)
      | ~ r1_tarski(X10,X11) ) ),
    inference(superposition,[],[f44,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f27,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f3443,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f25,f3441])).

fof(f3441,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f3419])).

fof(f3419,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f58,f3280])).

fof(f3280,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f3279])).

fof(f3279,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f38,f3254])).

fof(f3254,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ r1_tarski(sK0,sK2) ),
    inference(forward_demodulation,[],[f3208,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f3208,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f420,f67])).

fof(f67,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f26,f37])).

fof(f26,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f420,plain,(
    ! [X6,X4,X5,X3] :
      ( k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f419,f349])).

fof(f349,plain,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f338,f321])).

fof(f321,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f213,f31])).

fof(f213,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f195,f63])).

fof(f195,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f44,f29])).

fof(f338,plain,(
    ! [X0] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f57,f28])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f55,f36])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f419,plain,(
    ! [X6,X4,X5,X3] :
      ( k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6)))))
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f418,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f418,plain,(
    ! [X6,X4,X5,X3] :
      ( k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6)))))
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f394,f29])).

fof(f394,plain,(
    ! [X6,X4,X5,X3] :
      ( k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6)))))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f60,f37])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3))))) ),
    inference(definition_unfolding,[],[f46,f36,f55,f36,f36])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(f25,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f3794,plain,(
    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(forward_demodulation,[],[f3793,f28])).

fof(f3793,plain,(
    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3709,f29])).

fof(f3709,plain,(
    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f413,f67])).

fof(f413,plain,(
    ! [X6,X4,X7,X5] : k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))) ),
    inference(superposition,[],[f56,f60])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f74,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f37,f28])).

fof(f108,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f106,f29])).

fof(f106,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f63,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:20:19 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.20/0.47  % (24233)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (24239)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (24257)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (24232)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (24249)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (24255)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (24237)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (24254)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (24243)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (24236)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (24246)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (24242)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (24241)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (24244)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24254)Refutation not found, incomplete strategy% (24254)------------------------------
% 0.20/0.52  % (24254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24254)Memory used [KB]: 10746
% 0.20/0.52  % (24254)Time elapsed: 0.078 s
% 0.20/0.52  % (24254)------------------------------
% 0.20/0.52  % (24254)------------------------------
% 0.20/0.52  % (24238)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (24252)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (24249)Refutation not found, incomplete strategy% (24249)------------------------------
% 0.20/0.52  % (24249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24249)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24249)Memory used [KB]: 10618
% 0.20/0.52  % (24249)Time elapsed: 0.128 s
% 0.20/0.52  % (24249)------------------------------
% 0.20/0.52  % (24249)------------------------------
% 0.20/0.53  % (24256)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (24261)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (24259)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (24234)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (24248)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (24235)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (24240)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (24250)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (24253)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (24245)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (24260)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (24247)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (24258)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (24251)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.18/0.65  % (24263)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.75/0.71  % (24264)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.21/0.81  % (24237)Time limit reached!
% 3.21/0.81  % (24237)------------------------------
% 3.21/0.81  % (24237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.81  % (24237)Termination reason: Time limit
% 3.21/0.81  
% 3.21/0.81  % (24237)Memory used [KB]: 10234
% 3.21/0.81  % (24237)Time elapsed: 0.407 s
% 3.21/0.81  % (24237)------------------------------
% 3.21/0.81  % (24237)------------------------------
% 4.12/0.90  % (24242)Time limit reached!
% 4.12/0.90  % (24242)------------------------------
% 4.12/0.90  % (24242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.90  % (24242)Termination reason: Time limit
% 4.12/0.90  % (24242)Termination phase: Saturation
% 4.12/0.90  
% 4.12/0.90  % (24242)Memory used [KB]: 15223
% 4.12/0.90  % (24242)Time elapsed: 0.500 s
% 4.12/0.90  % (24242)------------------------------
% 4.12/0.90  % (24242)------------------------------
% 4.12/0.91  % (24265)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.12/0.91  % (24233)Time limit reached!
% 4.12/0.91  % (24233)------------------------------
% 4.12/0.91  % (24233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.91  % (24233)Termination reason: Time limit
% 4.12/0.91  
% 4.12/0.91  % (24233)Memory used [KB]: 8955
% 4.12/0.91  % (24233)Time elapsed: 0.519 s
% 4.12/0.91  % (24233)------------------------------
% 4.12/0.91  % (24233)------------------------------
% 4.12/0.92  % (24232)Time limit reached!
% 4.12/0.92  % (24232)------------------------------
% 4.12/0.92  % (24232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.92  % (24232)Termination reason: Time limit
% 4.12/0.92  
% 4.12/0.92  % (24232)Memory used [KB]: 4861
% 4.12/0.92  % (24232)Time elapsed: 0.516 s
% 4.12/0.92  % (24232)------------------------------
% 4.12/0.92  % (24232)------------------------------
% 4.54/0.95  % (24244)Time limit reached!
% 4.54/0.95  % (24244)------------------------------
% 4.54/0.95  % (24244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.97  % (24244)Termination reason: Time limit
% 4.54/0.97  
% 4.54/0.97  % (24244)Memory used [KB]: 14200
% 4.54/0.97  % (24244)Time elapsed: 0.528 s
% 4.54/0.97  % (24244)------------------------------
% 4.54/0.97  % (24244)------------------------------
% 4.54/1.00  % (24248)Time limit reached!
% 4.54/1.00  % (24248)------------------------------
% 4.54/1.00  % (24248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.00  % (24248)Termination reason: Time limit
% 4.54/1.00  % (24248)Termination phase: Saturation
% 4.54/1.00  
% 4.54/1.00  % (24248)Memory used [KB]: 16630
% 4.54/1.00  % (24248)Time elapsed: 0.600 s
% 4.54/1.00  % (24248)------------------------------
% 4.54/1.00  % (24248)------------------------------
% 5.02/1.01  % (24256)Refutation found. Thanks to Tanya!
% 5.02/1.01  % SZS status Theorem for theBenchmark
% 5.02/1.01  % (24239)Time limit reached!
% 5.02/1.01  % (24239)------------------------------
% 5.02/1.01  % (24239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.01  % (24239)Termination reason: Time limit
% 5.02/1.01  
% 5.02/1.01  % (24239)Memory used [KB]: 11641
% 5.02/1.01  % (24239)Time elapsed: 0.605 s
% 5.02/1.01  % (24239)------------------------------
% 5.02/1.01  % (24239)------------------------------
% 5.02/1.02  % SZS output start Proof for theBenchmark
% 5.02/1.02  fof(f4686,plain,(
% 5.02/1.02    $false),
% 5.02/1.02    inference(global_subsumption,[],[f108,f4685])).
% 5.02/1.02  fof(f4685,plain,(
% 5.02/1.02    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 5.02/1.02    inference(forward_demodulation,[],[f4507,f61])).
% 5.02/1.02  fof(f61,plain,(
% 5.02/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 5.02/1.02    inference(equality_resolution,[],[f40])).
% 5.02/1.02  fof(f40,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f18])).
% 5.02/1.02  fof(f18,axiom,(
% 5.02/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.02/1.02  fof(f4507,plain,(
% 5.02/1.02    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),k1_xboole_0)),
% 5.02/1.02    inference(backward_demodulation,[],[f74,f4445])).
% 5.02/1.02  fof(f4445,plain,(
% 5.02/1.02    k1_xboole_0 = sK1),
% 5.02/1.02    inference(unit_resulting_resolution,[],[f3794,f4036,f38])).
% 5.02/1.02  fof(f38,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 5.02/1.02    inference(cnf_transformation,[],[f18])).
% 5.02/1.02  fof(f4036,plain,(
% 5.02/1.02    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 5.02/1.02    inference(unit_resulting_resolution,[],[f4035,f58])).
% 5.02/1.02  fof(f58,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f42,f36])).
% 5.02/1.02  fof(f36,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.02/1.02    inference(cnf_transformation,[],[f3])).
% 5.02/1.02  fof(f3,axiom,(
% 5.02/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.02/1.02  fof(f42,plain,(
% 5.02/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 5.02/1.02    inference(cnf_transformation,[],[f2])).
% 5.02/1.02  fof(f2,axiom,(
% 5.02/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.02/1.02  fof(f4035,plain,(
% 5.02/1.02    ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(global_subsumption,[],[f3443,f4006])).
% 5.02/1.02  fof(f4006,plain,(
% 5.02/1.02    k1_xboole_0 != sK0 | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(superposition,[],[f3864,f37])).
% 5.02/1.02  fof(f37,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f24])).
% 5.02/1.02  fof(f24,plain,(
% 5.02/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.02/1.02    inference(ennf_transformation,[],[f5])).
% 5.02/1.02  fof(f5,axiom,(
% 5.02/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.02/1.02  fof(f3864,plain,(
% 5.02/1.02    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 5.02/1.02    inference(unit_resulting_resolution,[],[f3847,f79])).
% 5.02/1.02  fof(f79,plain,(
% 5.02/1.02    ( ! [X0] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)) )),
% 5.02/1.02    inference(forward_demodulation,[],[f75,f30])).
% 5.02/1.02  fof(f30,plain,(
% 5.02/1.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.02/1.02    inference(cnf_transformation,[],[f7])).
% 5.02/1.02  fof(f7,axiom,(
% 5.02/1.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.02/1.02  fof(f75,plain,(
% 5.02/1.02    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,k1_xboole_0) | r1_tarski(X0,k1_xboole_0)) )),
% 5.02/1.02    inference(superposition,[],[f58,f28])).
% 5.02/1.02  fof(f28,plain,(
% 5.02/1.02    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f6])).
% 5.02/1.02  fof(f6,axiom,(
% 5.02/1.02    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 5.02/1.02  fof(f3847,plain,(
% 5.02/1.02    ~r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)),
% 5.02/1.02    inference(global_subsumption,[],[f27,f3833])).
% 5.02/1.02  fof(f3833,plain,(
% 5.02/1.02    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)),
% 5.02/1.02    inference(superposition,[],[f3794,f1282])).
% 5.02/1.02  fof(f1282,plain,(
% 5.02/1.02    ( ! [X4,X3] : (k5_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,k1_xboole_0)) )),
% 5.02/1.02    inference(superposition,[],[f1261,f31])).
% 5.02/1.02  fof(f31,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f1])).
% 5.02/1.02  fof(f1,axiom,(
% 5.02/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.02/1.02  fof(f1261,plain,(
% 5.02/1.02    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = X9 | ~r1_tarski(X8,k1_xboole_0)) )),
% 5.02/1.02    inference(forward_demodulation,[],[f1219,f63])).
% 5.02/1.02  fof(f63,plain,(
% 5.02/1.02    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.02/1.02    inference(superposition,[],[f31,f30])).
% 5.02/1.02  fof(f1219,plain,(
% 5.02/1.02    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X9)) = X9 | ~r1_tarski(X8,k1_xboole_0)) )),
% 5.02/1.02    inference(superposition,[],[f214,f28])).
% 5.02/1.02  fof(f214,plain,(
% 5.02/1.02    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X10,X11),X12)) = X12 | ~r1_tarski(X10,X11)) )),
% 5.02/1.02    inference(forward_demodulation,[],[f199,f63])).
% 5.02/1.02  fof(f199,plain,(
% 5.02/1.02    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X10,X11),X12)) = k5_xboole_0(k1_xboole_0,X12) | ~r1_tarski(X10,X11)) )),
% 5.02/1.02    inference(superposition,[],[f44,f59])).
% 5.02/1.02  fof(f59,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f41,f36])).
% 5.02/1.02  fof(f41,plain,(
% 5.02/1.02    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 5.02/1.02    inference(cnf_transformation,[],[f2])).
% 5.02/1.02  fof(f44,plain,(
% 5.02/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.02/1.02    inference(cnf_transformation,[],[f8])).
% 5.02/1.02  fof(f8,axiom,(
% 5.02/1.02    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.02/1.02  fof(f27,plain,(
% 5.02/1.02    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 5.02/1.02    inference(cnf_transformation,[],[f23])).
% 5.02/1.02  fof(f23,plain,(
% 5.02/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 5.02/1.02    inference(flattening,[],[f22])).
% 5.02/1.02  fof(f22,plain,(
% 5.02/1.02    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 5.02/1.02    inference(ennf_transformation,[],[f21])).
% 5.02/1.02  fof(f21,negated_conjecture,(
% 5.02/1.02    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 5.02/1.02    inference(negated_conjecture,[],[f20])).
% 5.02/1.02  fof(f20,conjecture,(
% 5.02/1.02    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 5.02/1.02  fof(f3443,plain,(
% 5.02/1.02    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 5.02/1.02    inference(global_subsumption,[],[f25,f3441])).
% 5.02/1.02  fof(f3441,plain,(
% 5.02/1.02    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(trivial_inequality_removal,[],[f3419])).
% 5.02/1.02  fof(f3419,plain,(
% 5.02/1.02    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(superposition,[],[f58,f3280])).
% 5.02/1.02  fof(f3280,plain,(
% 5.02/1.02    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(trivial_inequality_removal,[],[f3279])).
% 5.02/1.02  fof(f3279,plain,(
% 5.02/1.02    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(superposition,[],[f38,f3254])).
% 5.02/1.02  fof(f3254,plain,(
% 5.02/1.02    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(forward_demodulation,[],[f3208,f29])).
% 5.02/1.02  fof(f29,plain,(
% 5.02/1.02    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f9])).
% 5.02/1.02  fof(f9,axiom,(
% 5.02/1.02    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.02/1.02  fof(f3208,plain,(
% 5.02/1.02    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(superposition,[],[f420,f67])).
% 5.02/1.02  fof(f67,plain,(
% 5.02/1.02    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 5.02/1.02    inference(unit_resulting_resolution,[],[f26,f37])).
% 5.02/1.02  fof(f26,plain,(
% 5.02/1.02    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 5.02/1.02    inference(cnf_transformation,[],[f23])).
% 5.02/1.02  fof(f420,plain,(
% 5.02/1.02    ( ! [X6,X4,X5,X3] : (k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6))) | ~r1_tarski(X3,X4)) )),
% 5.02/1.02    inference(forward_demodulation,[],[f419,f349])).
% 5.02/1.02  fof(f349,plain,(
% 5.02/1.02    ( ! [X0] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 5.02/1.02    inference(forward_demodulation,[],[f338,f321])).
% 5.02/1.02  fof(f321,plain,(
% 5.02/1.02    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 5.02/1.02    inference(superposition,[],[f213,f31])).
% 5.02/1.02  fof(f213,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.02/1.02    inference(forward_demodulation,[],[f195,f63])).
% 5.02/1.02  fof(f195,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.02/1.02    inference(superposition,[],[f44,f29])).
% 5.02/1.02  fof(f338,plain,(
% 5.02/1.02    ( ! [X0] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 5.02/1.02    inference(superposition,[],[f57,f28])).
% 5.02/1.02  fof(f57,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 5.02/1.02    inference(definition_unfolding,[],[f35,f55,f36])).
% 5.02/1.02  fof(f55,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 5.02/1.02    inference(definition_unfolding,[],[f33,f54])).
% 5.02/1.02  fof(f54,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f34,f53])).
% 5.02/1.02  fof(f53,plain,(
% 5.02/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f43,f52])).
% 5.02/1.02  fof(f52,plain,(
% 5.02/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f45,f51])).
% 5.02/1.02  fof(f51,plain,(
% 5.02/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f47,f50])).
% 5.02/1.02  fof(f50,plain,(
% 5.02/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 5.02/1.02    inference(definition_unfolding,[],[f48,f49])).
% 5.02/1.02  fof(f49,plain,(
% 5.02/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f16])).
% 5.02/1.02  fof(f16,axiom,(
% 5.02/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 5.02/1.02  fof(f48,plain,(
% 5.02/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f15])).
% 5.02/1.02  fof(f15,axiom,(
% 5.02/1.02    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 5.02/1.02  fof(f47,plain,(
% 5.02/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f14])).
% 5.02/1.02  fof(f14,axiom,(
% 5.02/1.02    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 5.02/1.02  fof(f45,plain,(
% 5.02/1.02    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f13])).
% 5.02/1.02  fof(f13,axiom,(
% 5.02/1.02    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 5.02/1.02  fof(f43,plain,(
% 5.02/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f12])).
% 5.02/1.02  fof(f12,axiom,(
% 5.02/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 5.02/1.02  fof(f34,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f11])).
% 5.02/1.02  fof(f11,axiom,(
% 5.02/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.02/1.02  fof(f33,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 5.02/1.02    inference(cnf_transformation,[],[f17])).
% 5.02/1.02  fof(f17,axiom,(
% 5.02/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.02/1.02  fof(f35,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.02/1.02    inference(cnf_transformation,[],[f10])).
% 5.02/1.02  fof(f10,axiom,(
% 5.02/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.02/1.02  fof(f419,plain,(
% 5.02/1.02    ( ! [X6,X4,X5,X3] : (k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6))))) | ~r1_tarski(X3,X4)) )),
% 5.02/1.02    inference(forward_demodulation,[],[f418,f62])).
% 5.02/1.02  fof(f62,plain,(
% 5.02/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 5.02/1.02    inference(equality_resolution,[],[f39])).
% 5.02/1.02  fof(f39,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.02/1.02    inference(cnf_transformation,[],[f18])).
% 5.02/1.02  fof(f418,plain,(
% 5.02/1.02    ( ! [X6,X4,X5,X3] : (k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(k1_xboole_0,X5),k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6))))) | ~r1_tarski(X3,X4)) )),
% 5.02/1.02    inference(forward_demodulation,[],[f394,f29])).
% 5.02/1.02  fof(f394,plain,(
% 5.02/1.02    ( ! [X6,X4,X5,X3] : (k5_xboole_0(k2_zfmisc_1(X3,X5),k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(k5_xboole_0(X3,X3),X5),k2_zfmisc_1(X3,k5_xboole_0(X5,k3_xboole_0(X5,X6))))) | ~r1_tarski(X3,X4)) )),
% 5.02/1.02    inference(superposition,[],[f60,f37])).
% 5.02/1.02  fof(f60,plain,(
% 5.02/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1),k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))))) )),
% 5.02/1.02    inference(definition_unfolding,[],[f46,f36,f55,f36,f36])).
% 5.02/1.02  fof(f46,plain,(
% 5.02/1.02    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 5.02/1.02    inference(cnf_transformation,[],[f19])).
% 5.02/1.02  fof(f19,axiom,(
% 5.02/1.02    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).
% 5.02/1.02  fof(f25,plain,(
% 5.02/1.02    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 5.02/1.02    inference(cnf_transformation,[],[f23])).
% 5.02/1.02  fof(f3794,plain,(
% 5.02/1.02    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 5.02/1.02    inference(forward_demodulation,[],[f3793,f28])).
% 5.02/1.02  fof(f3793,plain,(
% 5.02/1.02    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k1_xboole_0)),
% 5.02/1.02    inference(forward_demodulation,[],[f3709,f29])).
% 5.02/1.02  fof(f3709,plain,(
% 5.02/1.02    k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1),k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))),
% 5.02/1.02    inference(superposition,[],[f413,f67])).
% 5.02/1.02  fof(f413,plain,(
% 5.02/1.02    ( ! [X6,X4,X7,X5] : (k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6) = k3_xboole_0(k2_zfmisc_1(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6),k5_xboole_0(k2_zfmisc_1(X4,X6),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))))) )),
% 5.02/1.02    inference(superposition,[],[f56,f60])).
% 5.02/1.02  fof(f56,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 5.02/1.02    inference(definition_unfolding,[],[f32,f55])).
% 5.02/1.02  fof(f32,plain,(
% 5.02/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.02/1.02    inference(cnf_transformation,[],[f4])).
% 5.02/1.02  fof(f4,axiom,(
% 5.02/1.02    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 5.02/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 5.02/1.02  fof(f74,plain,(
% 5.02/1.02    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)),
% 5.02/1.02    inference(unit_resulting_resolution,[],[f27,f68])).
% 5.02/1.02  fof(f68,plain,(
% 5.02/1.02    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 5.02/1.02    inference(superposition,[],[f37,f28])).
% 5.02/1.02  fof(f108,plain,(
% 5.02/1.02    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 5.02/1.02    inference(forward_demodulation,[],[f106,f29])).
% 5.02/1.02  fof(f106,plain,(
% 5.02/1.02    r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 5.02/1.02    inference(unit_resulting_resolution,[],[f63,f79])).
% 5.02/1.02  % SZS output end Proof for theBenchmark
% 5.02/1.02  % (24256)------------------------------
% 5.02/1.02  % (24256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.02  % (24256)Termination reason: Refutation
% 5.02/1.02  
% 5.02/1.02  % (24256)Memory used [KB]: 11769
% 5.02/1.02  % (24256)Time elapsed: 0.569 s
% 5.02/1.02  % (24256)------------------------------
% 5.02/1.02  % (24256)------------------------------
% 5.02/1.02  % (24231)Success in time 0.669 s
%------------------------------------------------------------------------------
