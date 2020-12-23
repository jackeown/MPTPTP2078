%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:13 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  111 (3962 expanded)
%              Number of leaves         :   18 (1272 expanded)
%              Depth                    :   35
%              Number of atoms          :  207 (5144 expanded)
%              Number of equality atoms :  106 (4437 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1295,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f1295,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f1292,f233])).

fof(f233,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f201,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f201,plain,(
    r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f98,f133])).

fof(f133,plain,(
    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f125,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f125,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f122,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f76,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f122,plain,(
    r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f102,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(superposition,[],[f91,f77])).

fof(f77,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f29,f76,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f74])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f98,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1292,plain,(
    sK1 = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f1282,f1193])).

fof(f1193,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | sK1 = k3_xboole_0(X11,sK2) ) ),
    inference(subsumption_resolution,[],[f1162,f603])).

fof(f603,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f602,f30])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f602,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f578,f137])).

fof(f137,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f103,f133])).

fof(f103,plain,(
    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f79,f77])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f37,f75])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f578,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK2 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f450,f441])).

fof(f441,plain,(
    ! [X1] :
      ( sK0 = sK6(sK1,X1,sK2)
      | sK2 = k3_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f435,f198])).

fof(f198,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,sK2)
      | sK0 = X7 ) ),
    inference(superposition,[],[f94,f133])).

fof(f94,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f435,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK1,X0,sK2),sK2)
      | sK2 = k3_xboole_0(sK1,X0) ) ),
    inference(factoring,[],[f180])).

fof(f180,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK6(sK1,X12,X13),sK2)
      | r2_hidden(sK6(sK1,X12,X13),X13)
      | k3_xboole_0(sK1,X12) = X13 ) ),
    inference(resolution,[],[f136,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f136,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK2) ) ),
    inference(backward_demodulation,[],[f120,f133])).

fof(f120,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(superposition,[],[f100,f103])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f450,plain,(
    ~ r2_hidden(sK6(sK1,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f449,f30])).

fof(f449,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK6(sK1,sK2,sK2),sK1) ),
    inference(forward_demodulation,[],[f448,f137])).

fof(f448,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK2),sK1) ),
    inference(subsumption_resolution,[],[f447,f435])).

fof(f447,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK2),sK1)
    | ~ r2_hidden(sK6(sK1,sK2,sK2),sK2) ),
    inference(duplicate_literal_removal,[],[f439])).

fof(f439,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ r2_hidden(sK6(sK1,sK2,sK2),sK1)
    | ~ r2_hidden(sK6(sK1,sK2,sK2),sK2)
    | sK2 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f435,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1162,plain,(
    ! [X11] :
      ( r2_hidden(sK0,sK1)
      | sK1 = k3_xboole_0(X11,sK2)
      | ~ v1_xboole_0(X11) ) ),
    inference(resolution,[],[f565,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f565,plain,(
    ! [X8] :
      ( r2_hidden(sK0,X8)
      | r2_hidden(sK0,sK1)
      | sK1 = k3_xboole_0(X8,sK2) ) ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,(
    ! [X8] :
      ( r2_hidden(sK0,X8)
      | r2_hidden(sK0,sK1)
      | sK1 = k3_xboole_0(X8,sK2)
      | sK1 = k3_xboole_0(X8,sK2) ) ),
    inference(superposition,[],[f61,f406])).

fof(f406,plain,(
    ! [X1] :
      ( sK0 = sK6(X1,sK2,sK1)
      | sK1 = k3_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f360,f198])).

fof(f360,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,sK2,sK1),sK2)
      | sK1 = k3_xboole_0(X0,sK2) ) ),
    inference(factoring,[],[f179])).

fof(f179,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK6(X10,X11,sK1),sK2)
      | r2_hidden(sK6(X10,X11,sK1),X11)
      | sK1 = k3_xboole_0(X10,X11) ) ),
    inference(resolution,[],[f136,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1282,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1281,f32])).

fof(f1281,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1277,f201])).

fof(f1277,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1268,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1268,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f1206,f197])).

fof(f197,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK0,X6)
      | r1_tarski(sK2,X6) ) ),
    inference(superposition,[],[f90,f133])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f56,f76])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1206,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f34,f1203])).

fof(f1203,plain,(
    sK0 = sK3(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1202,f31])).

fof(f1202,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK3(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1201,f233])).

fof(f1201,plain,
    ( sK1 = k3_xboole_0(k1_xboole_0,sK2)
    | sK0 = sK3(k1_xboole_0) ),
    inference(resolution,[],[f1193,f324])).

fof(f324,plain,
    ( v1_xboole_0(k1_xboole_0)
    | sK0 = sK3(k1_xboole_0) ),
    inference(resolution,[],[f315,f198])).

fof(f315,plain,
    ( r2_hidden(sK3(k1_xboole_0),sK2)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f247,f34])).

fof(f247,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,sK2) ) ),
    inference(superposition,[],[f100,f233])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (17849)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.48  % (17857)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (17843)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (17847)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.55  % (17851)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (17855)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (17859)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.57  % (17868)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.57  % (17865)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.57  % (17856)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.58  % (17842)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.58  % (17866)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.71/0.58  % (17848)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.58  % (17872)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.71/0.59  % (17844)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.71/0.59  % (17872)Refutation not found, incomplete strategy% (17872)------------------------------
% 1.71/0.59  % (17872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (17872)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (17872)Memory used [KB]: 1663
% 1.71/0.59  % (17872)Time elapsed: 0.149 s
% 1.71/0.59  % (17872)------------------------------
% 1.71/0.59  % (17872)------------------------------
% 1.71/0.59  % (17858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.84/0.60  % (17850)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.84/0.60  % (17846)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.84/0.61  % (17867)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.84/0.61  % (17852)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.84/0.61  % (17860)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.84/0.61  % (17858)Refutation not found, incomplete strategy% (17858)------------------------------
% 1.84/0.61  % (17858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (17858)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (17858)Memory used [KB]: 10618
% 1.84/0.61  % (17858)Time elapsed: 0.182 s
% 1.84/0.61  % (17858)------------------------------
% 1.84/0.61  % (17858)------------------------------
% 1.84/0.61  % (17859)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.61  % SZS output start Proof for theBenchmark
% 1.84/0.61  fof(f1296,plain,(
% 1.84/0.61    $false),
% 1.84/0.61    inference(subsumption_resolution,[],[f1295,f31])).
% 1.84/0.61  fof(f31,plain,(
% 1.84/0.61    k1_xboole_0 != sK1),
% 1.84/0.61    inference(cnf_transformation,[],[f25])).
% 1.84/0.61  fof(f25,plain,(
% 1.84/0.61    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.84/0.61    inference(ennf_transformation,[],[f23])).
% 1.84/0.61  fof(f23,negated_conjecture,(
% 1.84/0.61    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.84/0.61    inference(negated_conjecture,[],[f22])).
% 1.84/0.61  fof(f22,conjecture,(
% 1.84/0.61    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.84/0.61  fof(f1295,plain,(
% 1.84/0.61    k1_xboole_0 = sK1),
% 1.84/0.61    inference(forward_demodulation,[],[f1292,f233])).
% 1.84/0.61  fof(f233,plain,(
% 1.84/0.61    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 1.84/0.61    inference(resolution,[],[f201,f43])).
% 1.84/0.61  fof(f43,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f27])).
% 1.84/0.61  fof(f27,plain,(
% 1.84/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f8])).
% 1.84/0.61  fof(f8,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.84/0.61  fof(f201,plain,(
% 1.84/0.61    r1_tarski(k1_xboole_0,sK2)),
% 1.84/0.61    inference(superposition,[],[f98,f133])).
% 1.84/0.61  fof(f133,plain,(
% 1.84/0.61    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.84/0.61    inference(subsumption_resolution,[],[f125,f32])).
% 1.84/0.61  fof(f32,plain,(
% 1.84/0.61    k1_xboole_0 != sK2),
% 1.84/0.61    inference(cnf_transformation,[],[f25])).
% 1.84/0.61  fof(f125,plain,(
% 1.84/0.61    k1_xboole_0 = sK2 | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.84/0.61    inference(resolution,[],[f122,f88])).
% 1.84/0.61  fof(f88,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f53,f76,f76])).
% 1.84/0.61  fof(f76,plain,(
% 1.84/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f33,f74])).
% 1.84/0.61  fof(f74,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f39,f73])).
% 1.84/0.61  fof(f73,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f58,f72])).
% 1.84/0.61  fof(f72,plain,(
% 1.84/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f66,f71])).
% 1.84/0.61  fof(f71,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f67,f70])).
% 1.84/0.61  fof(f70,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f68,f69])).
% 1.84/0.61  fof(f69,plain,(
% 1.84/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f18])).
% 1.84/0.61  fof(f18,axiom,(
% 1.84/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.84/0.61  fof(f68,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f17])).
% 1.84/0.61  fof(f17,axiom,(
% 1.84/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.84/0.61  fof(f67,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f16])).
% 1.84/0.61  fof(f16,axiom,(
% 1.84/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.84/0.61  fof(f66,plain,(
% 1.84/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f15])).
% 1.84/0.61  fof(f15,axiom,(
% 1.84/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.84/0.61  fof(f58,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f14])).
% 1.84/0.61  fof(f14,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.84/0.61  fof(f39,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f13])).
% 1.84/0.61  fof(f13,axiom,(
% 1.84/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.84/0.61  fof(f33,plain,(
% 1.84/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f12])).
% 1.84/0.61  fof(f12,axiom,(
% 1.84/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.84/0.61  fof(f53,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f20])).
% 1.84/0.61  fof(f20,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.84/0.61  fof(f122,plain,(
% 1.84/0.61    r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.84/0.61    inference(resolution,[],[f102,f93])).
% 1.84/0.61  fof(f93,plain,(
% 1.84/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.61    inference(equality_resolution,[],[f44])).
% 1.84/0.61  fof(f44,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.84/0.61    inference(cnf_transformation,[],[f4])).
% 1.84/0.61  fof(f4,axiom,(
% 1.84/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.61  fof(f102,plain,(
% 1.84/0.61    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 1.84/0.61    inference(superposition,[],[f91,f77])).
% 1.84/0.61  fof(f77,plain,(
% 1.84/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.84/0.61    inference(definition_unfolding,[],[f29,f76,f75])).
% 1.84/0.61  fof(f75,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f38,f74])).
% 1.84/0.61  fof(f38,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f21])).
% 1.84/0.61  fof(f21,axiom,(
% 1.84/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.84/0.61  fof(f29,plain,(
% 1.84/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.84/0.61    inference(cnf_transformation,[],[f25])).
% 1.84/0.61  fof(f91,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f59,f75])).
% 1.84/0.61  fof(f59,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  fof(f28,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f6])).
% 1.84/0.61  fof(f6,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.84/0.61  fof(f98,plain,(
% 1.84/0.61    ( ! [X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.84/0.61    inference(equality_resolution,[],[f87])).
% 1.84/0.61  fof(f87,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.84/0.61    inference(definition_unfolding,[],[f54,f76])).
% 1.84/0.61  fof(f54,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f20])).
% 1.84/0.61  fof(f1292,plain,(
% 1.84/0.61    sK1 = k3_xboole_0(k1_xboole_0,sK2)),
% 1.84/0.61    inference(resolution,[],[f1282,f1193])).
% 1.84/0.61  fof(f1193,plain,(
% 1.84/0.61    ( ! [X11] : (~v1_xboole_0(X11) | sK1 = k3_xboole_0(X11,sK2)) )),
% 1.84/0.61    inference(subsumption_resolution,[],[f1162,f603])).
% 1.84/0.61  fof(f603,plain,(
% 1.84/0.61    ~r2_hidden(sK0,sK1)),
% 1.84/0.61    inference(subsumption_resolution,[],[f602,f30])).
% 1.84/0.61  fof(f30,plain,(
% 1.84/0.61    sK1 != sK2),
% 1.84/0.61    inference(cnf_transformation,[],[f25])).
% 1.84/0.61  fof(f602,plain,(
% 1.84/0.61    sK1 = sK2 | ~r2_hidden(sK0,sK1)),
% 1.84/0.61    inference(forward_demodulation,[],[f578,f137])).
% 1.84/0.61  fof(f137,plain,(
% 1.84/0.61    sK1 = k3_xboole_0(sK1,sK2)),
% 1.84/0.61    inference(backward_demodulation,[],[f103,f133])).
% 1.84/0.61  fof(f103,plain,(
% 1.84/0.61    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.84/0.61    inference(superposition,[],[f79,f77])).
% 1.84/0.61  fof(f79,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 1.84/0.61    inference(definition_unfolding,[],[f37,f75])).
% 1.84/0.61  fof(f37,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f7])).
% 1.84/0.61  fof(f7,axiom,(
% 1.84/0.61    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.84/0.61  fof(f578,plain,(
% 1.84/0.61    ~r2_hidden(sK0,sK1) | sK2 = k3_xboole_0(sK1,sK2)),
% 1.84/0.61    inference(superposition,[],[f450,f441])).
% 1.84/0.61  fof(f441,plain,(
% 1.84/0.61    ( ! [X1] : (sK0 = sK6(sK1,X1,sK2) | sK2 = k3_xboole_0(sK1,X1)) )),
% 1.84/0.61    inference(resolution,[],[f435,f198])).
% 1.84/0.61  fof(f198,plain,(
% 1.84/0.61    ( ! [X7] : (~r2_hidden(X7,sK2) | sK0 = X7) )),
% 1.84/0.61    inference(superposition,[],[f94,f133])).
% 1.84/0.61  fof(f94,plain,(
% 1.84/0.61    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.84/0.61    inference(equality_resolution,[],[f84])).
% 1.84/0.61  fof(f84,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.84/0.61    inference(definition_unfolding,[],[f50,f76])).
% 1.84/0.61  fof(f50,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.84/0.61    inference(cnf_transformation,[],[f11])).
% 1.84/0.61  fof(f11,axiom,(
% 1.84/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.84/0.61  fof(f435,plain,(
% 1.84/0.61    ( ! [X0] : (r2_hidden(sK6(sK1,X0,sK2),sK2) | sK2 = k3_xboole_0(sK1,X0)) )),
% 1.84/0.61    inference(factoring,[],[f180])).
% 1.84/0.61  fof(f180,plain,(
% 1.84/0.61    ( ! [X12,X13] : (r2_hidden(sK6(sK1,X12,X13),sK2) | r2_hidden(sK6(sK1,X12,X13),X13) | k3_xboole_0(sK1,X12) = X13) )),
% 1.84/0.61    inference(resolution,[],[f136,f61])).
% 1.84/0.61  fof(f61,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.84/0.61    inference(cnf_transformation,[],[f2])).
% 1.84/0.61  fof(f2,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.84/0.61  fof(f136,plain,(
% 1.84/0.61    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK2)) )),
% 1.84/0.61    inference(backward_demodulation,[],[f120,f133])).
% 1.84/0.61  fof(f120,plain,(
% 1.84/0.61    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 1.84/0.61    inference(superposition,[],[f100,f103])).
% 1.84/0.61  fof(f100,plain,(
% 1.84/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.84/0.61    inference(equality_resolution,[],[f64])).
% 1.84/0.61  fof(f64,plain,(
% 1.84/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.84/0.61    inference(cnf_transformation,[],[f2])).
% 1.84/0.61  fof(f450,plain,(
% 1.84/0.61    ~r2_hidden(sK6(sK1,sK2,sK2),sK1)),
% 1.84/0.61    inference(subsumption_resolution,[],[f449,f30])).
% 1.84/0.61  fof(f449,plain,(
% 1.84/0.61    sK1 = sK2 | ~r2_hidden(sK6(sK1,sK2,sK2),sK1)),
% 1.84/0.61    inference(forward_demodulation,[],[f448,f137])).
% 1.84/0.61  fof(f448,plain,(
% 1.84/0.61    sK2 = k3_xboole_0(sK1,sK2) | ~r2_hidden(sK6(sK1,sK2,sK2),sK1)),
% 1.84/0.61    inference(subsumption_resolution,[],[f447,f435])).
% 1.84/0.61  fof(f447,plain,(
% 1.84/0.61    sK2 = k3_xboole_0(sK1,sK2) | ~r2_hidden(sK6(sK1,sK2,sK2),sK1) | ~r2_hidden(sK6(sK1,sK2,sK2),sK2)),
% 1.84/0.61    inference(duplicate_literal_removal,[],[f439])).
% 1.84/0.61  fof(f439,plain,(
% 1.84/0.61    sK2 = k3_xboole_0(sK1,sK2) | ~r2_hidden(sK6(sK1,sK2,sK2),sK1) | ~r2_hidden(sK6(sK1,sK2,sK2),sK2) | sK2 = k3_xboole_0(sK1,sK2)),
% 1.84/0.61    inference(resolution,[],[f435,f60])).
% 1.84/0.61  fof(f60,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.84/0.61    inference(cnf_transformation,[],[f2])).
% 1.84/0.61  fof(f1162,plain,(
% 1.84/0.61    ( ! [X11] : (r2_hidden(sK0,sK1) | sK1 = k3_xboole_0(X11,sK2) | ~v1_xboole_0(X11)) )),
% 1.84/0.61    inference(resolution,[],[f565,f35])).
% 1.84/0.61  fof(f35,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f1])).
% 1.84/0.61  fof(f1,axiom,(
% 1.84/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.84/0.61  fof(f565,plain,(
% 1.84/0.61    ( ! [X8] : (r2_hidden(sK0,X8) | r2_hidden(sK0,sK1) | sK1 = k3_xboole_0(X8,sK2)) )),
% 1.84/0.61    inference(duplicate_literal_removal,[],[f552])).
% 1.84/0.61  fof(f552,plain,(
% 1.84/0.61    ( ! [X8] : (r2_hidden(sK0,X8) | r2_hidden(sK0,sK1) | sK1 = k3_xboole_0(X8,sK2) | sK1 = k3_xboole_0(X8,sK2)) )),
% 1.84/0.61    inference(superposition,[],[f61,f406])).
% 1.84/0.61  fof(f406,plain,(
% 1.84/0.61    ( ! [X1] : (sK0 = sK6(X1,sK2,sK1) | sK1 = k3_xboole_0(X1,sK2)) )),
% 1.84/0.61    inference(resolution,[],[f360,f198])).
% 1.84/0.61  fof(f360,plain,(
% 1.84/0.61    ( ! [X0] : (r2_hidden(sK6(X0,sK2,sK1),sK2) | sK1 = k3_xboole_0(X0,sK2)) )),
% 1.84/0.61    inference(factoring,[],[f179])).
% 1.84/0.61  fof(f179,plain,(
% 1.84/0.61    ( ! [X10,X11] : (r2_hidden(sK6(X10,X11,sK1),sK2) | r2_hidden(sK6(X10,X11,sK1),X11) | sK1 = k3_xboole_0(X10,X11)) )),
% 1.84/0.61    inference(resolution,[],[f136,f62])).
% 1.84/0.61  fof(f62,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.84/0.61    inference(cnf_transformation,[],[f2])).
% 1.84/0.61  fof(f1282,plain,(
% 1.84/0.61    v1_xboole_0(k1_xboole_0)),
% 1.84/0.61    inference(subsumption_resolution,[],[f1281,f32])).
% 1.84/0.61  fof(f1281,plain,(
% 1.84/0.61    v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2),
% 1.84/0.61    inference(subsumption_resolution,[],[f1277,f201])).
% 1.84/0.61  fof(f1277,plain,(
% 1.84/0.61    v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 1.84/0.61    inference(resolution,[],[f1268,f46])).
% 1.84/0.61  fof(f46,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.84/0.61    inference(cnf_transformation,[],[f4])).
% 1.84/0.61  fof(f1268,plain,(
% 1.84/0.61    r1_tarski(sK2,k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 1.84/0.61    inference(resolution,[],[f1206,f197])).
% 1.84/0.61  fof(f197,plain,(
% 1.84/0.61    ( ! [X6] : (~r2_hidden(sK0,X6) | r1_tarski(sK2,X6)) )),
% 1.84/0.61    inference(superposition,[],[f90,f133])).
% 1.84/0.61  fof(f90,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f56,f76])).
% 1.84/0.61  fof(f56,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f19])).
% 1.84/0.61  fof(f19,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.84/0.61  fof(f1206,plain,(
% 1.84/0.61    r2_hidden(sK0,k1_xboole_0) | v1_xboole_0(k1_xboole_0)),
% 1.84/0.61    inference(superposition,[],[f34,f1203])).
% 1.84/0.61  fof(f1203,plain,(
% 1.84/0.61    sK0 = sK3(k1_xboole_0)),
% 1.84/0.61    inference(subsumption_resolution,[],[f1202,f31])).
% 1.84/0.61  fof(f1202,plain,(
% 1.84/0.61    k1_xboole_0 = sK1 | sK0 = sK3(k1_xboole_0)),
% 1.84/0.61    inference(forward_demodulation,[],[f1201,f233])).
% 1.84/0.61  fof(f1201,plain,(
% 1.84/0.61    sK1 = k3_xboole_0(k1_xboole_0,sK2) | sK0 = sK3(k1_xboole_0)),
% 1.84/0.61    inference(resolution,[],[f1193,f324])).
% 1.84/0.61  fof(f324,plain,(
% 1.84/0.61    v1_xboole_0(k1_xboole_0) | sK0 = sK3(k1_xboole_0)),
% 1.84/0.61    inference(resolution,[],[f315,f198])).
% 1.84/0.61  fof(f315,plain,(
% 1.84/0.61    r2_hidden(sK3(k1_xboole_0),sK2) | v1_xboole_0(k1_xboole_0)),
% 1.84/0.61    inference(resolution,[],[f247,f34])).
% 1.84/0.61  fof(f247,plain,(
% 1.84/0.61    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,sK2)) )),
% 1.84/0.61    inference(superposition,[],[f100,f233])).
% 1.84/0.61  fof(f34,plain,(
% 1.84/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f1])).
% 1.84/0.61  % SZS output end Proof for theBenchmark
% 1.84/0.61  % (17859)------------------------------
% 1.84/0.61  % (17859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (17859)Termination reason: Refutation
% 1.84/0.61  
% 1.84/0.61  % (17859)Memory used [KB]: 2174
% 1.84/0.61  % (17859)Time elapsed: 0.207 s
% 1.84/0.61  % (17859)------------------------------
% 1.84/0.61  % (17859)------------------------------
% 1.84/0.61  % (17853)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.84/0.62  % (17841)Success in time 0.255 s
%------------------------------------------------------------------------------
