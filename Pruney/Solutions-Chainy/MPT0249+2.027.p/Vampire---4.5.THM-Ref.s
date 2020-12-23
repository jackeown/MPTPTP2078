%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:14 EST 2020

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  122 (2638 expanded)
%              Number of leaves         :   25 ( 851 expanded)
%              Depth                    :   24
%              Number of atoms          :  171 (3336 expanded)
%              Number of equality atoms :  106 (2701 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f745,plain,(
    $false ),
    inference(global_subsumption,[],[f704,f744])).

fof(f744,plain,(
    r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f733,f534])).

fof(f534,plain,(
    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f306,f465,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f465,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(backward_demodulation,[],[f384,f432])).

fof(f432,plain,(
    sK0 = sK3(sK1) ),
    inference(unit_resulting_resolution,[],[f334,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f334,plain,(
    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f91,f91,f306,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(sK1),X3)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f116,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK1),X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f112,f50])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1),X1)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f108,f50])).

fof(f108,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK1),X2)
      | ~ r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f50,f99])).

fof(f99,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f384,plain,(
    r1_tarski(k6_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f306,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f81,f78])).

fof(f78,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f32,f76,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f733,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) ),
    inference(backward_demodulation,[],[f385,f702])).

fof(f702,plain,(
    sK0 = sK3(sK2) ),
    inference(unit_resulting_resolution,[],[f91,f676,f562])).

fof(f562,plain,(
    ! [X5] :
      ( sK0 = sK3(sK2)
      | ~ r1_tarski(sK2,X5)
      | ~ r1_tarski(X5,sK1) ) ),
    inference(resolution,[],[f549,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK2),X1)
      | ~ r1_tarski(sK2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f109,f50])).

fof(f109,plain,(
    ! [X3] :
      ( r2_hidden(sK3(sK2),X3)
      | ~ r1_tarski(sK2,X3) ) ),
    inference(resolution,[],[f50,f100])).

fof(f100,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f35,f38])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f549,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | sK0 = X1 ) ),
    inference(superposition,[],[f93,f534])).

fof(f676,plain,(
    r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f81,f646])).

fof(f646,plain,(
    sK1 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f642,f540])).

fof(f540,plain,(
    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(backward_demodulation,[],[f78,f534])).

fof(f642,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f589,f635])).

fof(f635,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) ),
    inference(superposition,[],[f90,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f67,f73,f68,f72])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f66,f65,f73,f68,f76])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f589,plain,(
    k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK2)) ),
    inference(forward_demodulation,[],[f588,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f59,f71,f71])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f588,plain,(
    k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f577,f194])).

fof(f194,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f122,f178])).

fof(f178,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f167,f134])).

fof(f134,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f122,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f167,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f122,f120])).

fof(f120,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f61,f36])).

fof(f61,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f122,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f117,f97])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f96,f80])).

fof(f80,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f73])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f79,f36])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f39,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f117,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f61,f36])).

fof(f577,plain,(
    k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,sK1))) ),
    inference(superposition,[],[f123,f540])).

fof(f123,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(backward_demodulation,[],[f98,f122])).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) ),
    inference(backward_demodulation,[],[f82,f61])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f45,f73,f75,f73])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f44,f74])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f385,plain,(
    r1_tarski(k6_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f100,f88])).

fof(f704,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f33,f676,f49])).

fof(f33,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (31125)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (31148)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (31133)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (31140)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (31142)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (31135)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (31150)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (31129)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31130)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (31135)Refutation not found, incomplete strategy% (31135)------------------------------
% 0.21/0.52  % (31135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31135)Memory used [KB]: 10618
% 0.21/0.52  % (31135)Time elapsed: 0.116 s
% 0.21/0.52  % (31135)------------------------------
% 0.21/0.52  % (31135)------------------------------
% 0.21/0.53  % (31153)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (31152)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (31151)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (31149)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (31127)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31126)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31128)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (31132)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (31154)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (31145)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (31146)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (31143)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (31141)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (31144)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (31138)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (31137)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (31136)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (31134)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (31136)Refutation not found, incomplete strategy% (31136)------------------------------
% 0.21/0.55  % (31136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31136)Memory used [KB]: 10618
% 0.21/0.55  % (31136)Time elapsed: 0.150 s
% 0.21/0.55  % (31136)------------------------------
% 0.21/0.55  % (31136)------------------------------
% 0.21/0.56  % (31131)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (31147)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (31139)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.66  % (31158)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.77/0.73  % (31149)Refutation found. Thanks to Tanya!
% 2.77/0.73  % SZS status Theorem for theBenchmark
% 2.77/0.73  % SZS output start Proof for theBenchmark
% 2.77/0.73  fof(f745,plain,(
% 2.77/0.73    $false),
% 2.77/0.73    inference(global_subsumption,[],[f704,f744])).
% 2.77/0.73  fof(f744,plain,(
% 2.77/0.73    r1_tarski(sK1,sK2)),
% 2.77/0.73    inference(forward_demodulation,[],[f733,f534])).
% 2.77/0.73  fof(f534,plain,(
% 2.77/0.73    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f306,f465,f49])).
% 2.77/0.73  fof(f49,plain,(
% 2.77/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.77/0.73    inference(cnf_transformation,[],[f5])).
% 2.77/0.73  fof(f5,axiom,(
% 2.77/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.77/0.73  fof(f465,plain,(
% 2.77/0.73    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.77/0.73    inference(backward_demodulation,[],[f384,f432])).
% 2.77/0.73  fof(f432,plain,(
% 2.77/0.73    sK0 = sK3(sK1)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f334,f93])).
% 2.77/0.73  fof(f93,plain,(
% 2.77/0.73    ( ! [X2,X0] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 2.77/0.73    inference(equality_resolution,[],[f85])).
% 2.77/0.73  fof(f85,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.77/0.73    inference(definition_unfolding,[],[f54,f76])).
% 2.77/0.73  fof(f76,plain,(
% 2.77/0.73    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f37,f72])).
% 2.77/0.73  fof(f72,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f43,f71])).
% 2.77/0.73  fof(f71,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f60,f70])).
% 2.77/0.73  fof(f70,plain,(
% 2.77/0.73    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f62,f69])).
% 2.77/0.73  fof(f69,plain,(
% 2.77/0.73    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f63,f68])).
% 2.77/0.73  fof(f68,plain,(
% 2.77/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f64,f65])).
% 2.77/0.73  fof(f65,plain,(
% 2.77/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f22])).
% 2.77/0.73  fof(f22,axiom,(
% 2.77/0.73    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.77/0.73  fof(f64,plain,(
% 2.77/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f21])).
% 2.77/0.73  fof(f21,axiom,(
% 2.77/0.73    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.77/0.73  fof(f63,plain,(
% 2.77/0.73    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f20])).
% 2.77/0.73  fof(f20,axiom,(
% 2.77/0.73    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.77/0.73  fof(f62,plain,(
% 2.77/0.73    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f19])).
% 2.77/0.73  fof(f19,axiom,(
% 2.77/0.73    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.77/0.73  fof(f60,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f18])).
% 2.77/0.73  fof(f18,axiom,(
% 2.77/0.73    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.77/0.73  fof(f43,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f17])).
% 2.77/0.73  fof(f17,axiom,(
% 2.77/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.77/0.73  fof(f37,plain,(
% 2.77/0.73    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f16])).
% 2.77/0.73  fof(f16,axiom,(
% 2.77/0.73    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.77/0.73  fof(f54,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.77/0.73    inference(cnf_transformation,[],[f12])).
% 2.77/0.73  fof(f12,axiom,(
% 2.77/0.73    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.77/0.73  fof(f334,plain,(
% 2.77/0.73    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f91,f91,f91,f306,f129])).
% 2.77/0.73  fof(f129,plain,(
% 2.77/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(sK1),X3) | ~r1_tarski(sK1,X0) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3)) )),
% 2.77/0.73    inference(resolution,[],[f116,f50])).
% 2.77/0.73  fof(f50,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f31])).
% 2.77/0.73  fof(f31,plain,(
% 2.77/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.77/0.73    inference(ennf_transformation,[],[f1])).
% 2.77/0.73  fof(f1,axiom,(
% 2.77/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.77/0.73  fof(f116,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK1),X2) | ~r1_tarski(X0,X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X1,X2)) )),
% 2.77/0.73    inference(resolution,[],[f112,f50])).
% 2.77/0.73  fof(f112,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r2_hidden(sK3(sK1),X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X0,X1)) )),
% 2.77/0.73    inference(resolution,[],[f108,f50])).
% 2.77/0.73  fof(f108,plain,(
% 2.77/0.73    ( ! [X2] : (r2_hidden(sK3(sK1),X2) | ~r1_tarski(sK1,X2)) )),
% 2.77/0.73    inference(resolution,[],[f50,f99])).
% 2.77/0.73  fof(f99,plain,(
% 2.77/0.73    r2_hidden(sK3(sK1),sK1)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f34,f38])).
% 2.77/0.73  fof(f38,plain,(
% 2.77/0.73    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.77/0.73    inference(cnf_transformation,[],[f30])).
% 2.77/0.73  fof(f30,plain,(
% 2.77/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.77/0.73    inference(ennf_transformation,[],[f4])).
% 2.77/0.73  fof(f4,axiom,(
% 2.77/0.73    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.77/0.73  fof(f34,plain,(
% 2.77/0.73    k1_xboole_0 != sK1),
% 2.77/0.73    inference(cnf_transformation,[],[f29])).
% 2.77/0.73  fof(f29,plain,(
% 2.77/0.73    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.77/0.73    inference(ennf_transformation,[],[f26])).
% 2.77/0.73  fof(f26,negated_conjecture,(
% 2.77/0.73    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.77/0.73    inference(negated_conjecture,[],[f25])).
% 2.77/0.73  fof(f25,conjecture,(
% 2.77/0.73    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 2.77/0.73  fof(f91,plain,(
% 2.77/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.77/0.73    inference(equality_resolution,[],[f48])).
% 2.77/0.73  fof(f48,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.77/0.73    inference(cnf_transformation,[],[f5])).
% 2.77/0.73  fof(f384,plain,(
% 2.77/0.73    r1_tarski(k6_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1)),sK1)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f99,f88])).
% 2.77/0.73  fof(f88,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f57,f76])).
% 2.77/0.73  fof(f57,plain,(
% 2.77/0.73    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f23])).
% 2.77/0.73  fof(f23,axiom,(
% 2.77/0.73    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.77/0.73  fof(f306,plain,(
% 2.77/0.73    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.77/0.73    inference(superposition,[],[f81,f78])).
% 2.77/0.73  fof(f78,plain,(
% 2.77/0.73    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.77/0.73    inference(definition_unfolding,[],[f32,f76,f73])).
% 2.77/0.73  fof(f73,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f42,f72])).
% 2.77/0.73  fof(f42,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f24])).
% 2.77/0.73  fof(f24,axiom,(
% 2.77/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.77/0.73  fof(f32,plain,(
% 2.77/0.73    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.77/0.73    inference(cnf_transformation,[],[f29])).
% 2.77/0.73  fof(f81,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f41,f73])).
% 2.77/0.73  fof(f41,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f8])).
% 2.77/0.73  fof(f8,axiom,(
% 2.77/0.73    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.77/0.73  fof(f733,plain,(
% 2.77/0.73    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)),
% 2.77/0.73    inference(backward_demodulation,[],[f385,f702])).
% 2.77/0.73  fof(f702,plain,(
% 2.77/0.73    sK0 = sK3(sK2)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f91,f676,f562])).
% 2.77/0.73  fof(f562,plain,(
% 2.77/0.73    ( ! [X5] : (sK0 = sK3(sK2) | ~r1_tarski(sK2,X5) | ~r1_tarski(X5,sK1)) )),
% 2.77/0.73    inference(resolution,[],[f549,f114])).
% 2.77/0.73  fof(f114,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r2_hidden(sK3(sK2),X1) | ~r1_tarski(sK2,X0) | ~r1_tarski(X0,X1)) )),
% 2.77/0.73    inference(resolution,[],[f109,f50])).
% 2.77/0.73  fof(f109,plain,(
% 2.77/0.73    ( ! [X3] : (r2_hidden(sK3(sK2),X3) | ~r1_tarski(sK2,X3)) )),
% 2.77/0.73    inference(resolution,[],[f50,f100])).
% 2.77/0.73  fof(f100,plain,(
% 2.77/0.73    r2_hidden(sK3(sK2),sK2)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f35,f38])).
% 2.77/0.73  fof(f35,plain,(
% 2.77/0.73    k1_xboole_0 != sK2),
% 2.77/0.73    inference(cnf_transformation,[],[f29])).
% 2.77/0.73  fof(f549,plain,(
% 2.77/0.73    ( ! [X1] : (~r2_hidden(X1,sK1) | sK0 = X1) )),
% 2.77/0.73    inference(superposition,[],[f93,f534])).
% 2.77/0.73  fof(f676,plain,(
% 2.77/0.73    r1_tarski(sK2,sK1)),
% 2.77/0.73    inference(superposition,[],[f81,f646])).
% 2.77/0.73  fof(f646,plain,(
% 2.77/0.73    sK1 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2)))),
% 2.77/0.73    inference(forward_demodulation,[],[f642,f540])).
% 2.77/0.73  fof(f540,plain,(
% 2.77/0.73    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.77/0.73    inference(backward_demodulation,[],[f78,f534])).
% 2.77/0.73  fof(f642,plain,(
% 2.77/0.73    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2)))),
% 2.77/0.73    inference(backward_demodulation,[],[f589,f635])).
% 2.77/0.73  fof(f635,plain,(
% 2.77/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6)) )),
% 2.77/0.73    inference(superposition,[],[f90,f77])).
% 2.77/0.73  fof(f77,plain,(
% 2.77/0.73    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f67,f73,f68,f72])).
% 2.77/0.73  fof(f67,plain,(
% 2.77/0.73    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f15])).
% 2.77/0.73  fof(f15,axiom,(
% 2.77/0.73    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 2.77/0.73  fof(f90,plain,(
% 2.77/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f66,f65,f73,f68,f76])).
% 2.77/0.73  fof(f66,plain,(
% 2.77/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f14])).
% 2.77/0.73  fof(f14,axiom,(
% 2.77/0.73    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 2.77/0.73  fof(f589,plain,(
% 2.77/0.73    k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK2))),
% 2.77/0.73    inference(forward_demodulation,[],[f588,f89])).
% 2.77/0.73  fof(f89,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 2.77/0.73    inference(definition_unfolding,[],[f59,f71,f71])).
% 2.77/0.73  fof(f59,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f13])).
% 2.77/0.73  fof(f13,axiom,(
% 2.77/0.73    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 2.77/0.73  fof(f588,plain,(
% 2.77/0.73    k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2)))),
% 2.77/0.73    inference(forward_demodulation,[],[f577,f194])).
% 2.77/0.73  fof(f194,plain,(
% 2.77/0.73    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 2.77/0.73    inference(superposition,[],[f122,f178])).
% 2.77/0.73  fof(f178,plain,(
% 2.77/0.73    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2) )),
% 2.77/0.73    inference(forward_demodulation,[],[f167,f134])).
% 2.77/0.73  fof(f134,plain,(
% 2.77/0.73    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.77/0.73    inference(superposition,[],[f122,f36])).
% 2.77/0.73  fof(f36,plain,(
% 2.77/0.73    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f10])).
% 2.77/0.73  fof(f10,axiom,(
% 2.77/0.73    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.77/0.73  fof(f167,plain,(
% 2.77/0.73    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(X2,X3))) )),
% 2.77/0.73    inference(superposition,[],[f122,f120])).
% 2.77/0.73  fof(f120,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 2.77/0.73    inference(superposition,[],[f61,f36])).
% 2.77/0.73  fof(f61,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f9])).
% 2.77/0.73  fof(f9,axiom,(
% 2.77/0.73    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.77/0.73  fof(f122,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.77/0.73    inference(forward_demodulation,[],[f117,f97])).
% 2.77/0.73  fof(f97,plain,(
% 2.77/0.73    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.77/0.73    inference(backward_demodulation,[],[f96,f80])).
% 2.77/0.73  fof(f80,plain,(
% 2.77/0.73    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.77/0.73    inference(definition_unfolding,[],[f40,f73])).
% 2.77/0.73  fof(f40,plain,(
% 2.77/0.73    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.77/0.73    inference(cnf_transformation,[],[f28])).
% 2.77/0.73  fof(f28,plain,(
% 2.77/0.73    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.77/0.73    inference(rectify,[],[f2])).
% 2.77/0.73  fof(f2,axiom,(
% 2.77/0.73    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.77/0.73  fof(f96,plain,(
% 2.77/0.73    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.77/0.73    inference(forward_demodulation,[],[f79,f36])).
% 2.77/0.73  fof(f79,plain,(
% 2.77/0.73    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.77/0.73    inference(definition_unfolding,[],[f39,f74])).
% 2.77/0.73  fof(f74,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f46,f73])).
% 2.77/0.73  fof(f46,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f11])).
% 2.77/0.73  fof(f11,axiom,(
% 2.77/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.77/0.73  fof(f39,plain,(
% 2.77/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.77/0.73    inference(cnf_transformation,[],[f27])).
% 2.77/0.73  fof(f27,plain,(
% 2.77/0.73    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.77/0.73    inference(rectify,[],[f3])).
% 2.77/0.73  fof(f3,axiom,(
% 2.77/0.73    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.77/0.73  fof(f117,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.77/0.73    inference(superposition,[],[f61,f36])).
% 2.77/0.73  fof(f577,plain,(
% 2.77/0.73    k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,sK1)))),
% 2.77/0.73    inference(superposition,[],[f123,f540])).
% 2.77/0.73  fof(f123,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) )),
% 2.77/0.73    inference(backward_demodulation,[],[f98,f122])).
% 2.77/0.73  fof(f98,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))))) )),
% 2.77/0.73    inference(backward_demodulation,[],[f82,f61])).
% 2.77/0.73  fof(f82,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f45,f73,f75,f73])).
% 2.77/0.73  fof(f75,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f44,f74])).
% 2.77/0.73  fof(f44,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f6])).
% 2.77/0.73  fof(f6,axiom,(
% 2.77/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.77/0.73  fof(f45,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f7])).
% 2.77/0.73  fof(f7,axiom,(
% 2.77/0.73    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.77/0.73  fof(f385,plain,(
% 2.77/0.73    r1_tarski(k6_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2)),sK2)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f100,f88])).
% 2.77/0.73  fof(f704,plain,(
% 2.77/0.73    ~r1_tarski(sK1,sK2)),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f33,f676,f49])).
% 2.77/0.73  fof(f33,plain,(
% 2.77/0.73    sK1 != sK2),
% 2.77/0.73    inference(cnf_transformation,[],[f29])).
% 2.77/0.73  % SZS output end Proof for theBenchmark
% 2.77/0.73  % (31149)------------------------------
% 2.77/0.73  % (31149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.73  % (31149)Termination reason: Refutation
% 2.77/0.73  
% 2.77/0.73  % (31149)Memory used [KB]: 9978
% 2.77/0.73  % (31149)Time elapsed: 0.308 s
% 2.77/0.73  % (31149)------------------------------
% 2.77/0.73  % (31149)------------------------------
% 2.77/0.74  % (31124)Success in time 0.377 s
%------------------------------------------------------------------------------
