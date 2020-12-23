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
% DateTime   : Thu Dec  3 12:51:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 233 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  160 ( 499 expanded)
%              Number of equality atoms :   53 ( 202 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f629])).

fof(f629,plain,(
    k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f119,f476])).

fof(f476,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))) = k4_xboole_0(k1_relat_1(sK1),X2) ),
    inference(forward_demodulation,[],[f475,f117])).

fof(f117,plain,(
    ! [X0] : k4_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f50])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) ) ),
    inference(forward_demodulation,[],[f90,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f65,f58])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f475,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X2))) ),
    inference(forward_demodulation,[],[f443,f135])).

fof(f135,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f107,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | sK1 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f443,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k4_xboole_0(k7_relat_1(sK1,k1_relat_1(sK1)),k7_relat_1(sK1,X2))) ),
    inference(superposition,[],[f121,f433])).

fof(f433,plain,(
    ! [X2] : k7_relat_1(sK1,X2) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2)))) ),
    inference(backward_demodulation,[],[f144,f430])).

fof(f430,plain,(
    ! [X4] : k7_relat_1(sK1,X4) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X4))) ),
    inference(forward_demodulation,[],[f422,f228])).

fof(f228,plain,(
    ! [X3] : k7_relat_1(sK1,X3) = k7_relat_1(sK1,k3_xboole_0(X3,k1_relat_1(k7_relat_1(sK1,X3)))) ),
    inference(resolution,[],[f111,f87])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),X2)
      | k7_relat_1(sK1,X1) = k7_relat_1(sK1,k3_xboole_0(X1,X2)) ) ),
    inference(backward_demodulation,[],[f108,f109])).

fof(f109,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),X2)
      | k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,X1),X2) ) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f62,f55])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f422,plain,(
    ! [X4] : k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X4))) = k7_relat_1(sK1,k3_xboole_0(X4,k1_relat_1(k7_relat_1(sK1,X4)))) ),
    inference(resolution,[],[f223,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(X1,X0)) ) ),
    inference(forward_demodulation,[],[f126,f109])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X1),X0) ) ),
    inference(resolution,[],[f79,f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f223,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),X5) ),
    inference(subsumption_resolution,[],[f215,f92])).

fof(f215,plain,(
    ! [X5] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),X5)
      | ~ v1_relat_1(k7_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f141,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f141,plain,(
    ! [X1] : v4_relat_1(k7_relat_1(sK1,X1),X1) ),
    inference(subsumption_resolution,[],[f137,f55])).

fof(f137,plain,(
    ! [X1] :
      ( v4_relat_1(k7_relat_1(sK1,X1),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f134,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X2,X1)
      | v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f134,plain,(
    v4_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f100,f87])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | v4_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f68,f55])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f144,plain,(
    ! [X2] : k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X2))) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2)))) ),
    inference(resolution,[],[f128,f98])).

fof(f98,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f121,plain,(
    ! [X2,X1] : k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X1)),X2) = k1_relat_1(k4_xboole_0(k7_relat_1(sK1,X1),k7_relat_1(sK1,k3_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f118,f109])).

fof(f118,plain,(
    ! [X2,X1] : k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X1)),X2) = k1_relat_1(k4_xboole_0(k7_relat_1(sK1,X1),k7_relat_1(k7_relat_1(sK1,X1),X2))) ),
    inference(resolution,[],[f91,f92])).

fof(f119,plain,(
    k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f93,f117])).

fof(f93,plain,(
    k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f89,f58])).

fof(f89,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f56,f58])).

fof(f56,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:24:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (6560)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.50  % (6555)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.50  % (6548)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (6576)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.51  % (6568)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.51  % (6552)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (6550)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (6556)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.52  % (6563)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (6570)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.53  % (6559)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.53  % (6549)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (6553)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.53  % (6562)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.53  % (6574)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (6573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (6551)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (6554)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (6575)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.54  % (6572)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.54  % (6576)Refutation not found, incomplete strategy% (6576)------------------------------
% 0.19/0.54  % (6576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (6576)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (6576)Memory used [KB]: 10746
% 0.19/0.54  % (6576)Time elapsed: 0.133 s
% 0.19/0.54  % (6576)------------------------------
% 0.19/0.54  % (6576)------------------------------
% 0.19/0.54  % (6555)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f630,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(trivial_inequality_removal,[],[f629])).
% 0.19/0.54  fof(f629,plain,(
% 0.19/0.54    k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.19/0.54    inference(superposition,[],[f119,f476])).
% 0.19/0.54  fof(f476,plain,(
% 0.19/0.54    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))) = k4_xboole_0(k1_relat_1(sK1),X2)) )),
% 0.19/0.54    inference(forward_demodulation,[],[f475,f117])).
% 0.19/0.54  fof(f117,plain,(
% 0.19/0.54    ( ! [X0] : (k4_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X0)))) )),
% 0.19/0.54    inference(resolution,[],[f91,f55])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    v1_relat_1(sK1)),
% 0.19/0.54    inference(cnf_transformation,[],[f51])).
% 0.19/0.54  fof(f51,plain,(
% 0.19/0.54    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f50])).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f27])).
% 0.19/0.54  fof(f27,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.19/0.54    inference(negated_conjecture,[],[f26])).
% 0.19/0.54  fof(f26,conjecture,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 0.19/0.54  fof(f91,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0)))) )),
% 0.19/0.54    inference(forward_demodulation,[],[f90,f58])).
% 0.19/0.54  fof(f58,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f13])).
% 0.19/0.54  fof(f13,axiom,(
% 0.19/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.19/0.54  fof(f90,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.54    inference(forward_demodulation,[],[f65,f58])).
% 0.19/0.54  fof(f65,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f33])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f22])).
% 0.19/0.54  fof(f22,axiom,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.19/0.54  fof(f475,plain,(
% 0.19/0.54    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X2)))) )),
% 0.19/0.54    inference(forward_demodulation,[],[f443,f135])).
% 0.19/0.54  fof(f135,plain,(
% 0.19/0.54    sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 0.19/0.54    inference(resolution,[],[f107,f87])).
% 0.19/0.54  fof(f87,plain,(
% 0.19/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.54    inference(equality_resolution,[],[f73])).
% 0.19/0.54  fof(f73,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f54])).
% 0.19/0.54  fof(f54,plain,(
% 0.19/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.54    inference(flattening,[],[f53])).
% 0.19/0.54  fof(f53,plain,(
% 0.19/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.54    inference(nnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.54  fof(f107,plain,(
% 0.19/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | sK1 = k7_relat_1(sK1,X0)) )),
% 0.19/0.54    inference(resolution,[],[f66,f55])).
% 0.19/0.54  fof(f66,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f35])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(flattening,[],[f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f25])).
% 0.19/0.54  fof(f25,axiom,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.19/0.54  fof(f443,plain,(
% 0.19/0.54    ( ! [X2] : (k4_xboole_0(k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k4_xboole_0(k7_relat_1(sK1,k1_relat_1(sK1)),k7_relat_1(sK1,X2)))) )),
% 0.19/0.54    inference(superposition,[],[f121,f433])).
% 0.19/0.54  fof(f433,plain,(
% 0.19/0.54    ( ! [X2] : (k7_relat_1(sK1,X2) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))))) )),
% 0.19/0.54    inference(backward_demodulation,[],[f144,f430])).
% 0.19/0.54  fof(f430,plain,(
% 0.19/0.54    ( ! [X4] : (k7_relat_1(sK1,X4) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X4)))) )),
% 0.19/0.54    inference(forward_demodulation,[],[f422,f228])).
% 0.19/0.54  fof(f228,plain,(
% 0.19/0.54    ( ! [X3] : (k7_relat_1(sK1,X3) = k7_relat_1(sK1,k3_xboole_0(X3,k1_relat_1(k7_relat_1(sK1,X3))))) )),
% 0.19/0.54    inference(resolution,[],[f111,f87])).
% 0.19/0.54  fof(f111,plain,(
% 0.19/0.54    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),X2) | k7_relat_1(sK1,X1) = k7_relat_1(sK1,k3_xboole_0(X1,X2))) )),
% 0.19/0.54    inference(backward_demodulation,[],[f108,f109])).
% 0.19/0.54  fof(f109,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(resolution,[],[f78,f55])).
% 0.19/0.54  fof(f78,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f45])).
% 0.19/0.54  fof(f45,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f18])).
% 0.19/0.54  fof(f18,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.19/0.54  fof(f108,plain,(
% 0.19/0.54    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),X2) | k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,X1),X2)) )),
% 0.19/0.54    inference(resolution,[],[f66,f92])).
% 0.19/0.54  fof(f92,plain,(
% 0.19/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.19/0.54    inference(resolution,[],[f62,f55])).
% 0.19/0.54  fof(f62,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f16])).
% 0.19/0.54  fof(f16,axiom,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.19/0.54  fof(f422,plain,(
% 0.19/0.54    ( ! [X4] : (k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X4))) = k7_relat_1(sK1,k3_xboole_0(X4,k1_relat_1(k7_relat_1(sK1,X4))))) )),
% 0.19/0.54    inference(resolution,[],[f223,f128])).
% 0.19/0.54  fof(f128,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(X1,X0))) )),
% 0.19/0.54    inference(forward_demodulation,[],[f126,f109])).
% 0.19/0.54  fof(f126,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X1),X0)) )),
% 0.19/0.54    inference(resolution,[],[f79,f55])).
% 0.19/0.54  fof(f79,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(flattening,[],[f46])).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f19])).
% 0.19/0.54  fof(f19,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.19/0.54  fof(f223,plain,(
% 0.19/0.54    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),X5)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f215,f92])).
% 0.19/0.54  fof(f215,plain,(
% 0.19/0.54    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X5)),X5) | ~v1_relat_1(k7_relat_1(sK1,X5))) )),
% 0.19/0.54    inference(resolution,[],[f141,f67])).
% 0.19/0.54  fof(f67,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f52])).
% 0.19/0.54  fof(f52,plain,(
% 0.19/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(nnf_transformation,[],[f36])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,axiom,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.54  fof(f141,plain,(
% 0.19/0.54    ( ! [X1] : (v4_relat_1(k7_relat_1(sK1,X1),X1)) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f137,f55])).
% 0.19/0.54  fof(f137,plain,(
% 0.19/0.54    ( ! [X1] : (v4_relat_1(k7_relat_1(sK1,X1),X1) | ~v1_relat_1(sK1)) )),
% 0.19/0.54    inference(resolution,[],[f134,f81])).
% 0.19/0.54  fof(f81,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X1) | v4_relat_1(k7_relat_1(X2,X0),X0) | ~v1_relat_1(X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f49])).
% 0.19/0.54  fof(f49,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(flattening,[],[f48])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.19/0.54    inference(ennf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.19/0.54  fof(f134,plain,(
% 0.19/0.54    v4_relat_1(sK1,k1_relat_1(sK1))),
% 0.19/0.54    inference(resolution,[],[f100,f87])).
% 0.19/0.54  fof(f100,plain,(
% 0.19/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | v4_relat_1(sK1,X0)) )),
% 0.19/0.54    inference(resolution,[],[f68,f55])).
% 0.19/0.54  fof(f68,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f52])).
% 0.19/0.54  fof(f144,plain,(
% 0.19/0.54    ( ! [X2] : (k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X2))) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))))) )),
% 0.19/0.54    inference(resolution,[],[f128,f98])).
% 0.19/0.54  fof(f98,plain,(
% 0.19/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) )),
% 0.19/0.54    inference(resolution,[],[f64,f55])).
% 0.19/0.54  fof(f64,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f32])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f24])).
% 0.19/0.54  fof(f24,axiom,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.19/0.54  fof(f121,plain,(
% 0.19/0.54    ( ! [X2,X1] : (k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X1)),X2) = k1_relat_1(k4_xboole_0(k7_relat_1(sK1,X1),k7_relat_1(sK1,k3_xboole_0(X1,X2))))) )),
% 0.19/0.54    inference(forward_demodulation,[],[f118,f109])).
% 0.19/0.54  fof(f118,plain,(
% 0.19/0.54    ( ! [X2,X1] : (k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X1)),X2) = k1_relat_1(k4_xboole_0(k7_relat_1(sK1,X1),k7_relat_1(k7_relat_1(sK1,X1),X2)))) )),
% 0.19/0.54    inference(resolution,[],[f91,f92])).
% 0.19/0.54  fof(f119,plain,(
% 0.19/0.54    k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.19/0.54    inference(backward_demodulation,[],[f93,f117])).
% 0.19/0.54  fof(f93,plain,(
% 0.19/0.54    k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0)))),
% 0.19/0.54    inference(superposition,[],[f89,f58])).
% 0.19/0.54  fof(f89,plain,(
% 0.19/0.54    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0)))),
% 0.19/0.54    inference(forward_demodulation,[],[f56,f58])).
% 0.19/0.54  fof(f56,plain,(
% 0.19/0.54    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.19/0.54    inference(cnf_transformation,[],[f51])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (6555)------------------------------
% 0.19/0.54  % (6555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (6555)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (6555)Memory used [KB]: 2174
% 0.19/0.54  % (6555)Time elapsed: 0.131 s
% 0.19/0.54  % (6555)------------------------------
% 0.19/0.54  % (6555)------------------------------
% 0.19/0.54  % (6577)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.54  % (6547)Success in time 0.185 s
%------------------------------------------------------------------------------
