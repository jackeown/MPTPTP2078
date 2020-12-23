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
% DateTime   : Thu Dec  3 12:51:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 228 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 789 expanded)
%              Number of equality atoms :   53 ( 233 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f116])).

fof(f116,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f44,f115])).

fof(f115,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f112,plain,(
    ! [X2] :
      ( k1_xboole_0 = k11_relat_1(sK1,X2)
      | r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0))),sK1)
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f94,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
      | r2_hidden(k4_tarski(X1,X0),sK1) ) ),
    inference(resolution,[],[f67,f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f44,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f152,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f151,f78])).

fof(f78,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f151,plain,(
    ! [X0] : ~ r2_hidden(sK0,k10_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f150,f104])).

fof(f104,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f101,f102])).

fof(f102,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f101,f50])).

fof(f101,plain,(
    ! [X2] : ~ r2_hidden(X2,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f100,f87])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f72,f86])).

fof(f86,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f84,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f84,plain,(
    ! [X3] : k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X3),k1_tarski(X3)) ),
    inference(superposition,[],[f54,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f72,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f100,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k10_relat_1(sK1,k1_xboole_0))
      | k1_xboole_0 = k1_tarski(sK3(X2,k1_xboole_0,sK1)) ) ),
    inference(resolution,[],[f97,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(sK3(X0,X1,sK1)),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f150,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0,sK1),k1_xboole_0)
      | ~ r2_hidden(sK0,k10_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f139,f117])).

fof(f117,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f45,f116])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),k11_relat_1(sK1,X0))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(sK3(X0,X1,sK1),k11_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f134,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3(X0,X1,sK1)),sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f63,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:43:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (20332)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (20337)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (20331)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (20339)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (20338)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (20359)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (20352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (20333)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (20342)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (20345)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (20344)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (20332)Refutation not found, incomplete strategy% (20332)------------------------------
% 0.22/0.54  % (20332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20332)Memory used [KB]: 10746
% 0.22/0.54  % (20332)Time elapsed: 0.125 s
% 0.22/0.54  % (20332)------------------------------
% 0.22/0.54  % (20332)------------------------------
% 0.22/0.54  % (20346)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (20337)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f152,f116])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f44,f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X2] : (r2_hidden(X2,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f112,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f20])).
% 0.22/0.54  fof(f20,conjecture,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X2] : (k1_xboole_0 = k11_relat_1(sK1,X2) | r2_hidden(X2,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f95,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0))),sK1) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f94,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | r2_hidden(k4_tarski(X1,X0),sK1)) )),
% 0.22/0.54    inference(resolution,[],[f67,f43])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.54    inference(superposition,[],[f151,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.22/0.54    inference(resolution,[],[f48,f43])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK0,k10_relat_1(sK1,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f150,f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f101,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 0.22/0.54    inference(resolution,[],[f101,f50])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k10_relat_1(sK1,k1_xboole_0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f100,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f72,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_tarski(X3))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f84,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X3] : (k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X3),k1_tarski(X3))) )),
% 0.22/0.54    inference(superposition,[],[f54,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.54    inference(superposition,[],[f53,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,k10_relat_1(sK1,k1_xboole_0)) | k1_xboole_0 = k1_tarski(sK3(X2,k1_xboole_0,sK1))) )),
% 0.22/0.54    inference(resolution,[],[f97,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(sK3(X0,X1,sK1)),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.22/0.54    inference(resolution,[],[f96,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.22/0.54    inference(resolution,[],[f64,f43])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(rectify,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),k1_xboole_0) | ~r2_hidden(sK0,k10_relat_1(sK1,X0))) )),
% 0.22/0.54    inference(superposition,[],[f139,f117])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f45,f116])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),k11_relat_1(sK1,X0)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f135,f43])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(sK3(X0,X1,sK1),k11_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) )),
% 0.22/0.54    inference(resolution,[],[f134,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK3(X0,X1,sK1)),sK1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.22/0.54    inference(resolution,[],[f63,f43])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (20337)------------------------------
% 0.22/0.54  % (20337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20337)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (20337)Memory used [KB]: 6268
% 0.22/0.54  % (20337)Time elapsed: 0.090 s
% 0.22/0.54  % (20337)------------------------------
% 0.22/0.54  % (20337)------------------------------
% 0.22/0.54  % (20348)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (20335)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (20329)Success in time 0.173 s
%------------------------------------------------------------------------------
