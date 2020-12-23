%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:21 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 507 expanded)
%              Number of leaves         :   14 ( 141 expanded)
%              Depth                    :   23
%              Number of atoms          :  223 (1731 expanded)
%              Number of equality atoms :   62 ( 487 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f546,plain,(
    $false ),
    inference(subsumption_resolution,[],[f545,f32])).

fof(f32,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f545,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f538,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f538,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f78,f497])).

fof(f497,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f456,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f456,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f455,f132])).

fof(f132,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f93,f126])).

fof(f126,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f100,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))
      | k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) = X0 ) ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_xboole_0)),X0) ),
    inference(resolution,[],[f93,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f93,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f91,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0)))
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f60,f72])).

fof(f72,plain,(
    ! [X1] : k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X1)) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f61,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f30,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f59,f85])).

fof(f85,plain,(
    k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f72,f34])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f455,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0
      | r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f181,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f181,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK3(X1,X2,k1_xboole_0),X3)
      | k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f139,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f139,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,k1_xboole_0),X1)
      | k1_xboole_0 = k4_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f134,f126])).

fof(f134,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,k1_xboole_0),X1)
      | k4_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f95,f126])).

fof(f95,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),X1)
      | k4_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ) ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1))) ),
    inference(superposition,[],[f73,f54])).

fof(f73,plain,(
    ! [X2] : k1_setfam_1(k1_enumset1(X2,X2,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X2)) ),
    inference(superposition,[],[f61,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f35,f52,f52])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (32010)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (32002)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (32002)Refutation not found, incomplete strategy% (32002)------------------------------
% 0.21/0.49  % (32002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32002)Memory used [KB]: 10618
% 0.21/0.49  % (32002)Time elapsed: 0.084 s
% 0.21/0.49  % (32002)------------------------------
% 0.21/0.49  % (32002)------------------------------
% 0.21/0.49  % (32010)Refutation not found, incomplete strategy% (32010)------------------------------
% 0.21/0.49  % (32010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32010)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32010)Memory used [KB]: 10618
% 0.21/0.49  % (32010)Time elapsed: 0.085 s
% 0.21/0.49  % (32010)------------------------------
% 0.21/0.49  % (32010)------------------------------
% 0.21/0.50  % (31995)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (31997)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (31995)Refutation not found, incomplete strategy% (31995)------------------------------
% 0.21/0.50  % (31995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31995)Memory used [KB]: 10746
% 0.21/0.50  % (31995)Time elapsed: 0.098 s
% 0.21/0.50  % (31995)------------------------------
% 0.21/0.50  % (31995)------------------------------
% 0.21/0.50  % (32008)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (31996)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (31993)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (31994)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (32006)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (32015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.52  % (32016)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.52  % (32013)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.52  % (31999)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.52  % (32007)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.52  % (32018)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.53  % (32005)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (32014)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.53  % (32012)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.53  % (32011)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.53  % (31998)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (32000)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.53  % (32017)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.53  % (31993)Refutation not found, incomplete strategy% (31993)------------------------------
% 1.30/0.53  % (31993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (31993)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (31993)Memory used [KB]: 1663
% 1.30/0.53  % (31993)Time elapsed: 0.089 s
% 1.30/0.53  % (31993)------------------------------
% 1.30/0.53  % (31993)------------------------------
% 1.30/0.53  % (32015)Refutation not found, incomplete strategy% (32015)------------------------------
% 1.30/0.53  % (32015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (32015)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (32015)Memory used [KB]: 10746
% 1.30/0.53  % (32015)Time elapsed: 0.097 s
% 1.30/0.53  % (32015)------------------------------
% 1.30/0.53  % (32015)------------------------------
% 1.43/0.53  % (32019)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.53  % (32021)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.54  % (32020)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.54  % (32001)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.54  % (32009)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.54  % (32013)Refutation not found, incomplete strategy% (32013)------------------------------
% 1.43/0.54  % (32013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (32013)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (32013)Memory used [KB]: 10746
% 1.43/0.54  % (32013)Time elapsed: 0.126 s
% 1.43/0.54  % (32013)------------------------------
% 1.43/0.54  % (32013)------------------------------
% 1.43/0.54  % (32003)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.54  % (32022)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.54  % (32003)Refutation not found, incomplete strategy% (32003)------------------------------
% 1.43/0.54  % (32003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (32003)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (32003)Memory used [KB]: 10618
% 1.43/0.54  % (32003)Time elapsed: 0.142 s
% 1.43/0.54  % (32003)------------------------------
% 1.43/0.54  % (32003)------------------------------
% 1.43/0.54  % (32004)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (32004)Refutation not found, incomplete strategy% (32004)------------------------------
% 1.43/0.55  % (32004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32004)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (32004)Memory used [KB]: 10618
% 1.43/0.55  % (32004)Time elapsed: 0.142 s
% 1.43/0.55  % (32004)------------------------------
% 1.43/0.55  % (32004)------------------------------
% 1.43/0.55  % (32018)Refutation not found, incomplete strategy% (32018)------------------------------
% 1.43/0.55  % (32018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32018)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (32018)Memory used [KB]: 6268
% 1.43/0.55  % (32018)Time elapsed: 0.150 s
% 1.43/0.55  % (32018)------------------------------
% 1.43/0.55  % (32018)------------------------------
% 1.43/0.58  % (32001)Refutation found. Thanks to Tanya!
% 1.43/0.58  % SZS status Theorem for theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f546,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(subsumption_resolution,[],[f545,f32])).
% 1.43/0.58  fof(f32,plain,(
% 1.43/0.58    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.43/0.58    inference(cnf_transformation,[],[f18])).
% 1.43/0.58  fof(f18,plain,(
% 1.43/0.58    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f17])).
% 1.43/0.58  fof(f17,plain,(
% 1.43/0.58    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f14,plain,(
% 1.43/0.58    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.43/0.58    inference(flattening,[],[f13])).
% 1.43/0.58  fof(f13,plain,(
% 1.43/0.58    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f12])).
% 1.43/0.58  fof(f12,negated_conjecture,(
% 1.43/0.58    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.43/0.58    inference(negated_conjecture,[],[f11])).
% 1.43/0.58  fof(f11,conjecture,(
% 1.43/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.43/0.58  fof(f545,plain,(
% 1.43/0.58    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.43/0.58    inference(forward_demodulation,[],[f538,f34])).
% 1.43/0.58  fof(f34,plain,(
% 1.43/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.58    inference(cnf_transformation,[],[f6])).
% 1.43/0.58  fof(f6,axiom,(
% 1.43/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.43/0.58  fof(f538,plain,(
% 1.43/0.58    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.43/0.58    inference(superposition,[],[f78,f497])).
% 1.43/0.58  fof(f497,plain,(
% 1.43/0.58    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 1.43/0.58    inference(resolution,[],[f456,f31])).
% 1.43/0.58  fof(f31,plain,(
% 1.43/0.58    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.43/0.58    inference(cnf_transformation,[],[f18])).
% 1.43/0.58  fof(f456,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f455,f132])).
% 1.43/0.58  fof(f132,plain,(
% 1.43/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.43/0.58    inference(backward_demodulation,[],[f93,f126])).
% 1.43/0.58  fof(f126,plain,(
% 1.43/0.58    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),
% 1.43/0.58    inference(resolution,[],[f100,f33])).
% 1.43/0.58  fof(f33,plain,(
% 1.43/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f5])).
% 1.43/0.58  fof(f5,axiom,(
% 1.43/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.43/0.58  fof(f100,plain,(
% 1.43/0.58    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0))) | k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) = X0) )),
% 1.43/0.58    inference(resolution,[],[f94,f42])).
% 1.43/0.58  fof(f42,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f20])).
% 1.43/0.58  fof(f20,plain,(
% 1.43/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.58    inference(flattening,[],[f19])).
% 1.43/0.58  fof(f19,plain,(
% 1.43/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.58    inference(nnf_transformation,[],[f4])).
% 1.43/0.58  fof(f4,axiom,(
% 1.43/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.58  fof(f94,plain,(
% 1.43/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,k1_xboole_0)),X0)) )),
% 1.43/0.58    inference(resolution,[],[f93,f44])).
% 1.43/0.58  fof(f44,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f24])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 1.43/0.58  fof(f23,plain,(
% 1.43/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f22,plain,(
% 1.43/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.58    inference(rectify,[],[f21])).
% 1.43/0.58  fof(f21,plain,(
% 1.43/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.43/0.58    inference(nnf_transformation,[],[f16])).
% 1.43/0.58  fof(f16,plain,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f2])).
% 1.43/0.58  fof(f2,axiom,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.58  fof(f93,plain,(
% 1.43/0.58    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f91,f86])).
% 1.43/0.58  fof(f86,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0))) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 1.43/0.58    inference(superposition,[],[f60,f72])).
% 1.43/0.58  fof(f72,plain,(
% 1.43/0.58    ( ! [X1] : (k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X1)) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.43/0.58    inference(superposition,[],[f61,f54])).
% 1.43/0.58  fof(f54,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f38,f52])).
% 1.43/0.58  fof(f52,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f36,f37])).
% 1.43/0.58  fof(f37,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f8])).
% 1.43/0.58  fof(f8,axiom,(
% 1.43/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.58  fof(f36,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,axiom,(
% 1.43/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.43/0.58  fof(f38,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f7])).
% 1.43/0.58  fof(f7,axiom,(
% 1.43/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.43/0.58  fof(f61,plain,(
% 1.43/0.58    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) )),
% 1.43/0.58    inference(resolution,[],[f30,f55])).
% 1.43/0.58  fof(f55,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f39,f52])).
% 1.43/0.58  fof(f39,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f15])).
% 1.43/0.58  fof(f15,plain,(
% 1.43/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f10])).
% 1.43/0.58  fof(f10,axiom,(
% 1.43/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.43/0.58  fof(f30,plain,(
% 1.43/0.58    v1_relat_1(sK1)),
% 1.43/0.58    inference(cnf_transformation,[],[f18])).
% 1.43/0.58  fof(f60,plain,(
% 1.43/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.43/0.58    inference(equality_resolution,[],[f46])).
% 1.43/0.58  fof(f46,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.43/0.58    inference(cnf_transformation,[],[f29])).
% 1.43/0.58  fof(f29,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.43/0.58  fof(f28,plain,(
% 1.43/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f27,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(rectify,[],[f26])).
% 1.43/0.58  fof(f26,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(flattening,[],[f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.43/0.58    inference(nnf_transformation,[],[f3])).
% 1.43/0.58  fof(f3,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.43/0.58  fof(f91,plain,(
% 1.43/0.58    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,k1_xboole_0))) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 1.43/0.58    inference(superposition,[],[f59,f85])).
% 1.43/0.58  fof(f85,plain,(
% 1.43/0.58    k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.43/0.58    inference(superposition,[],[f72,f34])).
% 1.43/0.58  fof(f59,plain,(
% 1.43/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.43/0.58    inference(equality_resolution,[],[f47])).
% 1.43/0.58  fof(f47,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.43/0.58    inference(cnf_transformation,[],[f29])).
% 1.43/0.58  fof(f455,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0)) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f444])).
% 1.43/0.58  fof(f444,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 | r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0)) )),
% 1.43/0.58    inference(resolution,[],[f181,f50])).
% 1.43/0.58  fof(f50,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f29])).
% 1.43/0.58  fof(f181,plain,(
% 1.43/0.58    ( ! [X2,X3,X1] : (r2_hidden(sK3(X1,X2,k1_xboole_0),X3) | k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X3)) )),
% 1.43/0.58    inference(resolution,[],[f139,f43])).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f24])).
% 1.43/0.58  fof(f139,plain,(
% 1.43/0.58    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,k1_xboole_0),X1) | k1_xboole_0 = k4_xboole_0(X1,X2)) )),
% 1.43/0.58    inference(forward_demodulation,[],[f134,f126])).
% 1.43/0.58  fof(f134,plain,(
% 1.43/0.58    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,k1_xboole_0),X1) | k4_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))) )),
% 1.43/0.58    inference(backward_demodulation,[],[f95,f126])).
% 1.43/0.58  fof(f95,plain,(
% 1.43/0.58    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),X1) | k4_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))) )),
% 1.43/0.58    inference(resolution,[],[f93,f49])).
% 1.43/0.58  fof(f49,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.43/0.58    inference(cnf_transformation,[],[f29])).
% 1.43/0.58  fof(f78,plain,(
% 1.43/0.58    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1)))) )),
% 1.43/0.58    inference(superposition,[],[f73,f54])).
% 1.43/0.58  fof(f73,plain,(
% 1.43/0.58    ( ! [X2] : (k1_setfam_1(k1_enumset1(X2,X2,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X2))) )),
% 1.43/0.58    inference(superposition,[],[f61,f53])).
% 1.43/0.58  fof(f53,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f35,f52,f52])).
% 1.43/0.58  fof(f35,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f1])).
% 1.43/0.58  fof(f1,axiom,(
% 1.43/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.58  % SZS output end Proof for theBenchmark
% 1.43/0.58  % (32001)------------------------------
% 1.43/0.58  % (32001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (32001)Termination reason: Refutation
% 1.43/0.58  
% 1.43/0.58  % (32001)Memory used [KB]: 11129
% 1.43/0.58  % (32001)Time elapsed: 0.184 s
% 1.43/0.58  % (32001)------------------------------
% 1.43/0.58  % (32001)------------------------------
% 1.43/0.59  % (31992)Success in time 0.227 s
%------------------------------------------------------------------------------
