%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 711 expanded)
%              Number of leaves         :   10 ( 181 expanded)
%              Depth                    :   26
%              Number of atoms          :  298 (3600 expanded)
%              Number of equality atoms :  138 (1275 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f108,f101])).

fof(f101,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f31,f99])).

fof(f99,plain,(
    v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f97,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

fof(f97,plain,
    ( v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f96,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

fof(f96,plain,(
    r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f94,f51])).

fof(f51,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f94,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f46,f92])).

fof(f92,plain,(
    k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f91,f66])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f64,f31])).

fof(f64,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f63,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f59,f48])).

fof(f59,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK0),X0)
      | v3_relat_1(sK0)
      | k1_xboole_0 = sK3(k2_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f29,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | k1_xboole_0 = X2
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,
    ( k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f87,f65])).

fof(f65,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f64,f30])).

fof(f30,plain,
    ( ~ v3_relat_1(sK0)
    | r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f77,f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ) ),
    inference(resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f67,plain,
    ( k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v3_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f31,plain,
    ( ~ v3_relat_1(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f108,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f107,f100])).

fof(f100,plain,(
    r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f30,f99])).

fof(f107,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f98,f56])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f96,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16320)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (16319)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (16324)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16325)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (16330)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (16329)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (16324)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f31,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    v3_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v1_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ((k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0)) => ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) => (k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f96,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f41,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (((v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) & (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(rectify,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(nnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(superposition,[],[f46,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f91,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(resolution,[],[f64,f31])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v3_relat_1(sK0) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f28])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v3_relat_1(sK0) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    v3_relat_1(sK0) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f59,f48])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),X0) | v3_relat_1(sK0) | k1_xboole_0 = sK3(k2_relat_1(sK0),X0)) )),
% 0.21/0.52    inference(resolution,[],[f29,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK0)) | k1_xboole_0 = X2 | v3_relat_1(sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(resolution,[],[f87,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_relat_1(sK0)) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(resolution,[],[f64,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ~v3_relat_1(sK0) | r2_hidden(sK1,k2_relat_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(resolution,[],[f77,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.21/0.52    inference(equality_resolution,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X0,k2_relat_1(sK0)) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) )),
% 0.21/0.52    inference(resolution,[],[f68,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f28])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    k1_xboole_0 = sK3(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f64,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f47])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v3_relat_1(sK0) | k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    k1_xboole_0 = sK1),
% 0.21/0.52    inference(resolution,[],[f107,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f30,f99])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(resolution,[],[f98,f56])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X0,k2_relat_1(sK0))) )),
% 0.21/0.52    inference(resolution,[],[f96,f44])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16324)------------------------------
% 0.21/0.52  % (16324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16324)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16324)Memory used [KB]: 6268
% 0.21/0.52  % (16324)Time elapsed: 0.108 s
% 0.21/0.52  % (16324)------------------------------
% 0.21/0.52  % (16324)------------------------------
% 0.21/0.52  % (16330)Refutation not found, incomplete strategy% (16330)------------------------------
% 0.21/0.52  % (16330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16330)Memory used [KB]: 10618
% 0.21/0.52  % (16330)Time elapsed: 0.106 s
% 0.21/0.52  % (16330)------------------------------
% 0.21/0.52  % (16330)------------------------------
% 0.21/0.52  % (16329)Refutation not found, incomplete strategy% (16329)------------------------------
% 0.21/0.52  % (16329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16329)Memory used [KB]: 10618
% 0.21/0.52  % (16329)Time elapsed: 0.106 s
% 0.21/0.52  % (16329)------------------------------
% 0.21/0.52  % (16329)------------------------------
% 1.27/0.52  % (16343)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.53  % (16344)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.53  % (16335)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.53  % (16327)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.53  % (16321)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (16342)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.53  % (16323)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (16328)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.53  % (16318)Success in time 0.172 s
%------------------------------------------------------------------------------
