%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:54 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  207 (1160 expanded)
%              Number of clauses        :   99 ( 190 expanded)
%              Number of leaves         :   28 ( 310 expanded)
%              Depth                    :   22
%              Number of atoms          :  756 (4140 expanded)
%              Number of equality atoms :  264 (1103 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f51,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f52])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X10,X8)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK6)
          | ~ r2_hidden(X0,k1_ordinal1(sK6)) )
        & ( r1_ordinal1(X0,sK6)
          | r2_hidden(X0,k1_ordinal1(sK6)) )
        & v3_ordinal1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK5,X1)
            | ~ r2_hidden(sK5,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK5,X1)
            | r2_hidden(sK5,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ~ r1_ordinal1(sK5,sK6)
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( r1_ordinal1(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) )
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f61,f63,f62])).

fof(f110,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f116,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f80,f115])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f111])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f112])).

fof(f114,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f113])).

fof(f115,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f114])).

fof(f117,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f115])).

fof(f118,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f98,f116,f117])).

fof(f126,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f110,f118])).

fof(f107,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f108,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f138,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f87])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f28,f40,f39])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f139,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f95])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK4(X0),X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK4(X0),X0)
          & r2_hidden(sK4(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f99,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f116])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f67,f116])).

fof(f128,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f122])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f116])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f124])).

fof(f109,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f64])).

fof(f127,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f109,f118])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X1 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6284,plain,
    ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7)
    | X0 = sK5
    | X1 = sK5
    | X2 = sK5
    | X6 = sK5
    | X5 = sK5
    | X4 = sK5
    | X3 = sK5
    | X7 = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_6289,plain,
    ( ~ sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_6284])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | ~ r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4442,plain,
    ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)
    | ~ r2_hidden(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6228,plain,
    ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
    | ~ r2_hidden(sK5,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(instantiation,[status(thm)],[c_4442])).

cnf(c_6231,plain,
    ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_6228])).

cnf(c_28,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_33,negated_conjecture,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_268,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_646,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_268])).

cnf(c_647,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_36,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_35,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_649,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_36,c_35])).

cnf(c_1531,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_36,c_35,c_647])).

cnf(c_3328,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1531])).

cnf(c_37,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_65,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_67,plain,
    ( v3_ordinal1(sK6) != iProver_top
    | v1_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_75,plain,
    ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_78,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_77,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_79,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_651,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_796,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,X9)
    | X10 != X1
    | X11 != X2
    | X12 != X3
    | X13 != X4
    | X14 != X5
    | X15 != X6
    | X16 != X7
    | X17 != X8
    | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_797,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_798,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_800,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != iProver_top
    | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_27,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_919,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v1_ordinal1(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_649])).

cnf(c_920,plain,
    ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ r2_hidden(sK5,sK6)
    | ~ v1_ordinal1(sK6) ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_66,plain,
    ( ~ v3_ordinal1(sK6)
    | v1_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_922,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_35,c_66])).

cnf(c_923,plain,
    ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ r2_hidden(sK5,sK6) ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_930,plain,
    ( ~ r2_hidden(sK5,sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_923,c_4])).

cnf(c_932,plain,
    ( r2_hidden(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_2566,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_2573,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3602,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3603,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3602])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_458,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_6,c_30])).

cnf(c_3878,plain,
    ( ~ r1_tarski(X0,sK5)
    | r2_hidden(X0,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v1_ordinal1(X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_3879,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3878])).

cnf(c_3881,plain,
    ( sK5 = sK6
    | r1_tarski(sK6,sK5) != iProver_top
    | r2_hidden(sK6,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v1_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3879])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3765,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r2_hidden(X0,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4002,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_3765])).

cnf(c_4003,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4002])).

cnf(c_31,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_29,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_613,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_31,c_29])).

cnf(c_4303,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_4309,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4303])).

cnf(c_4311,plain,
    ( r1_tarski(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4309])).

cnf(c_2568,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3766,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
    | X0 != X2
    | X1 != k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_3943,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r2_hidden(X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | X9 != X0
    | k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(instantiation,[status(thm)],[c_3766])).

cnf(c_5038,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3943])).

cnf(c_5039,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != X0
    | r2_hidden(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5038])).

cnf(c_5041,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6
    | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5039])).

cnf(c_5304,plain,
    ( r1_tarski(sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3328,c_37,c_38,c_67,c_75,c_78,c_79,c_651,c_800,c_932,c_2573,c_3603,c_3881,c_4003,c_4311,c_5041])).

cnf(c_3331,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3337,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3650,plain,
    ( v1_ordinal1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_3337])).

cnf(c_3656,plain,
    ( v1_ordinal1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3650])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3643,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3618,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK5)
    | X0 != sK6
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_3619,plain,
    ( X0 != sK6
    | X1 != sK5
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3618])).

cnf(c_3621,plain,
    ( sK6 != sK6
    | sK6 != sK5
    | r2_hidden(sK6,sK6) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3619])).

cnf(c_632,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_268])).

cnf(c_633,plain,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_635,plain,
    ( r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_36,c_35])).

cnf(c_34,negated_conjecture,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_270,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_34])).

cnf(c_660,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_270])).

cnf(c_661,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_663,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_36,c_35])).

cnf(c_1533,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(prop_impl,[status(thm)],[c_36,c_35,c_661])).

cnf(c_1597,plain,
    ( r1_tarski(sK5,sK6)
    | r2_hidden(sK6,sK5) ),
    inference(bin_hyper_res,[status(thm)],[c_635,c_1533])).

cnf(c_1606,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_933,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_458,c_663])).

cnf(c_934,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | r2_hidden(sK5,sK6)
    | ~ v3_ordinal1(sK6)
    | ~ v1_ordinal1(sK5)
    | sK6 = sK5 ),
    inference(unflattening,[status(thm)],[c_933])).

cnf(c_936,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ v1_ordinal1(sK5)
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_934,c_35,c_930])).

cnf(c_862,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v1_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_27,c_32])).

cnf(c_863,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_865,plain,
    ( r2_hidden(sK6,sK6) != iProver_top
    | v1_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_69,plain,
    ( sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6289,c_6231,c_5304,c_3656,c_3643,c_3621,c_1606,c_936,c_930,c_865,c_78,c_75,c_69,c_67,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.25/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.98  
% 3.25/0.98  ------  iProver source info
% 3.25/0.98  
% 3.25/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.98  git: non_committed_changes: false
% 3.25/0.98  git: last_make_outside_of_git: false
% 3.25/0.98  
% 3.25/0.98  ------ 
% 3.25/0.98  
% 3.25/0.98  ------ Input Options
% 3.25/0.98  
% 3.25/0.98  --out_options                           all
% 3.25/0.98  --tptp_safe_out                         true
% 3.25/0.98  --problem_path                          ""
% 3.25/0.98  --include_path                          ""
% 3.25/0.98  --clausifier                            res/vclausify_rel
% 3.25/0.98  --clausifier_options                    --mode clausify
% 3.25/0.98  --stdin                                 false
% 3.25/0.98  --stats_out                             all
% 3.25/0.98  
% 3.25/0.98  ------ General Options
% 3.25/0.98  
% 3.25/0.98  --fof                                   false
% 3.25/0.98  --time_out_real                         305.
% 3.25/0.98  --time_out_virtual                      -1.
% 3.25/0.98  --symbol_type_check                     false
% 3.25/0.98  --clausify_out                          false
% 3.25/0.98  --sig_cnt_out                           false
% 3.25/0.98  --trig_cnt_out                          false
% 3.25/0.98  --trig_cnt_out_tolerance                1.
% 3.25/0.98  --trig_cnt_out_sk_spl                   false
% 3.25/0.98  --abstr_cl_out                          false
% 3.25/0.98  
% 3.25/0.98  ------ Global Options
% 3.25/0.98  
% 3.25/0.98  --schedule                              default
% 3.25/0.98  --add_important_lit                     false
% 3.25/0.98  --prop_solver_per_cl                    1000
% 3.25/0.98  --min_unsat_core                        false
% 3.25/0.98  --soft_assumptions                      false
% 3.25/0.98  --soft_lemma_size                       3
% 3.25/0.98  --prop_impl_unit_size                   0
% 3.25/0.98  --prop_impl_unit                        []
% 3.25/0.98  --share_sel_clauses                     true
% 3.25/0.98  --reset_solvers                         false
% 3.25/0.98  --bc_imp_inh                            [conj_cone]
% 3.25/0.98  --conj_cone_tolerance                   3.
% 3.25/0.98  --extra_neg_conj                        none
% 3.25/0.98  --large_theory_mode                     true
% 3.25/0.98  --prolific_symb_bound                   200
% 3.25/0.98  --lt_threshold                          2000
% 3.25/0.98  --clause_weak_htbl                      true
% 3.25/0.98  --gc_record_bc_elim                     false
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing Options
% 3.25/0.98  
% 3.25/0.98  --preprocessing_flag                    true
% 3.25/0.98  --time_out_prep_mult                    0.1
% 3.25/0.98  --splitting_mode                        input
% 3.25/0.98  --splitting_grd                         true
% 3.25/0.98  --splitting_cvd                         false
% 3.25/0.98  --splitting_cvd_svl                     false
% 3.25/0.98  --splitting_nvd                         32
% 3.25/0.98  --sub_typing                            true
% 3.25/0.98  --prep_gs_sim                           true
% 3.25/0.98  --prep_unflatten                        true
% 3.25/0.98  --prep_res_sim                          true
% 3.25/0.98  --prep_upred                            true
% 3.25/0.98  --prep_sem_filter                       exhaustive
% 3.25/0.98  --prep_sem_filter_out                   false
% 3.25/0.98  --pred_elim                             true
% 3.25/0.98  --res_sim_input                         true
% 3.25/0.98  --eq_ax_congr_red                       true
% 3.25/0.98  --pure_diseq_elim                       true
% 3.25/0.98  --brand_transform                       false
% 3.25/0.98  --non_eq_to_eq                          false
% 3.25/0.98  --prep_def_merge                        true
% 3.25/0.98  --prep_def_merge_prop_impl              false
% 3.25/0.98  --prep_def_merge_mbd                    true
% 3.25/0.98  --prep_def_merge_tr_red                 false
% 3.25/0.98  --prep_def_merge_tr_cl                  false
% 3.25/0.98  --smt_preprocessing                     true
% 3.25/0.98  --smt_ac_axioms                         fast
% 3.25/0.98  --preprocessed_out                      false
% 3.25/0.98  --preprocessed_stats                    false
% 3.25/0.98  
% 3.25/0.98  ------ Abstraction refinement Options
% 3.25/0.98  
% 3.25/0.98  --abstr_ref                             []
% 3.25/0.98  --abstr_ref_prep                        false
% 3.25/0.98  --abstr_ref_until_sat                   false
% 3.25/0.98  --abstr_ref_sig_restrict                funpre
% 3.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.98  --abstr_ref_under                       []
% 3.25/0.98  
% 3.25/0.98  ------ SAT Options
% 3.25/0.98  
% 3.25/0.98  --sat_mode                              false
% 3.25/0.98  --sat_fm_restart_options                ""
% 3.25/0.98  --sat_gr_def                            false
% 3.25/0.98  --sat_epr_types                         true
% 3.25/0.98  --sat_non_cyclic_types                  false
% 3.25/0.98  --sat_finite_models                     false
% 3.25/0.98  --sat_fm_lemmas                         false
% 3.25/0.98  --sat_fm_prep                           false
% 3.25/0.98  --sat_fm_uc_incr                        true
% 3.25/0.98  --sat_out_model                         small
% 3.25/0.98  --sat_out_clauses                       false
% 3.25/0.98  
% 3.25/0.98  ------ QBF Options
% 3.25/0.98  
% 3.25/0.98  --qbf_mode                              false
% 3.25/0.98  --qbf_elim_univ                         false
% 3.25/0.98  --qbf_dom_inst                          none
% 3.25/0.98  --qbf_dom_pre_inst                      false
% 3.25/0.98  --qbf_sk_in                             false
% 3.25/0.98  --qbf_pred_elim                         true
% 3.25/0.98  --qbf_split                             512
% 3.25/0.98  
% 3.25/0.98  ------ BMC1 Options
% 3.25/0.98  
% 3.25/0.98  --bmc1_incremental                      false
% 3.25/0.98  --bmc1_axioms                           reachable_all
% 3.25/0.98  --bmc1_min_bound                        0
% 3.25/0.98  --bmc1_max_bound                        -1
% 3.25/0.98  --bmc1_max_bound_default                -1
% 3.25/0.98  --bmc1_symbol_reachability              true
% 3.25/0.98  --bmc1_property_lemmas                  false
% 3.25/0.98  --bmc1_k_induction                      false
% 3.25/0.98  --bmc1_non_equiv_states                 false
% 3.25/0.98  --bmc1_deadlock                         false
% 3.25/0.98  --bmc1_ucm                              false
% 3.25/0.98  --bmc1_add_unsat_core                   none
% 3.25/0.98  --bmc1_unsat_core_children              false
% 3.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.98  --bmc1_out_stat                         full
% 3.25/0.98  --bmc1_ground_init                      false
% 3.25/0.98  --bmc1_pre_inst_next_state              false
% 3.25/0.98  --bmc1_pre_inst_state                   false
% 3.25/0.98  --bmc1_pre_inst_reach_state             false
% 3.25/0.98  --bmc1_out_unsat_core                   false
% 3.25/0.98  --bmc1_aig_witness_out                  false
% 3.25/0.98  --bmc1_verbose                          false
% 3.25/0.98  --bmc1_dump_clauses_tptp                false
% 3.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.98  --bmc1_dump_file                        -
% 3.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.98  --bmc1_ucm_extend_mode                  1
% 3.25/0.98  --bmc1_ucm_init_mode                    2
% 3.25/0.98  --bmc1_ucm_cone_mode                    none
% 3.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.98  --bmc1_ucm_relax_model                  4
% 3.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.98  --bmc1_ucm_layered_model                none
% 3.25/0.98  --bmc1_ucm_max_lemma_size               10
% 3.25/0.98  
% 3.25/0.98  ------ AIG Options
% 3.25/0.98  
% 3.25/0.98  --aig_mode                              false
% 3.25/0.98  
% 3.25/0.98  ------ Instantiation Options
% 3.25/0.98  
% 3.25/0.98  --instantiation_flag                    true
% 3.25/0.98  --inst_sos_flag                         false
% 3.25/0.98  --inst_sos_phase                        true
% 3.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel_side                     num_symb
% 3.25/0.98  --inst_solver_per_active                1400
% 3.25/0.98  --inst_solver_calls_frac                1.
% 3.25/0.98  --inst_passive_queue_type               priority_queues
% 3.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.98  --inst_passive_queues_freq              [25;2]
% 3.25/0.98  --inst_dismatching                      true
% 3.25/0.98  --inst_eager_unprocessed_to_passive     true
% 3.25/0.98  --inst_prop_sim_given                   true
% 3.25/0.98  --inst_prop_sim_new                     false
% 3.25/0.98  --inst_subs_new                         false
% 3.25/0.98  --inst_eq_res_simp                      false
% 3.25/0.98  --inst_subs_given                       false
% 3.25/0.98  --inst_orphan_elimination               true
% 3.25/0.98  --inst_learning_loop_flag               true
% 3.25/0.98  --inst_learning_start                   3000
% 3.25/0.98  --inst_learning_factor                  2
% 3.25/0.98  --inst_start_prop_sim_after_learn       3
% 3.25/0.98  --inst_sel_renew                        solver
% 3.25/0.98  --inst_lit_activity_flag                true
% 3.25/0.98  --inst_restr_to_given                   false
% 3.25/0.98  --inst_activity_threshold               500
% 3.25/0.98  --inst_out_proof                        true
% 3.25/0.98  
% 3.25/0.98  ------ Resolution Options
% 3.25/0.98  
% 3.25/0.98  --resolution_flag                       true
% 3.25/0.98  --res_lit_sel                           adaptive
% 3.25/0.98  --res_lit_sel_side                      none
% 3.25/0.98  --res_ordering                          kbo
% 3.25/0.98  --res_to_prop_solver                    active
% 3.25/0.98  --res_prop_simpl_new                    false
% 3.25/0.98  --res_prop_simpl_given                  true
% 3.25/0.98  --res_passive_queue_type                priority_queues
% 3.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.98  --res_passive_queues_freq               [15;5]
% 3.25/0.98  --res_forward_subs                      full
% 3.25/0.98  --res_backward_subs                     full
% 3.25/0.98  --res_forward_subs_resolution           true
% 3.25/0.98  --res_backward_subs_resolution          true
% 3.25/0.98  --res_orphan_elimination                true
% 3.25/0.98  --res_time_limit                        2.
% 3.25/0.98  --res_out_proof                         true
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Options
% 3.25/0.98  
% 3.25/0.98  --superposition_flag                    true
% 3.25/0.98  --sup_passive_queue_type                priority_queues
% 3.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.98  --demod_completeness_check              fast
% 3.25/0.98  --demod_use_ground                      true
% 3.25/0.98  --sup_to_prop_solver                    passive
% 3.25/0.98  --sup_prop_simpl_new                    true
% 3.25/0.98  --sup_prop_simpl_given                  true
% 3.25/0.98  --sup_fun_splitting                     false
% 3.25/0.98  --sup_smt_interval                      50000
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Simplification Setup
% 3.25/0.98  
% 3.25/0.98  --sup_indices_passive                   []
% 3.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_full_bw                           [BwDemod]
% 3.25/0.98  --sup_immed_triv                        [TrivRules]
% 3.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_immed_bw_main                     []
% 3.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  
% 3.25/0.98  ------ Combination Options
% 3.25/0.98  
% 3.25/0.98  --comb_res_mult                         3
% 3.25/0.98  --comb_sup_mult                         2
% 3.25/0.98  --comb_inst_mult                        10
% 3.25/0.98  
% 3.25/0.98  ------ Debug Options
% 3.25/0.98  
% 3.25/0.98  --dbg_backtrace                         false
% 3.25/0.98  --dbg_dump_prop_clauses                 false
% 3.25/0.98  --dbg_dump_prop_clauses_file            -
% 3.25/0.98  --dbg_out_stat                          false
% 3.25/0.98  ------ Parsing...
% 3.25/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.98  ------ Proving...
% 3.25/0.98  ------ Problem Properties 
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  clauses                                 35
% 3.25/0.98  conjectures                             2
% 3.25/0.98  EPR                                     19
% 3.25/0.98  Horn                                    26
% 3.25/0.98  unary                                   12
% 3.25/0.98  binary                                  11
% 3.25/0.98  lits                                    80
% 3.25/0.98  lits eq                                 14
% 3.25/0.98  fd_pure                                 0
% 3.25/0.98  fd_pseudo                               0
% 3.25/0.98  fd_cond                                 0
% 3.25/0.98  fd_pseudo_cond                          6
% 3.25/0.98  AC symbols                              0
% 3.25/0.98  
% 3.25/0.98  ------ Schedule dynamic 5 is on 
% 3.25/0.98  
% 3.25/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  ------ 
% 3.25/0.98  Current options:
% 3.25/0.98  ------ 
% 3.25/0.98  
% 3.25/0.98  ------ Input Options
% 3.25/0.98  
% 3.25/0.98  --out_options                           all
% 3.25/0.98  --tptp_safe_out                         true
% 3.25/0.98  --problem_path                          ""
% 3.25/0.98  --include_path                          ""
% 3.25/0.98  --clausifier                            res/vclausify_rel
% 3.25/0.98  --clausifier_options                    --mode clausify
% 3.25/0.98  --stdin                                 false
% 3.25/0.98  --stats_out                             all
% 3.25/0.98  
% 3.25/0.98  ------ General Options
% 3.25/0.98  
% 3.25/0.98  --fof                                   false
% 3.25/0.98  --time_out_real                         305.
% 3.25/0.98  --time_out_virtual                      -1.
% 3.25/0.98  --symbol_type_check                     false
% 3.25/0.98  --clausify_out                          false
% 3.25/0.98  --sig_cnt_out                           false
% 3.25/0.98  --trig_cnt_out                          false
% 3.25/0.98  --trig_cnt_out_tolerance                1.
% 3.25/0.98  --trig_cnt_out_sk_spl                   false
% 3.25/0.98  --abstr_cl_out                          false
% 3.25/0.98  
% 3.25/0.98  ------ Global Options
% 3.25/0.98  
% 3.25/0.98  --schedule                              default
% 3.25/0.98  --add_important_lit                     false
% 3.25/0.98  --prop_solver_per_cl                    1000
% 3.25/0.98  --min_unsat_core                        false
% 3.25/0.98  --soft_assumptions                      false
% 3.25/0.98  --soft_lemma_size                       3
% 3.25/0.98  --prop_impl_unit_size                   0
% 3.25/0.98  --prop_impl_unit                        []
% 3.25/0.98  --share_sel_clauses                     true
% 3.25/0.98  --reset_solvers                         false
% 3.25/0.98  --bc_imp_inh                            [conj_cone]
% 3.25/0.98  --conj_cone_tolerance                   3.
% 3.25/0.98  --extra_neg_conj                        none
% 3.25/0.98  --large_theory_mode                     true
% 3.25/0.98  --prolific_symb_bound                   200
% 3.25/0.98  --lt_threshold                          2000
% 3.25/0.98  --clause_weak_htbl                      true
% 3.25/0.98  --gc_record_bc_elim                     false
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing Options
% 3.25/0.98  
% 3.25/0.98  --preprocessing_flag                    true
% 3.25/0.98  --time_out_prep_mult                    0.1
% 3.25/0.98  --splitting_mode                        input
% 3.25/0.98  --splitting_grd                         true
% 3.25/0.98  --splitting_cvd                         false
% 3.25/0.98  --splitting_cvd_svl                     false
% 3.25/0.98  --splitting_nvd                         32
% 3.25/0.98  --sub_typing                            true
% 3.25/0.98  --prep_gs_sim                           true
% 3.25/0.98  --prep_unflatten                        true
% 3.25/0.98  --prep_res_sim                          true
% 3.25/0.98  --prep_upred                            true
% 3.25/0.98  --prep_sem_filter                       exhaustive
% 3.25/0.98  --prep_sem_filter_out                   false
% 3.25/0.98  --pred_elim                             true
% 3.25/0.98  --res_sim_input                         true
% 3.25/0.98  --eq_ax_congr_red                       true
% 3.25/0.98  --pure_diseq_elim                       true
% 3.25/0.98  --brand_transform                       false
% 3.25/0.98  --non_eq_to_eq                          false
% 3.25/0.98  --prep_def_merge                        true
% 3.25/0.98  --prep_def_merge_prop_impl              false
% 3.25/0.98  --prep_def_merge_mbd                    true
% 3.25/0.98  --prep_def_merge_tr_red                 false
% 3.25/0.98  --prep_def_merge_tr_cl                  false
% 3.25/0.98  --smt_preprocessing                     true
% 3.25/0.98  --smt_ac_axioms                         fast
% 3.25/0.98  --preprocessed_out                      false
% 3.25/0.98  --preprocessed_stats                    false
% 3.25/0.98  
% 3.25/0.98  ------ Abstraction refinement Options
% 3.25/0.98  
% 3.25/0.98  --abstr_ref                             []
% 3.25/0.98  --abstr_ref_prep                        false
% 3.25/0.98  --abstr_ref_until_sat                   false
% 3.25/0.98  --abstr_ref_sig_restrict                funpre
% 3.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.98  --abstr_ref_under                       []
% 3.25/0.98  
% 3.25/0.98  ------ SAT Options
% 3.25/0.98  
% 3.25/0.98  --sat_mode                              false
% 3.25/0.98  --sat_fm_restart_options                ""
% 3.25/0.98  --sat_gr_def                            false
% 3.25/0.98  --sat_epr_types                         true
% 3.25/0.98  --sat_non_cyclic_types                  false
% 3.25/0.98  --sat_finite_models                     false
% 3.25/0.98  --sat_fm_lemmas                         false
% 3.25/0.98  --sat_fm_prep                           false
% 3.25/0.98  --sat_fm_uc_incr                        true
% 3.25/0.98  --sat_out_model                         small
% 3.25/0.98  --sat_out_clauses                       false
% 3.25/0.98  
% 3.25/0.98  ------ QBF Options
% 3.25/0.98  
% 3.25/0.98  --qbf_mode                              false
% 3.25/0.98  --qbf_elim_univ                         false
% 3.25/0.98  --qbf_dom_inst                          none
% 3.25/0.98  --qbf_dom_pre_inst                      false
% 3.25/0.98  --qbf_sk_in                             false
% 3.25/0.98  --qbf_pred_elim                         true
% 3.25/0.98  --qbf_split                             512
% 3.25/0.98  
% 3.25/0.98  ------ BMC1 Options
% 3.25/0.98  
% 3.25/0.98  --bmc1_incremental                      false
% 3.25/0.98  --bmc1_axioms                           reachable_all
% 3.25/0.98  --bmc1_min_bound                        0
% 3.25/0.98  --bmc1_max_bound                        -1
% 3.25/0.98  --bmc1_max_bound_default                -1
% 3.25/0.98  --bmc1_symbol_reachability              true
% 3.25/0.98  --bmc1_property_lemmas                  false
% 3.25/0.98  --bmc1_k_induction                      false
% 3.25/0.98  --bmc1_non_equiv_states                 false
% 3.25/0.98  --bmc1_deadlock                         false
% 3.25/0.98  --bmc1_ucm                              false
% 3.25/0.98  --bmc1_add_unsat_core                   none
% 3.25/0.98  --bmc1_unsat_core_children              false
% 3.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.98  --bmc1_out_stat                         full
% 3.25/0.98  --bmc1_ground_init                      false
% 3.25/0.98  --bmc1_pre_inst_next_state              false
% 3.25/0.98  --bmc1_pre_inst_state                   false
% 3.25/0.98  --bmc1_pre_inst_reach_state             false
% 3.25/0.98  --bmc1_out_unsat_core                   false
% 3.25/0.98  --bmc1_aig_witness_out                  false
% 3.25/0.98  --bmc1_verbose                          false
% 3.25/0.98  --bmc1_dump_clauses_tptp                false
% 3.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.98  --bmc1_dump_file                        -
% 3.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.98  --bmc1_ucm_extend_mode                  1
% 3.25/0.98  --bmc1_ucm_init_mode                    2
% 3.25/0.98  --bmc1_ucm_cone_mode                    none
% 3.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.98  --bmc1_ucm_relax_model                  4
% 3.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.98  --bmc1_ucm_layered_model                none
% 3.25/0.98  --bmc1_ucm_max_lemma_size               10
% 3.25/0.98  
% 3.25/0.98  ------ AIG Options
% 3.25/0.98  
% 3.25/0.98  --aig_mode                              false
% 3.25/0.98  
% 3.25/0.98  ------ Instantiation Options
% 3.25/0.98  
% 3.25/0.98  --instantiation_flag                    true
% 3.25/0.98  --inst_sos_flag                         false
% 3.25/0.98  --inst_sos_phase                        true
% 3.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.98  --inst_lit_sel_side                     none
% 3.25/0.98  --inst_solver_per_active                1400
% 3.25/0.98  --inst_solver_calls_frac                1.
% 3.25/0.98  --inst_passive_queue_type               priority_queues
% 3.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.98  --inst_passive_queues_freq              [25;2]
% 3.25/0.98  --inst_dismatching                      true
% 3.25/0.98  --inst_eager_unprocessed_to_passive     true
% 3.25/0.98  --inst_prop_sim_given                   true
% 3.25/0.98  --inst_prop_sim_new                     false
% 3.25/0.98  --inst_subs_new                         false
% 3.25/0.98  --inst_eq_res_simp                      false
% 3.25/0.98  --inst_subs_given                       false
% 3.25/0.98  --inst_orphan_elimination               true
% 3.25/0.98  --inst_learning_loop_flag               true
% 3.25/0.98  --inst_learning_start                   3000
% 3.25/0.98  --inst_learning_factor                  2
% 3.25/0.98  --inst_start_prop_sim_after_learn       3
% 3.25/0.98  --inst_sel_renew                        solver
% 3.25/0.98  --inst_lit_activity_flag                true
% 3.25/0.98  --inst_restr_to_given                   false
% 3.25/0.98  --inst_activity_threshold               500
% 3.25/0.98  --inst_out_proof                        true
% 3.25/0.98  
% 3.25/0.98  ------ Resolution Options
% 3.25/0.98  
% 3.25/0.98  --resolution_flag                       false
% 3.25/0.98  --res_lit_sel                           adaptive
% 3.25/0.98  --res_lit_sel_side                      none
% 3.25/0.98  --res_ordering                          kbo
% 3.25/0.98  --res_to_prop_solver                    active
% 3.25/0.98  --res_prop_simpl_new                    false
% 3.25/0.98  --res_prop_simpl_given                  true
% 3.25/0.98  --res_passive_queue_type                priority_queues
% 3.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.98  --res_passive_queues_freq               [15;5]
% 3.25/0.98  --res_forward_subs                      full
% 3.25/0.98  --res_backward_subs                     full
% 3.25/0.98  --res_forward_subs_resolution           true
% 3.25/0.98  --res_backward_subs_resolution          true
% 3.25/0.98  --res_orphan_elimination                true
% 3.25/0.98  --res_time_limit                        2.
% 3.25/0.98  --res_out_proof                         true
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Options
% 3.25/0.98  
% 3.25/0.98  --superposition_flag                    true
% 3.25/0.98  --sup_passive_queue_type                priority_queues
% 3.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.98  --demod_completeness_check              fast
% 3.25/0.98  --demod_use_ground                      true
% 3.25/0.98  --sup_to_prop_solver                    passive
% 3.25/0.98  --sup_prop_simpl_new                    true
% 3.25/0.98  --sup_prop_simpl_given                  true
% 3.25/0.98  --sup_fun_splitting                     false
% 3.25/0.98  --sup_smt_interval                      50000
% 3.25/0.98  
% 3.25/0.98  ------ Superposition Simplification Setup
% 3.25/0.98  
% 3.25/0.98  --sup_indices_passive                   []
% 3.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_full_bw                           [BwDemod]
% 3.25/0.98  --sup_immed_triv                        [TrivRules]
% 3.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_immed_bw_main                     []
% 3.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.98  
% 3.25/0.98  ------ Combination Options
% 3.25/0.98  
% 3.25/0.98  --comb_res_mult                         3
% 3.25/0.98  --comb_sup_mult                         2
% 3.25/0.98  --comb_inst_mult                        10
% 3.25/0.98  
% 3.25/0.98  ------ Debug Options
% 3.25/0.98  
% 3.25/0.98  --dbg_backtrace                         false
% 3.25/0.98  --dbg_dump_prop_clauses                 false
% 3.25/0.98  --dbg_dump_prop_clauses_file            -
% 3.25/0.98  --dbg_out_stat                          false
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  ------ Proving...
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  % SZS status Theorem for theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  fof(f39,plain,(
% 3.25/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 3.25/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.25/0.98  
% 3.25/0.98  fof(f51,plain,(
% 3.25/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.25/0.98    inference(nnf_transformation,[],[f39])).
% 3.25/0.98  
% 3.25/0.98  fof(f52,plain,(
% 3.25/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.25/0.98    inference(flattening,[],[f51])).
% 3.25/0.98  
% 3.25/0.98  fof(f53,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(rectify,[],[f52])).
% 3.25/0.98  
% 3.25/0.98  fof(f86,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f53])).
% 3.25/0.98  
% 3.25/0.98  fof(f40,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.25/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.25/0.98  
% 3.25/0.98  fof(f47,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(nnf_transformation,[],[f40])).
% 3.25/0.98  
% 3.25/0.98  fof(f48,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(rectify,[],[f47])).
% 3.25/0.98  
% 3.25/0.98  fof(f49,plain,(
% 3.25/0.98    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f50,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 3.25/0.98  
% 3.25/0.98  fof(f82,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f50])).
% 3.25/0.98  
% 3.25/0.98  fof(f17,axiom,(
% 3.25/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f31,plain,(
% 3.25/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.25/0.98    inference(ennf_transformation,[],[f17])).
% 3.25/0.98  
% 3.25/0.98  fof(f32,plain,(
% 3.25/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.25/0.98    inference(flattening,[],[f31])).
% 3.25/0.98  
% 3.25/0.98  fof(f59,plain,(
% 3.25/0.98    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.25/0.98    inference(nnf_transformation,[],[f32])).
% 3.25/0.98  
% 3.25/0.98  fof(f103,plain,(
% 3.25/0.98    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f59])).
% 3.25/0.98  
% 3.25/0.98  fof(f21,conjecture,(
% 3.25/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f22,negated_conjecture,(
% 3.25/0.98    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.25/0.98    inference(negated_conjecture,[],[f21])).
% 3.25/0.98  
% 3.25/0.98  fof(f38,plain,(
% 3.25/0.98    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.25/0.98    inference(ennf_transformation,[],[f22])).
% 3.25/0.98  
% 3.25/0.98  fof(f60,plain,(
% 3.25/0.98    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.25/0.98    inference(nnf_transformation,[],[f38])).
% 3.25/0.98  
% 3.25/0.98  fof(f61,plain,(
% 3.25/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.25/0.98    inference(flattening,[],[f60])).
% 3.25/0.98  
% 3.25/0.98  fof(f63,plain,(
% 3.25/0.98    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK6) | ~r2_hidden(X0,k1_ordinal1(sK6))) & (r1_ordinal1(X0,sK6) | r2_hidden(X0,k1_ordinal1(sK6))) & v3_ordinal1(sK6))) )),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f62,plain,(
% 3.25/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK5,X1) | ~r2_hidden(sK5,k1_ordinal1(X1))) & (r1_ordinal1(sK5,X1) | r2_hidden(sK5,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK5))),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f64,plain,(
% 3.25/0.98    ((~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))) & v3_ordinal1(sK6)) & v3_ordinal1(sK5)),
% 3.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f61,f63,f62])).
% 3.25/0.98  
% 3.25/0.98  fof(f110,plain,(
% 3.25/0.98    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 3.25/0.98    inference(cnf_transformation,[],[f64])).
% 3.25/0.98  
% 3.25/0.98  fof(f15,axiom,(
% 3.25/0.98    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f98,plain,(
% 3.25/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f15])).
% 3.25/0.98  
% 3.25/0.98  fof(f11,axiom,(
% 3.25/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f80,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.25/0.98    inference(cnf_transformation,[],[f11])).
% 3.25/0.98  
% 3.25/0.98  fof(f116,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.25/0.98    inference(definition_unfolding,[],[f80,f115])).
% 3.25/0.98  
% 3.25/0.98  fof(f3,axiom,(
% 3.25/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f72,plain,(
% 3.25/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f3])).
% 3.25/0.98  
% 3.25/0.98  fof(f4,axiom,(
% 3.25/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f73,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f4])).
% 3.25/0.98  
% 3.25/0.98  fof(f5,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f74,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f5])).
% 3.25/0.98  
% 3.25/0.98  fof(f6,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f75,plain,(
% 3.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f6])).
% 3.25/0.98  
% 3.25/0.98  fof(f7,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f76,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f7])).
% 3.25/0.98  
% 3.25/0.98  fof(f8,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f77,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f8])).
% 3.25/0.98  
% 3.25/0.98  fof(f9,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f78,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f9])).
% 3.25/0.98  
% 3.25/0.98  fof(f111,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f77,f78])).
% 3.25/0.98  
% 3.25/0.98  fof(f112,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f76,f111])).
% 3.25/0.98  
% 3.25/0.98  fof(f113,plain,(
% 3.25/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f75,f112])).
% 3.25/0.98  
% 3.25/0.98  fof(f114,plain,(
% 3.25/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f74,f113])).
% 3.25/0.98  
% 3.25/0.98  fof(f115,plain,(
% 3.25/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f73,f114])).
% 3.25/0.98  
% 3.25/0.98  fof(f117,plain,(
% 3.25/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f72,f115])).
% 3.25/0.98  
% 3.25/0.98  fof(f118,plain,(
% 3.25/0.98    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.25/0.98    inference(definition_unfolding,[],[f98,f116,f117])).
% 3.25/0.98  
% 3.25/0.98  fof(f126,plain,(
% 3.25/0.98    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 3.25/0.98    inference(definition_unfolding,[],[f110,f118])).
% 3.25/0.98  
% 3.25/0.98  fof(f107,plain,(
% 3.25/0.98    v3_ordinal1(sK5)),
% 3.25/0.98    inference(cnf_transformation,[],[f64])).
% 3.25/0.98  
% 3.25/0.98  fof(f108,plain,(
% 3.25/0.98    v3_ordinal1(sK6)),
% 3.25/0.98    inference(cnf_transformation,[],[f64])).
% 3.25/0.98  
% 3.25/0.98  fof(f14,axiom,(
% 3.25/0.98    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f24,plain,(
% 3.25/0.98    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.25/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.25/0.98  
% 3.25/0.98  fof(f29,plain,(
% 3.25/0.98    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.25/0.98    inference(ennf_transformation,[],[f24])).
% 3.25/0.98  
% 3.25/0.98  fof(f97,plain,(
% 3.25/0.98    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f29])).
% 3.25/0.98  
% 3.25/0.98  fof(f87,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 3.25/0.98    inference(cnf_transformation,[],[f53])).
% 3.25/0.98  
% 3.25/0.98  fof(f138,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.25/0.98    inference(equality_resolution,[],[f87])).
% 3.25/0.98  
% 3.25/0.98  fof(f83,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f50])).
% 3.25/0.98  
% 3.25/0.98  fof(f13,axiom,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f28,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 3.25/0.98    inference(ennf_transformation,[],[f13])).
% 3.25/0.98  
% 3.25/0.98  fof(f41,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 3.25/0.98    inference(definition_folding,[],[f28,f40,f39])).
% 3.25/0.98  
% 3.25/0.98  fof(f54,plain,(
% 3.25/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 3.25/0.98    inference(nnf_transformation,[],[f41])).
% 3.25/0.98  
% 3.25/0.98  fof(f95,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 3.25/0.98    inference(cnf_transformation,[],[f54])).
% 3.25/0.98  
% 3.25/0.98  fof(f139,plain,(
% 3.25/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 3.25/0.98    inference(equality_resolution,[],[f95])).
% 3.25/0.98  
% 3.25/0.98  fof(f16,axiom,(
% 3.25/0.98    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f30,plain,(
% 3.25/0.98    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 3.25/0.98    inference(ennf_transformation,[],[f16])).
% 3.25/0.98  
% 3.25/0.98  fof(f55,plain,(
% 3.25/0.98    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 3.25/0.98    inference(nnf_transformation,[],[f30])).
% 3.25/0.98  
% 3.25/0.98  fof(f56,plain,(
% 3.25/0.98    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 3.25/0.98    inference(rectify,[],[f55])).
% 3.25/0.98  
% 3.25/0.98  fof(f57,plain,(
% 3.25/0.98    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK4(X0),X0) & r2_hidden(sK4(X0),X0)))),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f58,plain,(
% 3.25/0.98    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK4(X0),X0) & r2_hidden(sK4(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 3.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 3.25/0.98  
% 3.25/0.98  fof(f99,plain,(
% 3.25/0.98    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f58])).
% 3.25/0.98  
% 3.25/0.98  fof(f1,axiom,(
% 3.25/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f42,plain,(
% 3.25/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.25/0.98    inference(nnf_transformation,[],[f1])).
% 3.25/0.98  
% 3.25/0.98  fof(f43,plain,(
% 3.25/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.25/0.98    inference(flattening,[],[f42])).
% 3.25/0.98  
% 3.25/0.98  fof(f44,plain,(
% 3.25/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.25/0.98    inference(rectify,[],[f43])).
% 3.25/0.98  
% 3.25/0.98  fof(f45,plain,(
% 3.25/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.25/0.98    introduced(choice_axiom,[])).
% 3.25/0.98  
% 3.25/0.98  fof(f46,plain,(
% 3.25/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 3.25/0.98  
% 3.25/0.98  fof(f66,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f123,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.25/0.98    inference(definition_unfolding,[],[f66,f116])).
% 3.25/0.98  
% 3.25/0.98  fof(f129,plain,(
% 3.25/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.25/0.98    inference(equality_resolution,[],[f123])).
% 3.25/0.98  
% 3.25/0.98  fof(f20,axiom,(
% 3.25/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f37,plain,(
% 3.25/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.25/0.98    inference(ennf_transformation,[],[f20])).
% 3.25/0.98  
% 3.25/0.98  fof(f106,plain,(
% 3.25/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f37])).
% 3.25/0.98  
% 3.25/0.98  fof(f2,axiom,(
% 3.25/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f23,plain,(
% 3.25/0.98    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.25/0.98    inference(unused_predicate_definition_removal,[],[f2])).
% 3.25/0.98  
% 3.25/0.98  fof(f25,plain,(
% 3.25/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.25/0.98    inference(ennf_transformation,[],[f23])).
% 3.25/0.98  
% 3.25/0.98  fof(f26,plain,(
% 3.25/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.25/0.98    inference(flattening,[],[f25])).
% 3.25/0.98  
% 3.25/0.98  fof(f71,plain,(
% 3.25/0.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f26])).
% 3.25/0.98  
% 3.25/0.98  fof(f18,axiom,(
% 3.25/0.98    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f33,plain,(
% 3.25/0.98    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.25/0.98    inference(ennf_transformation,[],[f18])).
% 3.25/0.98  
% 3.25/0.98  fof(f34,plain,(
% 3.25/0.98    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.25/0.98    inference(flattening,[],[f33])).
% 3.25/0.98  
% 3.25/0.98  fof(f104,plain,(
% 3.25/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f34])).
% 3.25/0.98  
% 3.25/0.98  fof(f67,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f122,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.25/0.98    inference(definition_unfolding,[],[f67,f116])).
% 3.25/0.98  
% 3.25/0.98  fof(f128,plain,(
% 3.25/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.25/0.98    inference(equality_resolution,[],[f122])).
% 3.25/0.98  
% 3.25/0.98  fof(f19,axiom,(
% 3.25/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.98  
% 3.25/0.98  fof(f35,plain,(
% 3.25/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.25/0.98    inference(ennf_transformation,[],[f19])).
% 3.25/0.98  
% 3.25/0.98  fof(f36,plain,(
% 3.25/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.25/0.98    inference(flattening,[],[f35])).
% 3.25/0.98  
% 3.25/0.98  fof(f105,plain,(
% 3.25/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f36])).
% 3.25/0.98  
% 3.25/0.98  fof(f102,plain,(
% 3.25/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.25/0.98    inference(cnf_transformation,[],[f59])).
% 3.25/0.98  
% 3.25/0.98  fof(f65,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.25/0.98    inference(cnf_transformation,[],[f46])).
% 3.25/0.98  
% 3.25/0.98  fof(f124,plain,(
% 3.25/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.25/0.98    inference(definition_unfolding,[],[f65,f116])).
% 3.25/0.98  
% 3.25/0.98  fof(f130,plain,(
% 3.25/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.25/0.98    inference(equality_resolution,[],[f124])).
% 3.25/0.98  
% 3.25/0.98  fof(f109,plain,(
% 3.25/0.98    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 3.25/0.98    inference(cnf_transformation,[],[f64])).
% 3.25/0.98  
% 3.25/0.98  fof(f127,plain,(
% 3.25/0.98    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 3.25/0.98    inference(definition_unfolding,[],[f109,f118])).
% 3.25/0.98  
% 3.25/0.98  cnf(c_21,plain,
% 3.25/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.25/0.98      | X1 = X0
% 3.25/0.98      | X8 = X0
% 3.25/0.98      | X7 = X0
% 3.25/0.98      | X6 = X0
% 3.25/0.98      | X5 = X0
% 3.25/0.98      | X4 = X0
% 3.25/0.98      | X3 = X0
% 3.25/0.98      | X2 = X0 ),
% 3.25/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_6284,plain,
% 3.25/0.98      ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7)
% 3.25/0.98      | X0 = sK5
% 3.25/0.98      | X1 = sK5
% 3.25/0.98      | X2 = sK5
% 3.25/0.98      | X6 = sK5
% 3.25/0.98      | X5 = sK5
% 3.25/0.98      | X4 = sK5
% 3.25/0.98      | X3 = sK5
% 3.25/0.98      | X7 = sK5 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_6289,plain,
% 3.25/0.98      ( ~ sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK5 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_6284]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_12,plain,
% 3.25/0.98      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.25/0.98      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 3.25/0.98      | ~ r2_hidden(X0,X9) ),
% 3.25/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4442,plain,
% 3.25/0.98      ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)
% 3.25/0.98      | ~ r2_hidden(sK5,X0) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_6228,plain,
% 3.25/0.98      ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
% 3.25/0.98      | ~ r2_hidden(sK5,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_4442]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_6231,plain,
% 3.25/0.98      ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.25/0.98      | ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_6228]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_28,plain,
% 3.25/0.98      ( r1_ordinal1(X0,X1)
% 3.25/0.98      | ~ r1_tarski(X0,X1)
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(X1) ),
% 3.25/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_33,negated_conjecture,
% 3.25/0.98      ( ~ r1_ordinal1(sK5,sK6)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f126]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_268,plain,
% 3.25/0.98      ( ~ r1_ordinal1(sK5,sK6)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(prop_impl,[status(thm)],[c_33]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_646,plain,
% 3.25/0.98      ( ~ r1_tarski(X0,X1)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(X1)
% 3.25/0.98      | sK6 != X1
% 3.25/0.98      | sK5 != X0 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_268]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_647,plain,
% 3.25/0.98      ( ~ r1_tarski(sK5,sK6)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(sK6)
% 3.25/0.98      | ~ v3_ordinal1(sK5) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_646]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_36,negated_conjecture,
% 3.25/0.98      ( v3_ordinal1(sK5) ),
% 3.25/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_35,negated_conjecture,
% 3.25/0.98      ( v3_ordinal1(sK6) ),
% 3.25/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_649,plain,
% 3.25/0.98      ( ~ r1_tarski(sK5,sK6)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_647,c_36,c_35]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_1531,plain,
% 3.25/0.98      ( ~ r1_tarski(sK5,sK6)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(prop_impl,[status(thm)],[c_36,c_35,c_647]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3328,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6) != iProver_top
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_37,plain,
% 3.25/0.98      ( v3_ordinal1(sK5) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_38,plain,
% 3.25/0.98      ( v3_ordinal1(sK6) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_24,plain,
% 3.25/0.98      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_65,plain,
% 3.25/0.98      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_67,plain,
% 3.25/0.98      ( v3_ordinal1(sK6) != iProver_top
% 3.25/0.98      | v1_ordinal1(sK6) = iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_65]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_75,plain,
% 3.25/0.98      ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK6 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_20,plain,
% 3.25/0.98      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f138]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_78,plain,
% 3.25/0.98      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_77,plain,
% 3.25/0.98      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_79,plain,
% 3.25/0.98      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_77]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_651,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6) != iProver_top
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_11,plain,
% 3.25/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.25/0.98      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 3.25/0.98      | r2_hidden(X0,X9) ),
% 3.25/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_23,plain,
% 3.25/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 3.25/0.98      inference(cnf_transformation,[],[f139]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_796,plain,
% 3.25/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.25/0.98      | r2_hidden(X0,X9)
% 3.25/0.98      | X10 != X1
% 3.25/0.98      | X11 != X2
% 3.25/0.98      | X12 != X3
% 3.25/0.98      | X13 != X4
% 3.25/0.98      | X14 != X5
% 3.25/0.98      | X15 != X6
% 3.25/0.98      | X16 != X7
% 3.25/0.98      | X17 != X8
% 3.25/0.98      | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_797,plain,
% 3.25/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.25/0.98      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_796]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_798,plain,
% 3.25/0.98      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.25/0.98      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_800,plain,
% 3.25/0.98      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != iProver_top
% 3.25/0.98      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_798]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_27,plain,
% 3.25/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.25/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_919,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,X1)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v1_ordinal1(X1)
% 3.25/0.98      | sK6 != X1
% 3.25/0.98      | sK5 != X0 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_649]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_920,plain,
% 3.25/0.98      ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ r2_hidden(sK5,sK6)
% 3.25/0.98      | ~ v1_ordinal1(sK6) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_919]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_66,plain,
% 3.25/0.98      ( ~ v3_ordinal1(sK6) | v1_ordinal1(sK6) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_922,plain,
% 3.25/0.98      ( ~ r2_hidden(sK5,sK6)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_920,c_35,c_66]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_923,plain,
% 3.25/0.98      ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ r2_hidden(sK5,sK6) ),
% 3.25/0.98      inference(renaming,[status(thm)],[c_922]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,X1)
% 3.25/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f129]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_930,plain,
% 3.25/0.98      ( ~ r2_hidden(sK5,sK6) ),
% 3.25/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_923,c_4]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_932,plain,
% 3.25/0.98      ( r2_hidden(sK5,sK6) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2566,plain,
% 3.25/0.98      ( X0 != X1
% 3.25/0.98      | X2 != X3
% 3.25/0.98      | X4 != X5
% 3.25/0.98      | X6 != X7
% 3.25/0.98      | X8 != X9
% 3.25/0.98      | X10 != X11
% 3.25/0.98      | X12 != X13
% 3.25/0.98      | X14 != X15
% 3.25/0.98      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.25/0.98      theory(equality) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2573,plain,
% 3.25/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | sK6 != sK6 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_2566]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_32,plain,
% 3.25/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3602,plain,
% 3.25/0.98      ( ~ r1_tarski(sK5,sK6) | ~ r2_hidden(sK6,sK5) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_32]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3603,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6) != iProver_top
% 3.25/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_3602]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_6,plain,
% 3.25/0.98      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.25/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_30,plain,
% 3.25/0.98      ( ~ r2_xboole_0(X0,X1)
% 3.25/0.98      | r2_hidden(X0,X1)
% 3.25/0.98      | ~ v3_ordinal1(X1)
% 3.25/0.98      | ~ v1_ordinal1(X0) ),
% 3.25/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_458,plain,
% 3.25/0.98      ( ~ r1_tarski(X0,X1)
% 3.25/0.98      | r2_hidden(X0,X1)
% 3.25/0.98      | ~ v3_ordinal1(X1)
% 3.25/0.98      | ~ v1_ordinal1(X0)
% 3.25/0.98      | X1 = X0 ),
% 3.25/0.98      inference(resolution,[status(thm)],[c_6,c_30]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3878,plain,
% 3.25/0.98      ( ~ r1_tarski(X0,sK5)
% 3.25/0.98      | r2_hidden(X0,sK5)
% 3.25/0.98      | ~ v3_ordinal1(sK5)
% 3.25/0.98      | ~ v1_ordinal1(X0)
% 3.25/0.98      | sK5 = X0 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_458]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3879,plain,
% 3.25/0.98      ( sK5 = X0
% 3.25/0.98      | r1_tarski(X0,sK5) != iProver_top
% 3.25/0.98      | r2_hidden(X0,sK5) = iProver_top
% 3.25/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.25/0.98      | v1_ordinal1(X0) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_3878]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3881,plain,
% 3.25/0.98      ( sK5 = sK6
% 3.25/0.98      | r1_tarski(sK6,sK5) != iProver_top
% 3.25/0.98      | r2_hidden(sK6,sK5) = iProver_top
% 3.25/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.25/0.98      | v1_ordinal1(sK6) != iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_3879]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,X1)
% 3.25/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f128]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3765,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.25/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4002,plain,
% 3.25/0.98      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_3765]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4003,plain,
% 3.25/0.98      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_4002]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_31,plain,
% 3.25/0.98      ( r1_ordinal1(X0,X1)
% 3.25/0.98      | r2_hidden(X1,X0)
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(X1) ),
% 3.25/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_29,plain,
% 3.25/0.98      ( ~ r1_ordinal1(X0,X1)
% 3.25/0.98      | r1_tarski(X0,X1)
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(X1) ),
% 3.25/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_613,plain,
% 3.25/0.98      ( r1_tarski(X0,X1)
% 3.25/0.98      | r2_hidden(X1,X0)
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(X1) ),
% 3.25/0.98      inference(resolution,[status(thm)],[c_31,c_29]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4303,plain,
% 3.25/0.98      ( r1_tarski(X0,sK5)
% 3.25/0.98      | r2_hidden(sK5,X0)
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(sK5) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_613]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4309,plain,
% 3.25/0.98      ( r1_tarski(X0,sK5) = iProver_top
% 3.25/0.98      | r2_hidden(sK5,X0) = iProver_top
% 3.25/0.98      | v3_ordinal1(X0) != iProver_top
% 3.25/0.98      | v3_ordinal1(sK5) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_4303]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_4311,plain,
% 3.25/0.98      ( r1_tarski(sK6,sK5) = iProver_top
% 3.25/0.98      | r2_hidden(sK5,sK6) = iProver_top
% 3.25/0.98      | v3_ordinal1(sK6) != iProver_top
% 3.25/0.98      | v3_ordinal1(sK5) != iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_4309]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_2568,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.25/0.98      theory(equality) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3766,plain,
% 3.25/0.98      ( r2_hidden(X0,X1)
% 3.25/0.98      | ~ r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
% 3.25/0.98      | X0 != X2
% 3.25/0.98      | X1 != k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_2568]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3943,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.25/0.98      | r2_hidden(X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.25/0.98      | X9 != X0
% 3.25/0.98      | k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_3766]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5038,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.25/0.98      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.25/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | sK5 != X0 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_3943]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5039,plain,
% 3.25/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | sK5 != X0
% 3.25/0.98      | r2_hidden(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 3.25/0.98      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_5038]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5041,plain,
% 3.25/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 3.25/0.98      | sK5 != sK6
% 3.25/0.98      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 3.25/0.98      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_5039]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5304,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6) != iProver_top ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_3328,c_37,c_38,c_67,c_75,c_78,c_79,c_651,c_800,c_932,
% 3.25/0.98                 c_2573,c_3603,c_3881,c_4003,c_4311,c_5041]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3331,plain,
% 3.25/0.98      ( v3_ordinal1(sK5) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3337,plain,
% 3.25/0.98      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3650,plain,
% 3.25/0.98      ( v1_ordinal1(sK5) = iProver_top ),
% 3.25/0.98      inference(superposition,[status(thm)],[c_3331,c_3337]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3656,plain,
% 3.25/0.98      ( v1_ordinal1(sK5) ),
% 3.25/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3650]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_5,plain,
% 3.25/0.98      ( r2_hidden(X0,X1)
% 3.25/0.98      | r2_hidden(X0,X2)
% 3.25/0.98      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f130]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3643,plain,
% 3.25/0.98      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | r2_hidden(sK5,sK6) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3618,plain,
% 3.25/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(sK6,sK5) | X0 != sK6 | X1 != sK5 ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_2568]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3619,plain,
% 3.25/0.98      ( X0 != sK6
% 3.25/0.98      | X1 != sK5
% 3.25/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.25/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_3618]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_3621,plain,
% 3.25/0.98      ( sK6 != sK6
% 3.25/0.98      | sK6 != sK5
% 3.25/0.98      | r2_hidden(sK6,sK6) = iProver_top
% 3.25/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_3619]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_632,plain,
% 3.25/0.98      ( r2_hidden(X0,X1)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(X1)
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | sK6 != X0
% 3.25/0.98      | sK5 != X1 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_31,c_268]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_633,plain,
% 3.25/0.98      ( r2_hidden(sK6,sK5)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(sK6)
% 3.25/0.98      | ~ v3_ordinal1(sK5) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_632]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_635,plain,
% 3.25/0.98      ( r2_hidden(sK6,sK5)
% 3.25/0.98      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_633,c_36,c_35]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_34,negated_conjecture,
% 3.25/0.98      ( r1_ordinal1(sK5,sK6)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(cnf_transformation,[],[f127]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_270,plain,
% 3.25/0.98      ( r1_ordinal1(sK5,sK6)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(prop_impl,[status(thm)],[c_34]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_660,plain,
% 3.25/0.98      ( r1_tarski(X0,X1)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(X0)
% 3.25/0.98      | ~ v3_ordinal1(X1)
% 3.25/0.98      | sK6 != X1
% 3.25/0.98      | sK5 != X0 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_270]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_661,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(sK6)
% 3.25/0.98      | ~ v3_ordinal1(sK5) ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_660]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_663,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_661,c_36,c_35]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_1533,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 3.25/0.98      inference(prop_impl,[status(thm)],[c_36,c_35,c_661]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_1597,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6) | r2_hidden(sK6,sK5) ),
% 3.25/0.98      inference(bin_hyper_res,[status(thm)],[c_635,c_1533]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_1606,plain,
% 3.25/0.98      ( r1_tarski(sK5,sK6) = iProver_top
% 3.25/0.98      | r2_hidden(sK6,sK5) = iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_933,plain,
% 3.25/0.98      ( r2_hidden(X0,X1)
% 3.25/0.98      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v3_ordinal1(X1)
% 3.25/0.98      | ~ v1_ordinal1(X0)
% 3.25/0.98      | X1 = X0
% 3.25/0.98      | sK6 != X1
% 3.25/0.98      | sK5 != X0 ),
% 3.25/0.98      inference(resolution_lifted,[status(thm)],[c_458,c_663]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_934,plain,
% 3.25/0.98      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | r2_hidden(sK5,sK6)
% 3.25/0.98      | ~ v3_ordinal1(sK6)
% 3.25/0.98      | ~ v1_ordinal1(sK5)
% 3.25/0.98      | sK6 = sK5 ),
% 3.25/0.98      inference(unflattening,[status(thm)],[c_933]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_936,plain,
% 3.25/0.98      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 3.25/0.98      | ~ v1_ordinal1(sK5)
% 3.25/0.98      | sK6 = sK5 ),
% 3.25/0.98      inference(global_propositional_subsumption,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_934,c_35,c_930]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_862,plain,
% 3.25/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) | ~ v1_ordinal1(X1) ),
% 3.25/0.98      inference(resolution,[status(thm)],[c_27,c_32]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_863,plain,
% 3.25/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.25/0.98      | r2_hidden(X1,X0) != iProver_top
% 3.25/0.98      | v1_ordinal1(X0) != iProver_top ),
% 3.25/0.98      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_865,plain,
% 3.25/0.98      ( r2_hidden(sK6,sK6) != iProver_top
% 3.25/0.98      | v1_ordinal1(sK6) != iProver_top ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_863]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(c_69,plain,
% 3.25/0.98      ( sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 3.25/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.25/0.98  
% 3.25/0.98  cnf(contradiction,plain,
% 3.25/0.98      ( $false ),
% 3.25/0.98      inference(minisat,
% 3.25/0.98                [status(thm)],
% 3.25/0.98                [c_6289,c_6231,c_5304,c_3656,c_3643,c_3621,c_1606,c_936,
% 3.25/0.98                 c_930,c_865,c_78,c_75,c_69,c_67,c_38]) ).
% 3.25/0.98  
% 3.25/0.98  
% 3.25/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/0.98  
% 3.25/0.98  ------                               Statistics
% 3.25/0.98  
% 3.25/0.98  ------ General
% 3.25/0.98  
% 3.25/0.98  abstr_ref_over_cycles:                  0
% 3.25/0.98  abstr_ref_under_cycles:                 0
% 3.25/0.98  gc_basic_clause_elim:                   0
% 3.25/0.98  forced_gc_time:                         0
% 3.25/0.98  parsing_time:                           0.012
% 3.25/0.98  unif_index_cands_time:                  0.
% 3.25/0.98  unif_index_add_time:                    0.
% 3.25/0.98  orderings_time:                         0.
% 3.25/0.98  out_proof_time:                         0.028
% 3.25/0.98  total_time:                             0.32
% 3.25/0.98  num_of_symbols:                         43
% 3.25/0.98  num_of_terms:                           5516
% 3.25/0.98  
% 3.25/0.98  ------ Preprocessing
% 3.25/0.98  
% 3.25/0.98  num_of_splits:                          0
% 3.25/0.98  num_of_split_atoms:                     0
% 3.25/0.98  num_of_reused_defs:                     0
% 3.25/0.98  num_eq_ax_congr_red:                    92
% 3.25/0.98  num_of_sem_filtered_clauses:            1
% 3.25/0.98  num_of_subtypes:                        0
% 3.25/0.98  monotx_restored_types:                  0
% 3.25/0.98  sat_num_of_epr_types:                   0
% 3.25/0.98  sat_num_of_non_cyclic_types:            0
% 3.25/0.98  sat_guarded_non_collapsed_types:        0
% 3.25/0.98  num_pure_diseq_elim:                    0
% 3.25/0.98  simp_replaced_by:                       0
% 3.25/0.98  res_preprocessed:                       161
% 3.25/0.98  prep_upred:                             0
% 3.25/0.98  prep_unflattend:                        653
% 3.25/0.98  smt_new_axioms:                         0
% 3.25/0.98  pred_elim_cands:                        6
% 3.25/0.98  pred_elim:                              2
% 3.25/0.98  pred_elim_cl:                           2
% 3.25/0.98  pred_elim_cycles:                       10
% 3.25/0.99  merged_defs:                            8
% 3.25/0.99  merged_defs_ncl:                        0
% 3.25/0.99  bin_hyper_res:                          9
% 3.25/0.99  prep_cycles:                            4
% 3.25/0.99  pred_elim_time:                         0.058
% 3.25/0.99  splitting_time:                         0.
% 3.25/0.99  sem_filter_time:                        0.
% 3.25/0.99  monotx_time:                            0.001
% 3.25/0.99  subtype_inf_time:                       0.
% 3.25/0.99  
% 3.25/0.99  ------ Problem properties
% 3.25/0.99  
% 3.25/0.99  clauses:                                35
% 3.25/0.99  conjectures:                            2
% 3.25/0.99  epr:                                    19
% 3.25/0.99  horn:                                   26
% 3.25/0.99  ground:                                 5
% 3.25/0.99  unary:                                  12
% 3.25/0.99  binary:                                 11
% 3.25/0.99  lits:                                   80
% 3.25/0.99  lits_eq:                                14
% 3.25/0.99  fd_pure:                                0
% 3.25/0.99  fd_pseudo:                              0
% 3.25/0.99  fd_cond:                                0
% 3.25/0.99  fd_pseudo_cond:                         6
% 3.25/0.99  ac_symbols:                             0
% 3.25/0.99  
% 3.25/0.99  ------ Propositional Solver
% 3.25/0.99  
% 3.25/0.99  prop_solver_calls:                      27
% 3.25/0.99  prop_fast_solver_calls:                 1243
% 3.25/0.99  smt_solver_calls:                       0
% 3.25/0.99  smt_fast_solver_calls:                  0
% 3.25/0.99  prop_num_of_clauses:                    1594
% 3.25/0.99  prop_preprocess_simplified:             7703
% 3.25/0.99  prop_fo_subsumed:                       27
% 3.25/0.99  prop_solver_time:                       0.
% 3.25/0.99  smt_solver_time:                        0.
% 3.25/0.99  smt_fast_solver_time:                   0.
% 3.25/0.99  prop_fast_solver_time:                  0.
% 3.25/0.99  prop_unsat_core_time:                   0.
% 3.25/0.99  
% 3.25/0.99  ------ QBF
% 3.25/0.99  
% 3.25/0.99  qbf_q_res:                              0
% 3.25/0.99  qbf_num_tautologies:                    0
% 3.25/0.99  qbf_prep_cycles:                        0
% 3.25/0.99  
% 3.25/0.99  ------ BMC1
% 3.25/0.99  
% 3.25/0.99  bmc1_current_bound:                     -1
% 3.25/0.99  bmc1_last_solved_bound:                 -1
% 3.25/0.99  bmc1_unsat_core_size:                   -1
% 3.25/0.99  bmc1_unsat_core_parents_size:           -1
% 3.25/0.99  bmc1_merge_next_fun:                    0
% 3.25/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation
% 3.25/0.99  
% 3.25/0.99  inst_num_of_clauses:                    415
% 3.25/0.99  inst_num_in_passive:                    228
% 3.25/0.99  inst_num_in_active:                     160
% 3.25/0.99  inst_num_in_unprocessed:                26
% 3.25/0.99  inst_num_of_loops:                      214
% 3.25/0.99  inst_num_of_learning_restarts:          0
% 3.25/0.99  inst_num_moves_active_passive:          51
% 3.25/0.99  inst_lit_activity:                      0
% 3.25/0.99  inst_lit_activity_moves:                0
% 3.25/0.99  inst_num_tautologies:                   0
% 3.25/0.99  inst_num_prop_implied:                  0
% 3.25/0.99  inst_num_existing_simplified:           0
% 3.25/0.99  inst_num_eq_res_simplified:             0
% 3.25/0.99  inst_num_child_elim:                    0
% 3.25/0.99  inst_num_of_dismatching_blockings:      101
% 3.25/0.99  inst_num_of_non_proper_insts:           328
% 3.25/0.99  inst_num_of_duplicates:                 0
% 3.25/0.99  inst_inst_num_from_inst_to_res:         0
% 3.25/0.99  inst_dismatching_checking_time:         0.
% 3.25/0.99  
% 3.25/0.99  ------ Resolution
% 3.25/0.99  
% 3.25/0.99  res_num_of_clauses:                     0
% 3.25/0.99  res_num_in_passive:                     0
% 3.25/0.99  res_num_in_active:                      0
% 3.25/0.99  res_num_of_loops:                       165
% 3.25/0.99  res_forward_subset_subsumed:            26
% 3.25/0.99  res_backward_subset_subsumed:           0
% 3.25/0.99  res_forward_subsumed:                   2
% 3.25/0.99  res_backward_subsumed:                  0
% 3.25/0.99  res_forward_subsumption_resolution:     1
% 3.25/0.99  res_backward_subsumption_resolution:    0
% 3.25/0.99  res_clause_to_clause_subsumption:       945
% 3.25/0.99  res_orphan_elimination:                 0
% 3.25/0.99  res_tautology_del:                      68
% 3.25/0.99  res_num_eq_res_simplified:              0
% 3.25/0.99  res_num_sel_changes:                    0
% 3.25/0.99  res_moves_from_active_to_pass:          0
% 3.25/0.99  
% 3.25/0.99  ------ Superposition
% 3.25/0.99  
% 3.25/0.99  sup_time_total:                         0.
% 3.25/0.99  sup_time_generating:                    0.
% 3.25/0.99  sup_time_sim_full:                      0.
% 3.25/0.99  sup_time_sim_immed:                     0.
% 3.25/0.99  
% 3.25/0.99  sup_num_of_clauses:                     68
% 3.25/0.99  sup_num_in_active:                      42
% 3.25/0.99  sup_num_in_passive:                     26
% 3.25/0.99  sup_num_of_loops:                       42
% 3.25/0.99  sup_fw_superposition:                   32
% 3.25/0.99  sup_bw_superposition:                   9
% 3.25/0.99  sup_immediate_simplified:               1
% 3.25/0.99  sup_given_eliminated:                   0
% 3.25/0.99  comparisons_done:                       0
% 3.25/0.99  comparisons_avoided:                    0
% 3.25/0.99  
% 3.25/0.99  ------ Simplifications
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  sim_fw_subset_subsumed:                 0
% 3.25/0.99  sim_bw_subset_subsumed:                 0
% 3.25/0.99  sim_fw_subsumed:                        0
% 3.25/0.99  sim_bw_subsumed:                        0
% 3.25/0.99  sim_fw_subsumption_res:                 0
% 3.25/0.99  sim_bw_subsumption_res:                 0
% 3.25/0.99  sim_tautology_del:                      6
% 3.25/0.99  sim_eq_tautology_del:                   1
% 3.25/0.99  sim_eq_res_simp:                        0
% 3.25/0.99  sim_fw_demodulated:                     0
% 3.25/0.99  sim_bw_demodulated:                     0
% 3.25/0.99  sim_light_normalised:                   1
% 3.25/0.99  sim_joinable_taut:                      0
% 3.25/0.99  sim_joinable_simp:                      0
% 3.25/0.99  sim_ac_normalised:                      0
% 3.25/0.99  sim_smt_subsumption:                    0
% 3.25/0.99  
%------------------------------------------------------------------------------
