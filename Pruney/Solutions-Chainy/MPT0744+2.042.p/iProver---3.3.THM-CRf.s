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

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
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
fof(f40,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X10,X8)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f61])).

fof(f64,plain,(
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

fof(f63,plain,
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

fof(f65,plain,
    ( ( ~ r1_ordinal1(sK5,sK6)
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( r1_ordinal1(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) )
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f62,f64,f63])).

fof(f111,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f82,f116])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f112])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f113])).

fof(f115,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f114])).

fof(f116,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f75,f115])).

fof(f118,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f116])).

fof(f119,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f99,f117,f118])).

fof(f127,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f111,f119])).

fof(f108,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f109,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f139,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f88])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f29,plain,(
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

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f29,f41,f40])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f140,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f96])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK4(X0),X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK4(X0),X0)
          & r2_hidden(sK4(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f100,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f67,f117])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f124])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f68,f117])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f123])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f125,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f117])).

fof(f131,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f125])).

fof(f110,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f128,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f110,f119])).

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
    inference(cnf_transformation,[],[f87])).

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
    inference(cnf_transformation,[],[f83])).

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
    inference(cnf_transformation,[],[f104])).

cnf(c_33,negated_conjecture,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f127])).

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
    inference(cnf_transformation,[],[f108])).

cnf(c_35,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f109])).

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
    inference(cnf_transformation,[],[f98])).

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
    inference(cnf_transformation,[],[f139])).

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
    inference(cnf_transformation,[],[f84])).

cnf(c_23,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f140])).

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
    inference(cnf_transformation,[],[f100])).

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
    inference(cnf_transformation,[],[f130])).

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
    inference(cnf_transformation,[],[f107])).

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
    inference(cnf_transformation,[],[f72])).

cnf(c_30,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f105])).

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
    inference(cnf_transformation,[],[f129])).

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
    inference(cnf_transformation,[],[f106])).

cnf(c_29,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f103])).

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
    inference(cnf_transformation,[],[f131])).

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
    inference(cnf_transformation,[],[f128])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:36:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.94/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.03  
% 2.94/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.03  
% 2.94/1.03  ------  iProver source info
% 2.94/1.03  
% 2.94/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.03  git: non_committed_changes: false
% 2.94/1.03  git: last_make_outside_of_git: false
% 2.94/1.03  
% 2.94/1.03  ------ 
% 2.94/1.03  
% 2.94/1.03  ------ Input Options
% 2.94/1.03  
% 2.94/1.03  --out_options                           all
% 2.94/1.03  --tptp_safe_out                         true
% 2.94/1.03  --problem_path                          ""
% 2.94/1.03  --include_path                          ""
% 2.94/1.03  --clausifier                            res/vclausify_rel
% 2.94/1.03  --clausifier_options                    --mode clausify
% 2.94/1.03  --stdin                                 false
% 2.94/1.03  --stats_out                             all
% 2.94/1.03  
% 2.94/1.03  ------ General Options
% 2.94/1.03  
% 2.94/1.03  --fof                                   false
% 2.94/1.03  --time_out_real                         305.
% 2.94/1.03  --time_out_virtual                      -1.
% 2.94/1.03  --symbol_type_check                     false
% 2.94/1.03  --clausify_out                          false
% 2.94/1.03  --sig_cnt_out                           false
% 2.94/1.03  --trig_cnt_out                          false
% 2.94/1.03  --trig_cnt_out_tolerance                1.
% 2.94/1.03  --trig_cnt_out_sk_spl                   false
% 2.94/1.03  --abstr_cl_out                          false
% 2.94/1.03  
% 2.94/1.03  ------ Global Options
% 2.94/1.03  
% 2.94/1.03  --schedule                              default
% 2.94/1.03  --add_important_lit                     false
% 2.94/1.03  --prop_solver_per_cl                    1000
% 2.94/1.03  --min_unsat_core                        false
% 2.94/1.03  --soft_assumptions                      false
% 2.94/1.03  --soft_lemma_size                       3
% 2.94/1.03  --prop_impl_unit_size                   0
% 2.94/1.03  --prop_impl_unit                        []
% 2.94/1.03  --share_sel_clauses                     true
% 2.94/1.03  --reset_solvers                         false
% 2.94/1.03  --bc_imp_inh                            [conj_cone]
% 2.94/1.03  --conj_cone_tolerance                   3.
% 2.94/1.03  --extra_neg_conj                        none
% 2.94/1.03  --large_theory_mode                     true
% 2.94/1.03  --prolific_symb_bound                   200
% 2.94/1.03  --lt_threshold                          2000
% 2.94/1.03  --clause_weak_htbl                      true
% 2.94/1.03  --gc_record_bc_elim                     false
% 2.94/1.03  
% 2.94/1.03  ------ Preprocessing Options
% 2.94/1.03  
% 2.94/1.03  --preprocessing_flag                    true
% 2.94/1.03  --time_out_prep_mult                    0.1
% 2.94/1.03  --splitting_mode                        input
% 2.94/1.03  --splitting_grd                         true
% 2.94/1.03  --splitting_cvd                         false
% 2.94/1.03  --splitting_cvd_svl                     false
% 2.94/1.03  --splitting_nvd                         32
% 2.94/1.03  --sub_typing                            true
% 2.94/1.03  --prep_gs_sim                           true
% 2.94/1.03  --prep_unflatten                        true
% 2.94/1.03  --prep_res_sim                          true
% 2.94/1.03  --prep_upred                            true
% 2.94/1.03  --prep_sem_filter                       exhaustive
% 2.94/1.03  --prep_sem_filter_out                   false
% 2.94/1.03  --pred_elim                             true
% 2.94/1.03  --res_sim_input                         true
% 2.94/1.03  --eq_ax_congr_red                       true
% 2.94/1.03  --pure_diseq_elim                       true
% 2.94/1.03  --brand_transform                       false
% 2.94/1.03  --non_eq_to_eq                          false
% 2.94/1.03  --prep_def_merge                        true
% 2.94/1.03  --prep_def_merge_prop_impl              false
% 2.94/1.03  --prep_def_merge_mbd                    true
% 2.94/1.03  --prep_def_merge_tr_red                 false
% 2.94/1.03  --prep_def_merge_tr_cl                  false
% 2.94/1.03  --smt_preprocessing                     true
% 2.94/1.03  --smt_ac_axioms                         fast
% 2.94/1.03  --preprocessed_out                      false
% 2.94/1.03  --preprocessed_stats                    false
% 2.94/1.03  
% 2.94/1.03  ------ Abstraction refinement Options
% 2.94/1.03  
% 2.94/1.03  --abstr_ref                             []
% 2.94/1.03  --abstr_ref_prep                        false
% 2.94/1.03  --abstr_ref_until_sat                   false
% 2.94/1.03  --abstr_ref_sig_restrict                funpre
% 2.94/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.03  --abstr_ref_under                       []
% 2.94/1.03  
% 2.94/1.03  ------ SAT Options
% 2.94/1.03  
% 2.94/1.03  --sat_mode                              false
% 2.94/1.03  --sat_fm_restart_options                ""
% 2.94/1.03  --sat_gr_def                            false
% 2.94/1.03  --sat_epr_types                         true
% 2.94/1.03  --sat_non_cyclic_types                  false
% 2.94/1.03  --sat_finite_models                     false
% 2.94/1.03  --sat_fm_lemmas                         false
% 2.94/1.03  --sat_fm_prep                           false
% 2.94/1.03  --sat_fm_uc_incr                        true
% 2.94/1.03  --sat_out_model                         small
% 2.94/1.03  --sat_out_clauses                       false
% 2.94/1.03  
% 2.94/1.03  ------ QBF Options
% 2.94/1.03  
% 2.94/1.03  --qbf_mode                              false
% 2.94/1.03  --qbf_elim_univ                         false
% 2.94/1.03  --qbf_dom_inst                          none
% 2.94/1.03  --qbf_dom_pre_inst                      false
% 2.94/1.03  --qbf_sk_in                             false
% 2.94/1.03  --qbf_pred_elim                         true
% 2.94/1.03  --qbf_split                             512
% 2.94/1.03  
% 2.94/1.03  ------ BMC1 Options
% 2.94/1.03  
% 2.94/1.03  --bmc1_incremental                      false
% 2.94/1.03  --bmc1_axioms                           reachable_all
% 2.94/1.03  --bmc1_min_bound                        0
% 2.94/1.03  --bmc1_max_bound                        -1
% 2.94/1.03  --bmc1_max_bound_default                -1
% 2.94/1.03  --bmc1_symbol_reachability              true
% 2.94/1.03  --bmc1_property_lemmas                  false
% 2.94/1.03  --bmc1_k_induction                      false
% 2.94/1.03  --bmc1_non_equiv_states                 false
% 2.94/1.03  --bmc1_deadlock                         false
% 2.94/1.03  --bmc1_ucm                              false
% 2.94/1.03  --bmc1_add_unsat_core                   none
% 2.94/1.03  --bmc1_unsat_core_children              false
% 2.94/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.03  --bmc1_out_stat                         full
% 2.94/1.03  --bmc1_ground_init                      false
% 2.94/1.03  --bmc1_pre_inst_next_state              false
% 2.94/1.03  --bmc1_pre_inst_state                   false
% 2.94/1.03  --bmc1_pre_inst_reach_state             false
% 2.94/1.03  --bmc1_out_unsat_core                   false
% 2.94/1.03  --bmc1_aig_witness_out                  false
% 2.94/1.03  --bmc1_verbose                          false
% 2.94/1.03  --bmc1_dump_clauses_tptp                false
% 2.94/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.03  --bmc1_dump_file                        -
% 2.94/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.03  --bmc1_ucm_extend_mode                  1
% 2.94/1.03  --bmc1_ucm_init_mode                    2
% 2.94/1.03  --bmc1_ucm_cone_mode                    none
% 2.94/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.03  --bmc1_ucm_relax_model                  4
% 2.94/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.03  --bmc1_ucm_layered_model                none
% 2.94/1.03  --bmc1_ucm_max_lemma_size               10
% 2.94/1.03  
% 2.94/1.03  ------ AIG Options
% 2.94/1.03  
% 2.94/1.03  --aig_mode                              false
% 2.94/1.03  
% 2.94/1.03  ------ Instantiation Options
% 2.94/1.03  
% 2.94/1.03  --instantiation_flag                    true
% 2.94/1.03  --inst_sos_flag                         false
% 2.94/1.03  --inst_sos_phase                        true
% 2.94/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.03  --inst_lit_sel_side                     num_symb
% 2.94/1.03  --inst_solver_per_active                1400
% 2.94/1.03  --inst_solver_calls_frac                1.
% 2.94/1.03  --inst_passive_queue_type               priority_queues
% 2.94/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.03  --inst_passive_queues_freq              [25;2]
% 2.94/1.03  --inst_dismatching                      true
% 2.94/1.03  --inst_eager_unprocessed_to_passive     true
% 2.94/1.03  --inst_prop_sim_given                   true
% 2.94/1.03  --inst_prop_sim_new                     false
% 2.94/1.03  --inst_subs_new                         false
% 2.94/1.03  --inst_eq_res_simp                      false
% 2.94/1.03  --inst_subs_given                       false
% 2.94/1.03  --inst_orphan_elimination               true
% 2.94/1.03  --inst_learning_loop_flag               true
% 2.94/1.03  --inst_learning_start                   3000
% 2.94/1.03  --inst_learning_factor                  2
% 2.94/1.03  --inst_start_prop_sim_after_learn       3
% 2.94/1.03  --inst_sel_renew                        solver
% 2.94/1.03  --inst_lit_activity_flag                true
% 2.94/1.03  --inst_restr_to_given                   false
% 2.94/1.03  --inst_activity_threshold               500
% 2.94/1.03  --inst_out_proof                        true
% 2.94/1.03  
% 2.94/1.03  ------ Resolution Options
% 2.94/1.03  
% 2.94/1.03  --resolution_flag                       true
% 2.94/1.03  --res_lit_sel                           adaptive
% 2.94/1.03  --res_lit_sel_side                      none
% 2.94/1.03  --res_ordering                          kbo
% 2.94/1.03  --res_to_prop_solver                    active
% 2.94/1.03  --res_prop_simpl_new                    false
% 2.94/1.03  --res_prop_simpl_given                  true
% 2.94/1.03  --res_passive_queue_type                priority_queues
% 2.94/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.03  --res_passive_queues_freq               [15;5]
% 2.94/1.03  --res_forward_subs                      full
% 2.94/1.03  --res_backward_subs                     full
% 2.94/1.03  --res_forward_subs_resolution           true
% 2.94/1.03  --res_backward_subs_resolution          true
% 2.94/1.03  --res_orphan_elimination                true
% 2.94/1.03  --res_time_limit                        2.
% 2.94/1.03  --res_out_proof                         true
% 2.94/1.03  
% 2.94/1.03  ------ Superposition Options
% 2.94/1.03  
% 2.94/1.03  --superposition_flag                    true
% 2.94/1.03  --sup_passive_queue_type                priority_queues
% 2.94/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.03  --demod_completeness_check              fast
% 2.94/1.03  --demod_use_ground                      true
% 2.94/1.03  --sup_to_prop_solver                    passive
% 2.94/1.03  --sup_prop_simpl_new                    true
% 2.94/1.03  --sup_prop_simpl_given                  true
% 2.94/1.03  --sup_fun_splitting                     false
% 2.94/1.03  --sup_smt_interval                      50000
% 2.94/1.03  
% 2.94/1.03  ------ Superposition Simplification Setup
% 2.94/1.03  
% 2.94/1.03  --sup_indices_passive                   []
% 2.94/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.03  --sup_full_bw                           [BwDemod]
% 2.94/1.03  --sup_immed_triv                        [TrivRules]
% 2.94/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.03  --sup_immed_bw_main                     []
% 2.94/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.03  
% 2.94/1.03  ------ Combination Options
% 2.94/1.03  
% 2.94/1.03  --comb_res_mult                         3
% 2.94/1.03  --comb_sup_mult                         2
% 2.94/1.03  --comb_inst_mult                        10
% 2.94/1.03  
% 2.94/1.03  ------ Debug Options
% 2.94/1.03  
% 2.94/1.03  --dbg_backtrace                         false
% 2.94/1.03  --dbg_dump_prop_clauses                 false
% 2.94/1.03  --dbg_dump_prop_clauses_file            -
% 2.94/1.03  --dbg_out_stat                          false
% 2.94/1.03  ------ Parsing...
% 2.94/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.03  
% 2.94/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.94/1.03  
% 2.94/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.03  
% 2.94/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.03  ------ Proving...
% 2.94/1.03  ------ Problem Properties 
% 2.94/1.03  
% 2.94/1.03  
% 2.94/1.03  clauses                                 35
% 2.94/1.03  conjectures                             2
% 2.94/1.03  EPR                                     19
% 2.94/1.03  Horn                                    26
% 2.94/1.03  unary                                   12
% 2.94/1.03  binary                                  11
% 2.94/1.03  lits                                    80
% 2.94/1.03  lits eq                                 14
% 2.94/1.03  fd_pure                                 0
% 2.94/1.03  fd_pseudo                               0
% 2.94/1.03  fd_cond                                 0
% 2.94/1.03  fd_pseudo_cond                          6
% 2.94/1.03  AC symbols                              0
% 2.94/1.03  
% 2.94/1.03  ------ Schedule dynamic 5 is on 
% 2.94/1.03  
% 2.94/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/1.03  
% 2.94/1.03  
% 2.94/1.03  ------ 
% 2.94/1.03  Current options:
% 2.94/1.03  ------ 
% 2.94/1.03  
% 2.94/1.03  ------ Input Options
% 2.94/1.03  
% 2.94/1.03  --out_options                           all
% 2.94/1.03  --tptp_safe_out                         true
% 2.94/1.03  --problem_path                          ""
% 2.94/1.03  --include_path                          ""
% 2.94/1.03  --clausifier                            res/vclausify_rel
% 2.94/1.03  --clausifier_options                    --mode clausify
% 2.94/1.03  --stdin                                 false
% 2.94/1.03  --stats_out                             all
% 2.94/1.03  
% 2.94/1.03  ------ General Options
% 2.94/1.03  
% 2.94/1.03  --fof                                   false
% 2.94/1.03  --time_out_real                         305.
% 2.94/1.03  --time_out_virtual                      -1.
% 2.94/1.03  --symbol_type_check                     false
% 2.94/1.03  --clausify_out                          false
% 2.94/1.03  --sig_cnt_out                           false
% 2.94/1.03  --trig_cnt_out                          false
% 2.94/1.03  --trig_cnt_out_tolerance                1.
% 2.94/1.03  --trig_cnt_out_sk_spl                   false
% 2.94/1.03  --abstr_cl_out                          false
% 2.94/1.03  
% 2.94/1.03  ------ Global Options
% 2.94/1.03  
% 2.94/1.03  --schedule                              default
% 2.94/1.03  --add_important_lit                     false
% 2.94/1.03  --prop_solver_per_cl                    1000
% 2.94/1.03  --min_unsat_core                        false
% 2.94/1.03  --soft_assumptions                      false
% 2.94/1.03  --soft_lemma_size                       3
% 2.94/1.03  --prop_impl_unit_size                   0
% 2.94/1.03  --prop_impl_unit                        []
% 2.94/1.03  --share_sel_clauses                     true
% 2.94/1.03  --reset_solvers                         false
% 2.94/1.03  --bc_imp_inh                            [conj_cone]
% 2.94/1.03  --conj_cone_tolerance                   3.
% 2.94/1.03  --extra_neg_conj                        none
% 2.94/1.03  --large_theory_mode                     true
% 2.94/1.03  --prolific_symb_bound                   200
% 2.94/1.03  --lt_threshold                          2000
% 2.94/1.03  --clause_weak_htbl                      true
% 2.94/1.03  --gc_record_bc_elim                     false
% 2.94/1.03  
% 2.94/1.03  ------ Preprocessing Options
% 2.94/1.03  
% 2.94/1.03  --preprocessing_flag                    true
% 2.94/1.03  --time_out_prep_mult                    0.1
% 2.94/1.03  --splitting_mode                        input
% 2.94/1.03  --splitting_grd                         true
% 2.94/1.03  --splitting_cvd                         false
% 2.94/1.03  --splitting_cvd_svl                     false
% 2.94/1.03  --splitting_nvd                         32
% 2.94/1.03  --sub_typing                            true
% 2.94/1.03  --prep_gs_sim                           true
% 2.94/1.03  --prep_unflatten                        true
% 2.94/1.03  --prep_res_sim                          true
% 2.94/1.03  --prep_upred                            true
% 2.94/1.03  --prep_sem_filter                       exhaustive
% 2.94/1.03  --prep_sem_filter_out                   false
% 2.94/1.03  --pred_elim                             true
% 2.94/1.03  --res_sim_input                         true
% 2.94/1.03  --eq_ax_congr_red                       true
% 2.94/1.03  --pure_diseq_elim                       true
% 2.94/1.03  --brand_transform                       false
% 2.94/1.03  --non_eq_to_eq                          false
% 2.94/1.03  --prep_def_merge                        true
% 2.94/1.03  --prep_def_merge_prop_impl              false
% 2.94/1.03  --prep_def_merge_mbd                    true
% 2.94/1.03  --prep_def_merge_tr_red                 false
% 2.94/1.03  --prep_def_merge_tr_cl                  false
% 2.94/1.03  --smt_preprocessing                     true
% 2.94/1.03  --smt_ac_axioms                         fast
% 2.94/1.03  --preprocessed_out                      false
% 2.94/1.03  --preprocessed_stats                    false
% 2.94/1.03  
% 2.94/1.03  ------ Abstraction refinement Options
% 2.94/1.03  
% 2.94/1.03  --abstr_ref                             []
% 2.94/1.03  --abstr_ref_prep                        false
% 2.94/1.03  --abstr_ref_until_sat                   false
% 2.94/1.03  --abstr_ref_sig_restrict                funpre
% 2.94/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.03  --abstr_ref_under                       []
% 2.94/1.03  
% 2.94/1.03  ------ SAT Options
% 2.94/1.03  
% 2.94/1.03  --sat_mode                              false
% 2.94/1.03  --sat_fm_restart_options                ""
% 2.94/1.03  --sat_gr_def                            false
% 2.94/1.03  --sat_epr_types                         true
% 2.94/1.03  --sat_non_cyclic_types                  false
% 2.94/1.03  --sat_finite_models                     false
% 2.94/1.03  --sat_fm_lemmas                         false
% 2.94/1.03  --sat_fm_prep                           false
% 2.94/1.03  --sat_fm_uc_incr                        true
% 2.94/1.03  --sat_out_model                         small
% 2.94/1.03  --sat_out_clauses                       false
% 2.94/1.03  
% 2.94/1.03  ------ QBF Options
% 2.94/1.03  
% 2.94/1.03  --qbf_mode                              false
% 2.94/1.03  --qbf_elim_univ                         false
% 2.94/1.03  --qbf_dom_inst                          none
% 2.94/1.03  --qbf_dom_pre_inst                      false
% 2.94/1.03  --qbf_sk_in                             false
% 2.94/1.03  --qbf_pred_elim                         true
% 2.94/1.03  --qbf_split                             512
% 2.94/1.03  
% 2.94/1.03  ------ BMC1 Options
% 2.94/1.03  
% 2.94/1.03  --bmc1_incremental                      false
% 2.94/1.03  --bmc1_axioms                           reachable_all
% 2.94/1.03  --bmc1_min_bound                        0
% 2.94/1.03  --bmc1_max_bound                        -1
% 2.94/1.03  --bmc1_max_bound_default                -1
% 2.94/1.03  --bmc1_symbol_reachability              true
% 2.94/1.03  --bmc1_property_lemmas                  false
% 2.94/1.03  --bmc1_k_induction                      false
% 2.94/1.03  --bmc1_non_equiv_states                 false
% 2.94/1.03  --bmc1_deadlock                         false
% 2.94/1.03  --bmc1_ucm                              false
% 2.94/1.03  --bmc1_add_unsat_core                   none
% 2.94/1.03  --bmc1_unsat_core_children              false
% 2.94/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.03  --bmc1_out_stat                         full
% 2.94/1.03  --bmc1_ground_init                      false
% 2.94/1.03  --bmc1_pre_inst_next_state              false
% 2.94/1.03  --bmc1_pre_inst_state                   false
% 2.94/1.03  --bmc1_pre_inst_reach_state             false
% 2.94/1.03  --bmc1_out_unsat_core                   false
% 2.94/1.03  --bmc1_aig_witness_out                  false
% 2.94/1.03  --bmc1_verbose                          false
% 2.94/1.03  --bmc1_dump_clauses_tptp                false
% 2.94/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.03  --bmc1_dump_file                        -
% 2.94/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.03  --bmc1_ucm_extend_mode                  1
% 2.94/1.03  --bmc1_ucm_init_mode                    2
% 2.94/1.03  --bmc1_ucm_cone_mode                    none
% 2.94/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.03  --bmc1_ucm_relax_model                  4
% 2.94/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.03  --bmc1_ucm_layered_model                none
% 2.94/1.03  --bmc1_ucm_max_lemma_size               10
% 2.94/1.03  
% 2.94/1.03  ------ AIG Options
% 2.94/1.03  
% 2.94/1.03  --aig_mode                              false
% 2.94/1.03  
% 2.94/1.03  ------ Instantiation Options
% 2.94/1.03  
% 2.94/1.03  --instantiation_flag                    true
% 2.94/1.03  --inst_sos_flag                         false
% 2.94/1.03  --inst_sos_phase                        true
% 2.94/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.03  --inst_lit_sel_side                     none
% 2.94/1.03  --inst_solver_per_active                1400
% 2.94/1.03  --inst_solver_calls_frac                1.
% 2.94/1.03  --inst_passive_queue_type               priority_queues
% 2.94/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.03  --inst_passive_queues_freq              [25;2]
% 2.94/1.03  --inst_dismatching                      true
% 2.94/1.03  --inst_eager_unprocessed_to_passive     true
% 2.94/1.03  --inst_prop_sim_given                   true
% 2.94/1.03  --inst_prop_sim_new                     false
% 2.94/1.03  --inst_subs_new                         false
% 2.94/1.03  --inst_eq_res_simp                      false
% 2.94/1.03  --inst_subs_given                       false
% 2.94/1.03  --inst_orphan_elimination               true
% 2.94/1.03  --inst_learning_loop_flag               true
% 2.94/1.03  --inst_learning_start                   3000
% 2.94/1.03  --inst_learning_factor                  2
% 2.94/1.03  --inst_start_prop_sim_after_learn       3
% 2.94/1.03  --inst_sel_renew                        solver
% 2.94/1.03  --inst_lit_activity_flag                true
% 2.94/1.03  --inst_restr_to_given                   false
% 2.94/1.03  --inst_activity_threshold               500
% 2.94/1.03  --inst_out_proof                        true
% 2.94/1.03  
% 2.94/1.03  ------ Resolution Options
% 2.94/1.03  
% 2.94/1.03  --resolution_flag                       false
% 2.94/1.03  --res_lit_sel                           adaptive
% 2.94/1.03  --res_lit_sel_side                      none
% 2.94/1.03  --res_ordering                          kbo
% 2.94/1.03  --res_to_prop_solver                    active
% 2.94/1.03  --res_prop_simpl_new                    false
% 2.94/1.03  --res_prop_simpl_given                  true
% 2.94/1.03  --res_passive_queue_type                priority_queues
% 2.94/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.03  --res_passive_queues_freq               [15;5]
% 2.94/1.03  --res_forward_subs                      full
% 2.94/1.03  --res_backward_subs                     full
% 2.94/1.03  --res_forward_subs_resolution           true
% 2.94/1.03  --res_backward_subs_resolution          true
% 2.94/1.03  --res_orphan_elimination                true
% 2.94/1.03  --res_time_limit                        2.
% 2.94/1.03  --res_out_proof                         true
% 2.94/1.03  
% 2.94/1.03  ------ Superposition Options
% 2.94/1.03  
% 2.94/1.03  --superposition_flag                    true
% 2.94/1.03  --sup_passive_queue_type                priority_queues
% 2.94/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.03  --demod_completeness_check              fast
% 2.94/1.03  --demod_use_ground                      true
% 2.94/1.03  --sup_to_prop_solver                    passive
% 2.94/1.03  --sup_prop_simpl_new                    true
% 2.94/1.03  --sup_prop_simpl_given                  true
% 2.94/1.03  --sup_fun_splitting                     false
% 2.94/1.03  --sup_smt_interval                      50000
% 2.94/1.03  
% 2.94/1.03  ------ Superposition Simplification Setup
% 2.94/1.03  
% 2.94/1.03  --sup_indices_passive                   []
% 2.94/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.03  --sup_full_bw                           [BwDemod]
% 2.94/1.03  --sup_immed_triv                        [TrivRules]
% 2.94/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.03  --sup_immed_bw_main                     []
% 2.94/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.03  
% 2.94/1.03  ------ Combination Options
% 2.94/1.03  
% 2.94/1.03  --comb_res_mult                         3
% 2.94/1.03  --comb_sup_mult                         2
% 2.94/1.03  --comb_inst_mult                        10
% 2.94/1.03  
% 2.94/1.03  ------ Debug Options
% 2.94/1.03  
% 2.94/1.03  --dbg_backtrace                         false
% 2.94/1.03  --dbg_dump_prop_clauses                 false
% 2.94/1.03  --dbg_dump_prop_clauses_file            -
% 2.94/1.03  --dbg_out_stat                          false
% 2.94/1.03  
% 2.94/1.03  
% 2.94/1.03  
% 2.94/1.03  
% 2.94/1.03  ------ Proving...
% 2.94/1.03  
% 2.94/1.03  
% 2.94/1.03  % SZS status Theorem for theBenchmark.p
% 2.94/1.03  
% 2.94/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.03  
% 2.94/1.03  fof(f40,plain,(
% 2.94/1.03    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.94/1.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.94/1.03  
% 2.94/1.03  fof(f52,plain,(
% 2.94/1.03    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.94/1.03    inference(nnf_transformation,[],[f40])).
% 2.94/1.03  
% 2.94/1.03  fof(f53,plain,(
% 2.94/1.03    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.94/1.03    inference(flattening,[],[f52])).
% 2.94/1.03  
% 2.94/1.03  fof(f54,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.94/1.03    inference(rectify,[],[f53])).
% 2.94/1.03  
% 2.94/1.03  fof(f87,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f54])).
% 2.94/1.03  
% 2.94/1.03  fof(f41,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.94/1.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.94/1.03  
% 2.94/1.03  fof(f48,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.94/1.03    inference(nnf_transformation,[],[f41])).
% 2.94/1.03  
% 2.94/1.03  fof(f49,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.94/1.03    inference(rectify,[],[f48])).
% 2.94/1.03  
% 2.94/1.03  fof(f50,plain,(
% 2.94/1.03    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.94/1.03    introduced(choice_axiom,[])).
% 2.94/1.03  
% 2.94/1.03  fof(f51,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.94/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 2.94/1.03  
% 2.94/1.03  fof(f83,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f51])).
% 2.94/1.03  
% 2.94/1.03  fof(f17,axiom,(
% 2.94/1.03    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f32,plain,(
% 2.94/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.94/1.03    inference(ennf_transformation,[],[f17])).
% 2.94/1.03  
% 2.94/1.03  fof(f33,plain,(
% 2.94/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.94/1.03    inference(flattening,[],[f32])).
% 2.94/1.03  
% 2.94/1.03  fof(f60,plain,(
% 2.94/1.03    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.94/1.03    inference(nnf_transformation,[],[f33])).
% 2.94/1.03  
% 2.94/1.03  fof(f104,plain,(
% 2.94/1.03    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f60])).
% 2.94/1.03  
% 2.94/1.03  fof(f21,conjecture,(
% 2.94/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f22,negated_conjecture,(
% 2.94/1.03    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.94/1.03    inference(negated_conjecture,[],[f21])).
% 2.94/1.03  
% 2.94/1.03  fof(f39,plain,(
% 2.94/1.03    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.94/1.03    inference(ennf_transformation,[],[f22])).
% 2.94/1.03  
% 2.94/1.03  fof(f61,plain,(
% 2.94/1.03    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.94/1.03    inference(nnf_transformation,[],[f39])).
% 2.94/1.03  
% 2.94/1.03  fof(f62,plain,(
% 2.94/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.94/1.03    inference(flattening,[],[f61])).
% 2.94/1.03  
% 2.94/1.03  fof(f64,plain,(
% 2.94/1.03    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK6) | ~r2_hidden(X0,k1_ordinal1(sK6))) & (r1_ordinal1(X0,sK6) | r2_hidden(X0,k1_ordinal1(sK6))) & v3_ordinal1(sK6))) )),
% 2.94/1.03    introduced(choice_axiom,[])).
% 2.94/1.03  
% 2.94/1.03  fof(f63,plain,(
% 2.94/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK5,X1) | ~r2_hidden(sK5,k1_ordinal1(X1))) & (r1_ordinal1(sK5,X1) | r2_hidden(sK5,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK5))),
% 2.94/1.03    introduced(choice_axiom,[])).
% 2.94/1.03  
% 2.94/1.03  fof(f65,plain,(
% 2.94/1.03    ((~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))) & v3_ordinal1(sK6)) & v3_ordinal1(sK5)),
% 2.94/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f62,f64,f63])).
% 2.94/1.03  
% 2.94/1.03  fof(f111,plain,(
% 2.94/1.03    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.94/1.03    inference(cnf_transformation,[],[f65])).
% 2.94/1.03  
% 2.94/1.03  fof(f15,axiom,(
% 2.94/1.03    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f99,plain,(
% 2.94/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f15])).
% 2.94/1.03  
% 2.94/1.03  fof(f12,axiom,(
% 2.94/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f82,plain,(
% 2.94/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.94/1.03    inference(cnf_transformation,[],[f12])).
% 2.94/1.03  
% 2.94/1.03  fof(f117,plain,(
% 2.94/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.94/1.03    inference(definition_unfolding,[],[f82,f116])).
% 2.94/1.03  
% 2.94/1.03  fof(f4,axiom,(
% 2.94/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f74,plain,(
% 2.94/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f4])).
% 2.94/1.03  
% 2.94/1.03  fof(f5,axiom,(
% 2.94/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f75,plain,(
% 2.94/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f5])).
% 2.94/1.03  
% 2.94/1.03  fof(f6,axiom,(
% 2.94/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f76,plain,(
% 2.94/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f6])).
% 2.94/1.03  
% 2.94/1.03  fof(f7,axiom,(
% 2.94/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f77,plain,(
% 2.94/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f7])).
% 2.94/1.03  
% 2.94/1.03  fof(f8,axiom,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f78,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f8])).
% 2.94/1.03  
% 2.94/1.03  fof(f9,axiom,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f79,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f9])).
% 2.94/1.03  
% 2.94/1.03  fof(f10,axiom,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f80,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f10])).
% 2.94/1.03  
% 2.94/1.03  fof(f112,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f79,f80])).
% 2.94/1.03  
% 2.94/1.03  fof(f113,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f78,f112])).
% 2.94/1.03  
% 2.94/1.03  fof(f114,plain,(
% 2.94/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f77,f113])).
% 2.94/1.03  
% 2.94/1.03  fof(f115,plain,(
% 2.94/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f76,f114])).
% 2.94/1.03  
% 2.94/1.03  fof(f116,plain,(
% 2.94/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f75,f115])).
% 2.94/1.03  
% 2.94/1.03  fof(f118,plain,(
% 2.94/1.03    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f74,f116])).
% 2.94/1.03  
% 2.94/1.03  fof(f119,plain,(
% 2.94/1.03    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.94/1.03    inference(definition_unfolding,[],[f99,f117,f118])).
% 2.94/1.03  
% 2.94/1.03  fof(f127,plain,(
% 2.94/1.03    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.94/1.03    inference(definition_unfolding,[],[f111,f119])).
% 2.94/1.03  
% 2.94/1.03  fof(f108,plain,(
% 2.94/1.03    v3_ordinal1(sK5)),
% 2.94/1.03    inference(cnf_transformation,[],[f65])).
% 2.94/1.03  
% 2.94/1.03  fof(f109,plain,(
% 2.94/1.03    v3_ordinal1(sK6)),
% 2.94/1.03    inference(cnf_transformation,[],[f65])).
% 2.94/1.03  
% 2.94/1.03  fof(f14,axiom,(
% 2.94/1.03    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f25,plain,(
% 2.94/1.03    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 2.94/1.03    inference(pure_predicate_removal,[],[f14])).
% 2.94/1.03  
% 2.94/1.03  fof(f30,plain,(
% 2.94/1.03    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 2.94/1.03    inference(ennf_transformation,[],[f25])).
% 2.94/1.03  
% 2.94/1.03  fof(f98,plain,(
% 2.94/1.03    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f30])).
% 2.94/1.03  
% 2.94/1.03  fof(f88,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 2.94/1.03    inference(cnf_transformation,[],[f54])).
% 2.94/1.03  
% 2.94/1.03  fof(f139,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.94/1.03    inference(equality_resolution,[],[f88])).
% 2.94/1.03  
% 2.94/1.03  fof(f84,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f51])).
% 2.94/1.03  
% 2.94/1.03  fof(f13,axiom,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f29,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.94/1.03    inference(ennf_transformation,[],[f13])).
% 2.94/1.03  
% 2.94/1.03  fof(f42,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.94/1.03    inference(definition_folding,[],[f29,f41,f40])).
% 2.94/1.03  
% 2.94/1.03  fof(f55,plain,(
% 2.94/1.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.94/1.03    inference(nnf_transformation,[],[f42])).
% 2.94/1.03  
% 2.94/1.03  fof(f96,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.94/1.03    inference(cnf_transformation,[],[f55])).
% 2.94/1.03  
% 2.94/1.03  fof(f140,plain,(
% 2.94/1.03    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.94/1.03    inference(equality_resolution,[],[f96])).
% 2.94/1.03  
% 2.94/1.03  fof(f16,axiom,(
% 2.94/1.03    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f31,plain,(
% 2.94/1.03    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 2.94/1.03    inference(ennf_transformation,[],[f16])).
% 2.94/1.03  
% 2.94/1.03  fof(f56,plain,(
% 2.94/1.03    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 2.94/1.03    inference(nnf_transformation,[],[f31])).
% 2.94/1.03  
% 2.94/1.03  fof(f57,plain,(
% 2.94/1.03    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 2.94/1.03    inference(rectify,[],[f56])).
% 2.94/1.03  
% 2.94/1.03  fof(f58,plain,(
% 2.94/1.03    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK4(X0),X0) & r2_hidden(sK4(X0),X0)))),
% 2.94/1.03    introduced(choice_axiom,[])).
% 2.94/1.03  
% 2.94/1.03  fof(f59,plain,(
% 2.94/1.03    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK4(X0),X0) & r2_hidden(sK4(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 2.94/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 2.94/1.03  
% 2.94/1.03  fof(f100,plain,(
% 2.94/1.03    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f59])).
% 2.94/1.03  
% 2.94/1.03  fof(f1,axiom,(
% 2.94/1.03    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f43,plain,(
% 2.94/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.94/1.03    inference(nnf_transformation,[],[f1])).
% 2.94/1.03  
% 2.94/1.03  fof(f44,plain,(
% 2.94/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.94/1.03    inference(flattening,[],[f43])).
% 2.94/1.03  
% 2.94/1.03  fof(f45,plain,(
% 2.94/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.94/1.03    inference(rectify,[],[f44])).
% 2.94/1.03  
% 2.94/1.03  fof(f46,plain,(
% 2.94/1.03    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.94/1.03    introduced(choice_axiom,[])).
% 2.94/1.03  
% 2.94/1.03  fof(f47,plain,(
% 2.94/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.94/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 2.94/1.03  
% 2.94/1.03  fof(f67,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.94/1.03    inference(cnf_transformation,[],[f47])).
% 2.94/1.03  
% 2.94/1.03  fof(f124,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.94/1.03    inference(definition_unfolding,[],[f67,f117])).
% 2.94/1.03  
% 2.94/1.03  fof(f130,plain,(
% 2.94/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.94/1.03    inference(equality_resolution,[],[f124])).
% 2.94/1.03  
% 2.94/1.03  fof(f20,axiom,(
% 2.94/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f38,plain,(
% 2.94/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.94/1.03    inference(ennf_transformation,[],[f20])).
% 2.94/1.03  
% 2.94/1.03  fof(f107,plain,(
% 2.94/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f38])).
% 2.94/1.03  
% 2.94/1.03  fof(f2,axiom,(
% 2.94/1.03    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f24,plain,(
% 2.94/1.03    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.94/1.03    inference(unused_predicate_definition_removal,[],[f2])).
% 2.94/1.03  
% 2.94/1.03  fof(f26,plain,(
% 2.94/1.03    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.94/1.03    inference(ennf_transformation,[],[f24])).
% 2.94/1.03  
% 2.94/1.03  fof(f27,plain,(
% 2.94/1.03    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.94/1.03    inference(flattening,[],[f26])).
% 2.94/1.03  
% 2.94/1.03  fof(f72,plain,(
% 2.94/1.03    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f27])).
% 2.94/1.03  
% 2.94/1.03  fof(f18,axiom,(
% 2.94/1.03    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f34,plain,(
% 2.94/1.03    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 2.94/1.03    inference(ennf_transformation,[],[f18])).
% 2.94/1.03  
% 2.94/1.03  fof(f35,plain,(
% 2.94/1.03    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 2.94/1.03    inference(flattening,[],[f34])).
% 2.94/1.03  
% 2.94/1.03  fof(f105,plain,(
% 2.94/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f35])).
% 2.94/1.03  
% 2.94/1.03  fof(f68,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.94/1.03    inference(cnf_transformation,[],[f47])).
% 2.94/1.03  
% 2.94/1.03  fof(f123,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.94/1.03    inference(definition_unfolding,[],[f68,f117])).
% 2.94/1.03  
% 2.94/1.03  fof(f129,plain,(
% 2.94/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.94/1.03    inference(equality_resolution,[],[f123])).
% 2.94/1.03  
% 2.94/1.03  fof(f19,axiom,(
% 2.94/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.94/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.03  
% 2.94/1.03  fof(f36,plain,(
% 2.94/1.03    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.94/1.03    inference(ennf_transformation,[],[f19])).
% 2.94/1.03  
% 2.94/1.03  fof(f37,plain,(
% 2.94/1.03    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.94/1.03    inference(flattening,[],[f36])).
% 2.94/1.03  
% 2.94/1.03  fof(f106,plain,(
% 2.94/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f37])).
% 2.94/1.03  
% 2.94/1.03  fof(f103,plain,(
% 2.94/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.94/1.03    inference(cnf_transformation,[],[f60])).
% 2.94/1.03  
% 2.94/1.03  fof(f66,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.94/1.03    inference(cnf_transformation,[],[f47])).
% 2.94/1.03  
% 2.94/1.03  fof(f125,plain,(
% 2.94/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.94/1.03    inference(definition_unfolding,[],[f66,f117])).
% 2.94/1.03  
% 2.94/1.03  fof(f131,plain,(
% 2.94/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.94/1.03    inference(equality_resolution,[],[f125])).
% 2.94/1.03  
% 2.94/1.03  fof(f110,plain,(
% 2.94/1.03    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.94/1.03    inference(cnf_transformation,[],[f65])).
% 2.94/1.03  
% 2.94/1.03  fof(f128,plain,(
% 2.94/1.03    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.94/1.03    inference(definition_unfolding,[],[f110,f119])).
% 2.94/1.03  
% 2.94/1.03  cnf(c_21,plain,
% 2.94/1.03      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.94/1.03      | X1 = X0
% 2.94/1.03      | X8 = X0
% 2.94/1.03      | X7 = X0
% 2.94/1.03      | X6 = X0
% 2.94/1.03      | X5 = X0
% 2.94/1.03      | X4 = X0
% 2.94/1.03      | X3 = X0
% 2.94/1.03      | X2 = X0 ),
% 2.94/1.03      inference(cnf_transformation,[],[f87]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_6284,plain,
% 2.94/1.03      ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7)
% 2.94/1.03      | X0 = sK5
% 2.94/1.03      | X1 = sK5
% 2.94/1.03      | X2 = sK5
% 2.94/1.03      | X6 = sK5
% 2.94/1.03      | X5 = sK5
% 2.94/1.03      | X4 = sK5
% 2.94/1.03      | X3 = sK5
% 2.94/1.03      | X7 = sK5 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_6289,plain,
% 2.94/1.03      ( ~ sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK5 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_6284]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_12,plain,
% 2.94/1.03      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.94/1.03      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.94/1.03      | ~ r2_hidden(X0,X9) ),
% 2.94/1.03      inference(cnf_transformation,[],[f83]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4442,plain,
% 2.94/1.03      ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)
% 2.94/1.03      | ~ r2_hidden(sK5,X0) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_6228,plain,
% 2.94/1.03      ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
% 2.94/1.03      | ~ r2_hidden(sK5,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_4442]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_6231,plain,
% 2.94/1.03      ( sP0(sK5,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | ~ sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.94/1.03      | ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_6228]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_28,plain,
% 2.94/1.03      ( r1_ordinal1(X0,X1)
% 2.94/1.03      | ~ r1_tarski(X0,X1)
% 2.94/1.03      | ~ v3_ordinal1(X0)
% 2.94/1.03      | ~ v3_ordinal1(X1) ),
% 2.94/1.03      inference(cnf_transformation,[],[f104]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_33,negated_conjecture,
% 2.94/1.03      ( ~ r1_ordinal1(sK5,sK6)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.03      inference(cnf_transformation,[],[f127]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_268,plain,
% 2.94/1.03      ( ~ r1_ordinal1(sK5,sK6)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.03      inference(prop_impl,[status(thm)],[c_33]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_646,plain,
% 2.94/1.03      ( ~ r1_tarski(X0,X1)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.03      | ~ v3_ordinal1(X0)
% 2.94/1.03      | ~ v3_ordinal1(X1)
% 2.94/1.03      | sK6 != X1
% 2.94/1.03      | sK5 != X0 ),
% 2.94/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_268]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_647,plain,
% 2.94/1.03      ( ~ r1_tarski(sK5,sK6)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.03      | ~ v3_ordinal1(sK6)
% 2.94/1.03      | ~ v3_ordinal1(sK5) ),
% 2.94/1.03      inference(unflattening,[status(thm)],[c_646]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_36,negated_conjecture,
% 2.94/1.03      ( v3_ordinal1(sK5) ),
% 2.94/1.03      inference(cnf_transformation,[],[f108]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_35,negated_conjecture,
% 2.94/1.03      ( v3_ordinal1(sK6) ),
% 2.94/1.03      inference(cnf_transformation,[],[f109]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_649,plain,
% 2.94/1.03      ( ~ r1_tarski(sK5,sK6)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.03      inference(global_propositional_subsumption,
% 2.94/1.03                [status(thm)],
% 2.94/1.03                [c_647,c_36,c_35]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_1531,plain,
% 2.94/1.03      ( ~ r1_tarski(sK5,sK6)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.03      inference(prop_impl,[status(thm)],[c_36,c_35,c_647]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3328,plain,
% 2.94/1.03      ( r1_tarski(sK5,sK6) != iProver_top
% 2.94/1.03      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_37,plain,
% 2.94/1.03      ( v3_ordinal1(sK5) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_38,plain,
% 2.94/1.03      ( v3_ordinal1(sK6) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_24,plain,
% 2.94/1.03      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 2.94/1.03      inference(cnf_transformation,[],[f98]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_65,plain,
% 2.94/1.03      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_67,plain,
% 2.94/1.03      ( v3_ordinal1(sK6) != iProver_top
% 2.94/1.03      | v1_ordinal1(sK6) = iProver_top ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_65]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_75,plain,
% 2.94/1.03      ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK6 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_20,plain,
% 2.94/1.03      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 2.94/1.03      inference(cnf_transformation,[],[f139]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_78,plain,
% 2.94/1.03      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_20]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_77,plain,
% 2.94/1.03      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_79,plain,
% 2.94/1.03      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = iProver_top ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_77]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_651,plain,
% 2.94/1.03      ( r1_tarski(sK5,sK6) != iProver_top
% 2.94/1.03      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_11,plain,
% 2.94/1.03      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.94/1.03      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.94/1.03      | r2_hidden(X0,X9) ),
% 2.94/1.03      inference(cnf_transformation,[],[f84]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_23,plain,
% 2.94/1.03      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.94/1.03      inference(cnf_transformation,[],[f140]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_796,plain,
% 2.94/1.03      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.94/1.03      | r2_hidden(X0,X9)
% 2.94/1.03      | X10 != X1
% 2.94/1.03      | X11 != X2
% 2.94/1.03      | X12 != X3
% 2.94/1.03      | X13 != X4
% 2.94/1.03      | X14 != X5
% 2.94/1.03      | X15 != X6
% 2.94/1.03      | X16 != X7
% 2.94/1.03      | X17 != X8
% 2.94/1.03      | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
% 2.94/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_797,plain,
% 2.94/1.03      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.94/1.03      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
% 2.94/1.03      inference(unflattening,[status(thm)],[c_796]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_798,plain,
% 2.94/1.03      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.94/1.03      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_800,plain,
% 2.94/1.03      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != iProver_top
% 2.94/1.03      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_798]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_27,plain,
% 2.94/1.03      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 2.94/1.03      inference(cnf_transformation,[],[f100]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_919,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,X1)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.03      | ~ v1_ordinal1(X1)
% 2.94/1.03      | sK6 != X1
% 2.94/1.03      | sK5 != X0 ),
% 2.94/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_649]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_920,plain,
% 2.94/1.03      ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.03      | ~ r2_hidden(sK5,sK6)
% 2.94/1.03      | ~ v1_ordinal1(sK6) ),
% 2.94/1.03      inference(unflattening,[status(thm)],[c_919]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_66,plain,
% 2.94/1.03      ( ~ v3_ordinal1(sK6) | v1_ordinal1(sK6) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_24]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_922,plain,
% 2.94/1.03      ( ~ r2_hidden(sK5,sK6)
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.03      inference(global_propositional_subsumption,
% 2.94/1.03                [status(thm)],
% 2.94/1.03                [c_920,c_35,c_66]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_923,plain,
% 2.94/1.03      ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.03      | ~ r2_hidden(sK5,sK6) ),
% 2.94/1.03      inference(renaming,[status(thm)],[c_922]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,X1)
% 2.94/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.94/1.03      inference(cnf_transformation,[],[f130]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_930,plain,
% 2.94/1.03      ( ~ r2_hidden(sK5,sK6) ),
% 2.94/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_923,c_4]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_932,plain,
% 2.94/1.03      ( r2_hidden(sK5,sK6) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_2566,plain,
% 2.94/1.03      ( X0 != X1
% 2.94/1.03      | X2 != X3
% 2.94/1.03      | X4 != X5
% 2.94/1.03      | X6 != X7
% 2.94/1.03      | X8 != X9
% 2.94/1.03      | X10 != X11
% 2.94/1.03      | X12 != X13
% 2.94/1.03      | X14 != X15
% 2.94/1.03      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.94/1.03      theory(equality) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_2573,plain,
% 2.94/1.03      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | sK6 != sK6 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_2566]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_32,plain,
% 2.94/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.94/1.03      inference(cnf_transformation,[],[f107]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3602,plain,
% 2.94/1.03      ( ~ r1_tarski(sK5,sK6) | ~ r2_hidden(sK6,sK5) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_32]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3603,plain,
% 2.94/1.03      ( r1_tarski(sK5,sK6) != iProver_top
% 2.94/1.03      | r2_hidden(sK6,sK5) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_3602]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_6,plain,
% 2.94/1.03      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.94/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_30,plain,
% 2.94/1.03      ( ~ r2_xboole_0(X0,X1)
% 2.94/1.03      | r2_hidden(X0,X1)
% 2.94/1.03      | ~ v3_ordinal1(X1)
% 2.94/1.03      | ~ v1_ordinal1(X0) ),
% 2.94/1.03      inference(cnf_transformation,[],[f105]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_458,plain,
% 2.94/1.03      ( ~ r1_tarski(X0,X1)
% 2.94/1.03      | r2_hidden(X0,X1)
% 2.94/1.03      | ~ v3_ordinal1(X1)
% 2.94/1.03      | ~ v1_ordinal1(X0)
% 2.94/1.03      | X1 = X0 ),
% 2.94/1.03      inference(resolution,[status(thm)],[c_6,c_30]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3878,plain,
% 2.94/1.03      ( ~ r1_tarski(X0,sK5)
% 2.94/1.03      | r2_hidden(X0,sK5)
% 2.94/1.03      | ~ v3_ordinal1(sK5)
% 2.94/1.03      | ~ v1_ordinal1(X0)
% 2.94/1.03      | sK5 = X0 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_458]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3879,plain,
% 2.94/1.03      ( sK5 = X0
% 2.94/1.03      | r1_tarski(X0,sK5) != iProver_top
% 2.94/1.03      | r2_hidden(X0,sK5) = iProver_top
% 2.94/1.03      | v3_ordinal1(sK5) != iProver_top
% 2.94/1.03      | v1_ordinal1(X0) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_3878]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3881,plain,
% 2.94/1.03      ( sK5 = sK6
% 2.94/1.03      | r1_tarski(sK6,sK5) != iProver_top
% 2.94/1.03      | r2_hidden(sK6,sK5) = iProver_top
% 2.94/1.03      | v3_ordinal1(sK5) != iProver_top
% 2.94/1.03      | v1_ordinal1(sK6) != iProver_top ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_3879]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,X1)
% 2.94/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.94/1.03      inference(cnf_transformation,[],[f129]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3765,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 2.94/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4002,plain,
% 2.94/1.03      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.94/1.03      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_3765]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4003,plain,
% 2.94/1.03      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.94/1.03      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_4002]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_31,plain,
% 2.94/1.03      ( r1_ordinal1(X0,X1)
% 2.94/1.03      | r2_hidden(X1,X0)
% 2.94/1.03      | ~ v3_ordinal1(X0)
% 2.94/1.03      | ~ v3_ordinal1(X1) ),
% 2.94/1.03      inference(cnf_transformation,[],[f106]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_29,plain,
% 2.94/1.03      ( ~ r1_ordinal1(X0,X1)
% 2.94/1.03      | r1_tarski(X0,X1)
% 2.94/1.03      | ~ v3_ordinal1(X0)
% 2.94/1.03      | ~ v3_ordinal1(X1) ),
% 2.94/1.03      inference(cnf_transformation,[],[f103]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_613,plain,
% 2.94/1.03      ( r1_tarski(X0,X1)
% 2.94/1.03      | r2_hidden(X1,X0)
% 2.94/1.03      | ~ v3_ordinal1(X0)
% 2.94/1.03      | ~ v3_ordinal1(X1) ),
% 2.94/1.03      inference(resolution,[status(thm)],[c_31,c_29]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4303,plain,
% 2.94/1.03      ( r1_tarski(X0,sK5)
% 2.94/1.03      | r2_hidden(sK5,X0)
% 2.94/1.03      | ~ v3_ordinal1(X0)
% 2.94/1.03      | ~ v3_ordinal1(sK5) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_613]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4309,plain,
% 2.94/1.03      ( r1_tarski(X0,sK5) = iProver_top
% 2.94/1.03      | r2_hidden(sK5,X0) = iProver_top
% 2.94/1.03      | v3_ordinal1(X0) != iProver_top
% 2.94/1.03      | v3_ordinal1(sK5) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_4303]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_4311,plain,
% 2.94/1.03      ( r1_tarski(sK6,sK5) = iProver_top
% 2.94/1.03      | r2_hidden(sK5,sK6) = iProver_top
% 2.94/1.03      | v3_ordinal1(sK6) != iProver_top
% 2.94/1.03      | v3_ordinal1(sK5) != iProver_top ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_4309]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_2568,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.94/1.03      theory(equality) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3766,plain,
% 2.94/1.03      ( r2_hidden(X0,X1)
% 2.94/1.03      | ~ r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
% 2.94/1.03      | X0 != X2
% 2.94/1.03      | X1 != k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_2568]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3943,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 2.94/1.03      | r2_hidden(X9,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 2.94/1.03      | X9 != X0
% 2.94/1.03      | k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_3766]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_5038,plain,
% 2.94/1.03      ( ~ r2_hidden(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.94/1.03      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.94/1.03      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | sK5 != X0 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_3943]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_5039,plain,
% 2.94/1.03      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | sK5 != X0
% 2.94/1.03      | r2_hidden(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.94/1.03      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_5038]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_5041,plain,
% 2.94/1.03      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.94/1.03      | sK5 != sK6
% 2.94/1.03      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.94/1.03      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_5039]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_5304,plain,
% 2.94/1.03      ( r1_tarski(sK5,sK6) != iProver_top ),
% 2.94/1.03      inference(global_propositional_subsumption,
% 2.94/1.03                [status(thm)],
% 2.94/1.03                [c_3328,c_37,c_38,c_67,c_75,c_78,c_79,c_651,c_800,c_932,
% 2.94/1.03                 c_2573,c_3603,c_3881,c_4003,c_4311,c_5041]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3331,plain,
% 2.94/1.03      ( v3_ordinal1(sK5) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3337,plain,
% 2.94/1.03      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3650,plain,
% 2.94/1.03      ( v1_ordinal1(sK5) = iProver_top ),
% 2.94/1.03      inference(superposition,[status(thm)],[c_3331,c_3337]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3656,plain,
% 2.94/1.03      ( v1_ordinal1(sK5) ),
% 2.94/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3650]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_5,plain,
% 2.94/1.03      ( r2_hidden(X0,X1)
% 2.94/1.03      | r2_hidden(X0,X2)
% 2.94/1.03      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.94/1.03      inference(cnf_transformation,[],[f131]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3643,plain,
% 2.94/1.03      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.94/1.03      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.03      | r2_hidden(sK5,sK6) ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3618,plain,
% 2.94/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(sK6,sK5) | X0 != sK6 | X1 != sK5 ),
% 2.94/1.03      inference(instantiation,[status(thm)],[c_2568]) ).
% 2.94/1.03  
% 2.94/1.03  cnf(c_3619,plain,
% 2.94/1.03      ( X0 != sK6
% 2.94/1.03      | X1 != sK5
% 2.94/1.03      | r2_hidden(X0,X1) = iProver_top
% 2.94/1.03      | r2_hidden(sK6,sK5) != iProver_top ),
% 2.94/1.03      inference(predicate_to_equality,[status(thm)],[c_3618]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_3621,plain,
% 2.94/1.04      ( sK6 != sK6
% 2.94/1.04      | sK6 != sK5
% 2.94/1.04      | r2_hidden(sK6,sK6) = iProver_top
% 2.94/1.04      | r2_hidden(sK6,sK5) != iProver_top ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_3619]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_632,plain,
% 2.94/1.04      ( r2_hidden(X0,X1)
% 2.94/1.04      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | ~ v3_ordinal1(X1)
% 2.94/1.04      | ~ v3_ordinal1(X0)
% 2.94/1.04      | sK6 != X0
% 2.94/1.04      | sK5 != X1 ),
% 2.94/1.04      inference(resolution_lifted,[status(thm)],[c_31,c_268]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_633,plain,
% 2.94/1.04      ( r2_hidden(sK6,sK5)
% 2.94/1.04      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | ~ v3_ordinal1(sK6)
% 2.94/1.04      | ~ v3_ordinal1(sK5) ),
% 2.94/1.04      inference(unflattening,[status(thm)],[c_632]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_635,plain,
% 2.94/1.04      ( r2_hidden(sK6,sK5)
% 2.94/1.04      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.04      inference(global_propositional_subsumption,
% 2.94/1.04                [status(thm)],
% 2.94/1.04                [c_633,c_36,c_35]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_34,negated_conjecture,
% 2.94/1.04      ( r1_ordinal1(sK5,sK6)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.04      inference(cnf_transformation,[],[f128]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_270,plain,
% 2.94/1.04      ( r1_ordinal1(sK5,sK6)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.04      inference(prop_impl,[status(thm)],[c_34]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_660,plain,
% 2.94/1.04      ( r1_tarski(X0,X1)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | ~ v3_ordinal1(X0)
% 2.94/1.04      | ~ v3_ordinal1(X1)
% 2.94/1.04      | sK6 != X1
% 2.94/1.04      | sK5 != X0 ),
% 2.94/1.04      inference(resolution_lifted,[status(thm)],[c_29,c_270]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_661,plain,
% 2.94/1.04      ( r1_tarski(sK5,sK6)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | ~ v3_ordinal1(sK6)
% 2.94/1.04      | ~ v3_ordinal1(sK5) ),
% 2.94/1.04      inference(unflattening,[status(thm)],[c_660]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_663,plain,
% 2.94/1.04      ( r1_tarski(sK5,sK6)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.04      inference(global_propositional_subsumption,
% 2.94/1.04                [status(thm)],
% 2.94/1.04                [c_661,c_36,c_35]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_1533,plain,
% 2.94/1.04      ( r1_tarski(sK5,sK6)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.94/1.04      inference(prop_impl,[status(thm)],[c_36,c_35,c_661]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_1597,plain,
% 2.94/1.04      ( r1_tarski(sK5,sK6) | r2_hidden(sK6,sK5) ),
% 2.94/1.04      inference(bin_hyper_res,[status(thm)],[c_635,c_1533]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_1606,plain,
% 2.94/1.04      ( r1_tarski(sK5,sK6) = iProver_top
% 2.94/1.04      | r2_hidden(sK6,sK5) = iProver_top ),
% 2.94/1.04      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_933,plain,
% 2.94/1.04      ( r2_hidden(X0,X1)
% 2.94/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | ~ v3_ordinal1(X1)
% 2.94/1.04      | ~ v1_ordinal1(X0)
% 2.94/1.04      | X1 = X0
% 2.94/1.04      | sK6 != X1
% 2.94/1.04      | sK5 != X0 ),
% 2.94/1.04      inference(resolution_lifted,[status(thm)],[c_458,c_663]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_934,plain,
% 2.94/1.04      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | r2_hidden(sK5,sK6)
% 2.94/1.04      | ~ v3_ordinal1(sK6)
% 2.94/1.04      | ~ v1_ordinal1(sK5)
% 2.94/1.04      | sK6 = sK5 ),
% 2.94/1.04      inference(unflattening,[status(thm)],[c_933]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_936,plain,
% 2.94/1.04      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.94/1.04      | ~ v1_ordinal1(sK5)
% 2.94/1.04      | sK6 = sK5 ),
% 2.94/1.04      inference(global_propositional_subsumption,
% 2.94/1.04                [status(thm)],
% 2.94/1.04                [c_934,c_35,c_930]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_862,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) | ~ v1_ordinal1(X1) ),
% 2.94/1.04      inference(resolution,[status(thm)],[c_27,c_32]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_863,plain,
% 2.94/1.04      ( r2_hidden(X0,X1) != iProver_top
% 2.94/1.04      | r2_hidden(X1,X0) != iProver_top
% 2.94/1.04      | v1_ordinal1(X0) != iProver_top ),
% 2.94/1.04      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_865,plain,
% 2.94/1.04      ( r2_hidden(sK6,sK6) != iProver_top
% 2.94/1.04      | v1_ordinal1(sK6) != iProver_top ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_863]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_69,plain,
% 2.94/1.04      ( sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_23]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(contradiction,plain,
% 2.94/1.04      ( $false ),
% 2.94/1.04      inference(minisat,
% 2.94/1.04                [status(thm)],
% 2.94/1.04                [c_6289,c_6231,c_5304,c_3656,c_3643,c_3621,c_1606,c_936,
% 2.94/1.04                 c_930,c_865,c_78,c_75,c_69,c_67,c_38]) ).
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.04  
% 2.94/1.04  ------                               Statistics
% 2.94/1.04  
% 2.94/1.04  ------ General
% 2.94/1.04  
% 2.94/1.04  abstr_ref_over_cycles:                  0
% 2.94/1.04  abstr_ref_under_cycles:                 0
% 2.94/1.04  gc_basic_clause_elim:                   0
% 2.94/1.04  forced_gc_time:                         0
% 2.94/1.04  parsing_time:                           0.013
% 2.94/1.04  unif_index_cands_time:                  0.
% 2.94/1.04  unif_index_add_time:                    0.
% 2.94/1.04  orderings_time:                         0.
% 2.94/1.04  out_proof_time:                         0.011
% 2.94/1.04  total_time:                             0.228
% 2.94/1.04  num_of_symbols:                         43
% 2.94/1.04  num_of_terms:                           5516
% 2.94/1.04  
% 2.94/1.04  ------ Preprocessing
% 2.94/1.04  
% 2.94/1.04  num_of_splits:                          0
% 2.94/1.04  num_of_split_atoms:                     0
% 2.94/1.04  num_of_reused_defs:                     0
% 2.94/1.04  num_eq_ax_congr_red:                    92
% 2.94/1.04  num_of_sem_filtered_clauses:            1
% 2.94/1.04  num_of_subtypes:                        0
% 2.94/1.04  monotx_restored_types:                  0
% 2.94/1.04  sat_num_of_epr_types:                   0
% 2.94/1.04  sat_num_of_non_cyclic_types:            0
% 2.94/1.04  sat_guarded_non_collapsed_types:        0
% 2.94/1.04  num_pure_diseq_elim:                    0
% 2.94/1.04  simp_replaced_by:                       0
% 2.94/1.04  res_preprocessed:                       161
% 2.94/1.04  prep_upred:                             0
% 2.94/1.04  prep_unflattend:                        653
% 2.94/1.04  smt_new_axioms:                         0
% 2.94/1.04  pred_elim_cands:                        6
% 2.94/1.04  pred_elim:                              2
% 2.94/1.04  pred_elim_cl:                           2
% 2.94/1.04  pred_elim_cycles:                       10
% 2.94/1.04  merged_defs:                            8
% 2.94/1.04  merged_defs_ncl:                        0
% 2.94/1.04  bin_hyper_res:                          9
% 2.94/1.04  prep_cycles:                            4
% 2.94/1.04  pred_elim_time:                         0.04
% 2.94/1.04  splitting_time:                         0.
% 2.94/1.04  sem_filter_time:                        0.
% 2.94/1.04  monotx_time:                            0.
% 2.94/1.04  subtype_inf_time:                       0.
% 2.94/1.04  
% 2.94/1.04  ------ Problem properties
% 2.94/1.04  
% 2.94/1.04  clauses:                                35
% 2.94/1.04  conjectures:                            2
% 2.94/1.04  epr:                                    19
% 2.94/1.04  horn:                                   26
% 2.94/1.04  ground:                                 5
% 2.94/1.04  unary:                                  12
% 2.94/1.04  binary:                                 11
% 2.94/1.04  lits:                                   80
% 2.94/1.04  lits_eq:                                14
% 2.94/1.04  fd_pure:                                0
% 2.94/1.04  fd_pseudo:                              0
% 2.94/1.04  fd_cond:                                0
% 2.94/1.04  fd_pseudo_cond:                         6
% 2.94/1.04  ac_symbols:                             0
% 2.94/1.04  
% 2.94/1.04  ------ Propositional Solver
% 2.94/1.04  
% 2.94/1.04  prop_solver_calls:                      27
% 2.94/1.04  prop_fast_solver_calls:                 1243
% 2.94/1.04  smt_solver_calls:                       0
% 2.94/1.04  smt_fast_solver_calls:                  0
% 2.94/1.04  prop_num_of_clauses:                    1594
% 2.94/1.04  prop_preprocess_simplified:             7703
% 2.94/1.04  prop_fo_subsumed:                       27
% 2.94/1.04  prop_solver_time:                       0.
% 2.94/1.04  smt_solver_time:                        0.
% 2.94/1.04  smt_fast_solver_time:                   0.
% 2.94/1.04  prop_fast_solver_time:                  0.
% 2.94/1.04  prop_unsat_core_time:                   0.
% 2.94/1.04  
% 2.94/1.04  ------ QBF
% 2.94/1.04  
% 2.94/1.04  qbf_q_res:                              0
% 2.94/1.04  qbf_num_tautologies:                    0
% 2.94/1.04  qbf_prep_cycles:                        0
% 2.94/1.04  
% 2.94/1.04  ------ BMC1
% 2.94/1.04  
% 2.94/1.04  bmc1_current_bound:                     -1
% 2.94/1.04  bmc1_last_solved_bound:                 -1
% 2.94/1.04  bmc1_unsat_core_size:                   -1
% 2.94/1.04  bmc1_unsat_core_parents_size:           -1
% 2.94/1.04  bmc1_merge_next_fun:                    0
% 2.94/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.04  
% 2.94/1.04  ------ Instantiation
% 2.94/1.04  
% 2.94/1.04  inst_num_of_clauses:                    415
% 2.94/1.04  inst_num_in_passive:                    228
% 2.94/1.04  inst_num_in_active:                     160
% 2.94/1.04  inst_num_in_unprocessed:                26
% 2.94/1.04  inst_num_of_loops:                      214
% 2.94/1.04  inst_num_of_learning_restarts:          0
% 2.94/1.04  inst_num_moves_active_passive:          51
% 2.94/1.04  inst_lit_activity:                      0
% 2.94/1.04  inst_lit_activity_moves:                0
% 2.94/1.04  inst_num_tautologies:                   0
% 2.94/1.04  inst_num_prop_implied:                  0
% 2.94/1.04  inst_num_existing_simplified:           0
% 2.94/1.04  inst_num_eq_res_simplified:             0
% 2.94/1.04  inst_num_child_elim:                    0
% 2.94/1.04  inst_num_of_dismatching_blockings:      101
% 2.94/1.04  inst_num_of_non_proper_insts:           328
% 2.94/1.04  inst_num_of_duplicates:                 0
% 2.94/1.04  inst_inst_num_from_inst_to_res:         0
% 2.94/1.04  inst_dismatching_checking_time:         0.
% 2.94/1.04  
% 2.94/1.04  ------ Resolution
% 2.94/1.04  
% 2.94/1.04  res_num_of_clauses:                     0
% 2.94/1.04  res_num_in_passive:                     0
% 2.94/1.04  res_num_in_active:                      0
% 2.94/1.04  res_num_of_loops:                       165
% 2.94/1.04  res_forward_subset_subsumed:            26
% 2.94/1.04  res_backward_subset_subsumed:           0
% 2.94/1.04  res_forward_subsumed:                   2
% 2.94/1.04  res_backward_subsumed:                  0
% 2.94/1.04  res_forward_subsumption_resolution:     1
% 2.94/1.04  res_backward_subsumption_resolution:    0
% 2.94/1.04  res_clause_to_clause_subsumption:       945
% 2.94/1.04  res_orphan_elimination:                 0
% 2.94/1.04  res_tautology_del:                      68
% 2.94/1.04  res_num_eq_res_simplified:              0
% 2.94/1.04  res_num_sel_changes:                    0
% 2.94/1.04  res_moves_from_active_to_pass:          0
% 2.94/1.04  
% 2.94/1.04  ------ Superposition
% 2.94/1.04  
% 2.94/1.04  sup_time_total:                         0.
% 2.94/1.04  sup_time_generating:                    0.
% 2.94/1.04  sup_time_sim_full:                      0.
% 2.94/1.04  sup_time_sim_immed:                     0.
% 2.94/1.04  
% 2.94/1.04  sup_num_of_clauses:                     68
% 2.94/1.04  sup_num_in_active:                      42
% 2.94/1.04  sup_num_in_passive:                     26
% 2.94/1.04  sup_num_of_loops:                       42
% 2.94/1.04  sup_fw_superposition:                   32
% 2.94/1.04  sup_bw_superposition:                   9
% 2.94/1.04  sup_immediate_simplified:               1
% 2.94/1.04  sup_given_eliminated:                   0
% 2.94/1.04  comparisons_done:                       0
% 2.94/1.04  comparisons_avoided:                    0
% 2.94/1.04  
% 2.94/1.04  ------ Simplifications
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  sim_fw_subset_subsumed:                 0
% 2.94/1.04  sim_bw_subset_subsumed:                 0
% 2.94/1.04  sim_fw_subsumed:                        0
% 2.94/1.04  sim_bw_subsumed:                        0
% 2.94/1.04  sim_fw_subsumption_res:                 0
% 2.94/1.04  sim_bw_subsumption_res:                 0
% 2.94/1.04  sim_tautology_del:                      6
% 2.94/1.04  sim_eq_tautology_del:                   1
% 2.94/1.04  sim_eq_res_simp:                        0
% 2.94/1.04  sim_fw_demodulated:                     0
% 2.94/1.04  sim_bw_demodulated:                     0
% 2.94/1.04  sim_light_normalised:                   1
% 2.94/1.04  sim_joinable_taut:                      0
% 2.94/1.04  sim_joinable_simp:                      0
% 2.94/1.04  sim_ac_normalised:                      0
% 2.94/1.04  sim_smt_subsumption:                    0
% 2.94/1.04  
%------------------------------------------------------------------------------
