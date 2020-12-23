%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:24 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 311 expanded)
%              Number of clauses        :   39 (  47 expanded)
%              Number of leaves         :   19 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  431 (1174 expanded)
%              Number of equality atoms :  241 ( 579 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK5 != sK6
          & ~ r2_hidden(sK5,sK6) )
        | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
      & ( sK5 = sK6
        | r2_hidden(sK5,sK6)
        | r2_hidden(sK5,k1_ordinal1(sK6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ( sK5 != sK6
        & ~ r2_hidden(sK5,sK6) )
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( sK5 = sK6
      | r2_hidden(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).

fof(f76,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f94,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,sK6)
    | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f78,plain,
    ( sK5 != sK6
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( sK5 != sK6
    | ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
    inference(definition_unfolding,[],[f78,f85])).

fof(f77,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
    inference(definition_unfolding,[],[f77,f85])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f83])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f100,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f90])).

fof(f101,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f100])).

fof(f16,plain,(
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

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f65])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f35])).

cnf(c_856,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1595,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_2086,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_2088,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_853,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1754,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_854,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1581,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_1753,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1689,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k2_xboole_0(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1691,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
    | r2_hidden(sK5,sK6)
    | sK5 = sK6 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1336,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1361,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1419,plain,
    ( sK6 = sK5
    | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1336,c_1361])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_32,plain,
    ( sK5 != sK6
    | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
    | ~ r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1337,plain,
    ( r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1414,plain,
    ( r2_hidden(sK5,sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1337,c_1361])).

cnf(c_1512,plain,
    ( ~ r2_hidden(sK5,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1414])).

cnf(c_1527,plain,
    ( r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
    | sK6 = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1419])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1582,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
    | r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1619,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
    | sK5 = X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1621,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_1625,plain,
    ( sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1419,c_32,c_1512,c_1527,c_1582,c_1621])).

cnf(c_857,plain,
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

cnf(c_862,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_10,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_66,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_43,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X4 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X3 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_40,plain,
    ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2088,c_1754,c_1753,c_1691,c_1625,c_862,c_66,c_43,c_40,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.50/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.00  
% 1.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.50/1.00  
% 1.50/1.00  ------  iProver source info
% 1.50/1.00  
% 1.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.50/1.00  git: non_committed_changes: false
% 1.50/1.00  git: last_make_outside_of_git: false
% 1.50/1.00  
% 1.50/1.00  ------ 
% 1.50/1.00  
% 1.50/1.00  ------ Input Options
% 1.50/1.00  
% 1.50/1.00  --out_options                           all
% 1.50/1.00  --tptp_safe_out                         true
% 1.50/1.00  --problem_path                          ""
% 1.50/1.00  --include_path                          ""
% 1.50/1.00  --clausifier                            res/vclausify_rel
% 1.50/1.00  --clausifier_options                    --mode clausify
% 1.50/1.00  --stdin                                 false
% 1.50/1.00  --stats_out                             all
% 1.50/1.00  
% 1.50/1.00  ------ General Options
% 1.50/1.00  
% 1.50/1.00  --fof                                   false
% 1.50/1.00  --time_out_real                         305.
% 1.50/1.00  --time_out_virtual                      -1.
% 1.50/1.00  --symbol_type_check                     false
% 1.50/1.00  --clausify_out                          false
% 1.50/1.00  --sig_cnt_out                           false
% 1.50/1.00  --trig_cnt_out                          false
% 1.50/1.00  --trig_cnt_out_tolerance                1.
% 1.50/1.00  --trig_cnt_out_sk_spl                   false
% 1.50/1.00  --abstr_cl_out                          false
% 1.50/1.00  
% 1.50/1.00  ------ Global Options
% 1.50/1.00  
% 1.50/1.00  --schedule                              default
% 1.50/1.00  --add_important_lit                     false
% 1.50/1.00  --prop_solver_per_cl                    1000
% 1.50/1.00  --min_unsat_core                        false
% 1.50/1.00  --soft_assumptions                      false
% 1.50/1.00  --soft_lemma_size                       3
% 1.50/1.00  --prop_impl_unit_size                   0
% 1.50/1.00  --prop_impl_unit                        []
% 1.50/1.00  --share_sel_clauses                     true
% 1.50/1.00  --reset_solvers                         false
% 1.50/1.00  --bc_imp_inh                            [conj_cone]
% 1.50/1.00  --conj_cone_tolerance                   3.
% 1.50/1.00  --extra_neg_conj                        none
% 1.50/1.00  --large_theory_mode                     true
% 1.50/1.00  --prolific_symb_bound                   200
% 1.50/1.00  --lt_threshold                          2000
% 1.50/1.00  --clause_weak_htbl                      true
% 1.50/1.00  --gc_record_bc_elim                     false
% 1.50/1.00  
% 1.50/1.00  ------ Preprocessing Options
% 1.50/1.00  
% 1.50/1.00  --preprocessing_flag                    true
% 1.50/1.00  --time_out_prep_mult                    0.1
% 1.50/1.00  --splitting_mode                        input
% 1.50/1.00  --splitting_grd                         true
% 1.50/1.00  --splitting_cvd                         false
% 1.50/1.00  --splitting_cvd_svl                     false
% 1.50/1.00  --splitting_nvd                         32
% 1.50/1.00  --sub_typing                            true
% 1.50/1.00  --prep_gs_sim                           true
% 1.50/1.00  --prep_unflatten                        true
% 1.50/1.00  --prep_res_sim                          true
% 1.50/1.00  --prep_upred                            true
% 1.50/1.00  --prep_sem_filter                       exhaustive
% 1.50/1.00  --prep_sem_filter_out                   false
% 1.50/1.00  --pred_elim                             true
% 1.50/1.00  --res_sim_input                         true
% 1.50/1.00  --eq_ax_congr_red                       true
% 1.50/1.00  --pure_diseq_elim                       true
% 1.50/1.00  --brand_transform                       false
% 1.50/1.00  --non_eq_to_eq                          false
% 1.50/1.00  --prep_def_merge                        true
% 1.50/1.00  --prep_def_merge_prop_impl              false
% 1.50/1.00  --prep_def_merge_mbd                    true
% 1.50/1.00  --prep_def_merge_tr_red                 false
% 1.50/1.00  --prep_def_merge_tr_cl                  false
% 1.50/1.00  --smt_preprocessing                     true
% 1.50/1.00  --smt_ac_axioms                         fast
% 1.50/1.00  --preprocessed_out                      false
% 1.50/1.00  --preprocessed_stats                    false
% 1.50/1.00  
% 1.50/1.00  ------ Abstraction refinement Options
% 1.50/1.00  
% 1.50/1.00  --abstr_ref                             []
% 1.50/1.00  --abstr_ref_prep                        false
% 1.50/1.00  --abstr_ref_until_sat                   false
% 1.50/1.00  --abstr_ref_sig_restrict                funpre
% 1.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/1.00  --abstr_ref_under                       []
% 1.50/1.00  
% 1.50/1.00  ------ SAT Options
% 1.50/1.00  
% 1.50/1.00  --sat_mode                              false
% 1.50/1.00  --sat_fm_restart_options                ""
% 1.50/1.00  --sat_gr_def                            false
% 1.50/1.00  --sat_epr_types                         true
% 1.50/1.00  --sat_non_cyclic_types                  false
% 1.50/1.00  --sat_finite_models                     false
% 1.50/1.00  --sat_fm_lemmas                         false
% 1.50/1.00  --sat_fm_prep                           false
% 1.50/1.00  --sat_fm_uc_incr                        true
% 1.50/1.00  --sat_out_model                         small
% 1.50/1.00  --sat_out_clauses                       false
% 1.50/1.00  
% 1.50/1.00  ------ QBF Options
% 1.50/1.00  
% 1.50/1.00  --qbf_mode                              false
% 1.50/1.00  --qbf_elim_univ                         false
% 1.50/1.00  --qbf_dom_inst                          none
% 1.50/1.00  --qbf_dom_pre_inst                      false
% 1.50/1.00  --qbf_sk_in                             false
% 1.50/1.00  --qbf_pred_elim                         true
% 1.50/1.00  --qbf_split                             512
% 1.50/1.00  
% 1.50/1.00  ------ BMC1 Options
% 1.50/1.00  
% 1.50/1.00  --bmc1_incremental                      false
% 1.50/1.00  --bmc1_axioms                           reachable_all
% 1.50/1.00  --bmc1_min_bound                        0
% 1.50/1.00  --bmc1_max_bound                        -1
% 1.50/1.00  --bmc1_max_bound_default                -1
% 1.50/1.00  --bmc1_symbol_reachability              true
% 1.50/1.00  --bmc1_property_lemmas                  false
% 1.50/1.00  --bmc1_k_induction                      false
% 1.50/1.00  --bmc1_non_equiv_states                 false
% 1.50/1.00  --bmc1_deadlock                         false
% 1.50/1.00  --bmc1_ucm                              false
% 1.50/1.00  --bmc1_add_unsat_core                   none
% 1.50/1.00  --bmc1_unsat_core_children              false
% 1.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/1.00  --bmc1_out_stat                         full
% 1.50/1.00  --bmc1_ground_init                      false
% 1.50/1.00  --bmc1_pre_inst_next_state              false
% 1.50/1.00  --bmc1_pre_inst_state                   false
% 1.50/1.00  --bmc1_pre_inst_reach_state             false
% 1.50/1.00  --bmc1_out_unsat_core                   false
% 1.50/1.00  --bmc1_aig_witness_out                  false
% 1.50/1.00  --bmc1_verbose                          false
% 1.50/1.00  --bmc1_dump_clauses_tptp                false
% 1.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.50/1.00  --bmc1_dump_file                        -
% 1.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.50/1.00  --bmc1_ucm_extend_mode                  1
% 1.50/1.00  --bmc1_ucm_init_mode                    2
% 1.50/1.00  --bmc1_ucm_cone_mode                    none
% 1.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.50/1.00  --bmc1_ucm_relax_model                  4
% 1.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/1.00  --bmc1_ucm_layered_model                none
% 1.50/1.00  --bmc1_ucm_max_lemma_size               10
% 1.50/1.00  
% 1.50/1.00  ------ AIG Options
% 1.50/1.00  
% 1.50/1.00  --aig_mode                              false
% 1.50/1.00  
% 1.50/1.00  ------ Instantiation Options
% 1.50/1.00  
% 1.50/1.00  --instantiation_flag                    true
% 1.50/1.00  --inst_sos_flag                         false
% 1.50/1.00  --inst_sos_phase                        true
% 1.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/1.00  --inst_lit_sel_side                     num_symb
% 1.50/1.00  --inst_solver_per_active                1400
% 1.50/1.00  --inst_solver_calls_frac                1.
% 1.50/1.00  --inst_passive_queue_type               priority_queues
% 1.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/1.00  --inst_passive_queues_freq              [25;2]
% 1.50/1.00  --inst_dismatching                      true
% 1.50/1.00  --inst_eager_unprocessed_to_passive     true
% 1.50/1.00  --inst_prop_sim_given                   true
% 1.50/1.00  --inst_prop_sim_new                     false
% 1.50/1.00  --inst_subs_new                         false
% 1.50/1.00  --inst_eq_res_simp                      false
% 1.50/1.00  --inst_subs_given                       false
% 1.50/1.00  --inst_orphan_elimination               true
% 1.50/1.00  --inst_learning_loop_flag               true
% 1.50/1.00  --inst_learning_start                   3000
% 1.50/1.00  --inst_learning_factor                  2
% 1.50/1.00  --inst_start_prop_sim_after_learn       3
% 1.50/1.00  --inst_sel_renew                        solver
% 1.50/1.00  --inst_lit_activity_flag                true
% 1.50/1.00  --inst_restr_to_given                   false
% 1.50/1.00  --inst_activity_threshold               500
% 1.50/1.00  --inst_out_proof                        true
% 1.50/1.00  
% 1.50/1.00  ------ Resolution Options
% 1.50/1.00  
% 1.50/1.00  --resolution_flag                       true
% 1.50/1.00  --res_lit_sel                           adaptive
% 1.50/1.00  --res_lit_sel_side                      none
% 1.50/1.00  --res_ordering                          kbo
% 1.50/1.00  --res_to_prop_solver                    active
% 1.50/1.00  --res_prop_simpl_new                    false
% 1.50/1.00  --res_prop_simpl_given                  true
% 1.50/1.00  --res_passive_queue_type                priority_queues
% 1.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/1.00  --res_passive_queues_freq               [15;5]
% 1.50/1.00  --res_forward_subs                      full
% 1.50/1.00  --res_backward_subs                     full
% 1.50/1.00  --res_forward_subs_resolution           true
% 1.50/1.00  --res_backward_subs_resolution          true
% 1.50/1.00  --res_orphan_elimination                true
% 1.50/1.00  --res_time_limit                        2.
% 1.50/1.00  --res_out_proof                         true
% 1.50/1.00  
% 1.50/1.00  ------ Superposition Options
% 1.50/1.00  
% 1.50/1.00  --superposition_flag                    true
% 1.50/1.00  --sup_passive_queue_type                priority_queues
% 1.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.50/1.00  --demod_completeness_check              fast
% 1.50/1.00  --demod_use_ground                      true
% 1.50/1.00  --sup_to_prop_solver                    passive
% 1.50/1.00  --sup_prop_simpl_new                    true
% 1.50/1.00  --sup_prop_simpl_given                  true
% 1.50/1.00  --sup_fun_splitting                     false
% 1.50/1.00  --sup_smt_interval                      50000
% 1.50/1.00  
% 1.50/1.00  ------ Superposition Simplification Setup
% 1.50/1.00  
% 1.50/1.00  --sup_indices_passive                   []
% 1.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.00  --sup_full_bw                           [BwDemod]
% 1.50/1.00  --sup_immed_triv                        [TrivRules]
% 1.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.00  --sup_immed_bw_main                     []
% 1.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.00  
% 1.50/1.00  ------ Combination Options
% 1.50/1.00  
% 1.50/1.00  --comb_res_mult                         3
% 1.50/1.00  --comb_sup_mult                         2
% 1.50/1.00  --comb_inst_mult                        10
% 1.50/1.00  
% 1.50/1.00  ------ Debug Options
% 1.50/1.00  
% 1.50/1.00  --dbg_backtrace                         false
% 1.50/1.00  --dbg_dump_prop_clauses                 false
% 1.50/1.00  --dbg_dump_prop_clauses_file            -
% 1.50/1.00  --dbg_out_stat                          false
% 1.50/1.00  ------ Parsing...
% 1.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.50/1.00  
% 1.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.50/1.00  
% 1.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.50/1.00  
% 1.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.50/1.00  ------ Proving...
% 1.50/1.00  ------ Problem Properties 
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  clauses                                 30
% 1.50/1.00  conjectures                             3
% 1.50/1.00  EPR                                     11
% 1.50/1.00  Horn                                    23
% 1.50/1.00  unary                                   11
% 1.50/1.00  binary                                  5
% 1.50/1.00  lits                                    71
% 1.50/1.00  lits eq                                 23
% 1.50/1.00  fd_pure                                 0
% 1.50/1.00  fd_pseudo                               0
% 1.50/1.00  fd_cond                                 0
% 1.50/1.00  fd_pseudo_cond                          8
% 1.50/1.00  AC symbols                              0
% 1.50/1.00  
% 1.50/1.00  ------ Schedule dynamic 5 is on 
% 1.50/1.00  
% 1.50/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  ------ 
% 1.50/1.00  Current options:
% 1.50/1.00  ------ 
% 1.50/1.00  
% 1.50/1.00  ------ Input Options
% 1.50/1.00  
% 1.50/1.00  --out_options                           all
% 1.50/1.00  --tptp_safe_out                         true
% 1.50/1.00  --problem_path                          ""
% 1.50/1.00  --include_path                          ""
% 1.50/1.00  --clausifier                            res/vclausify_rel
% 1.50/1.00  --clausifier_options                    --mode clausify
% 1.50/1.00  --stdin                                 false
% 1.50/1.00  --stats_out                             all
% 1.50/1.00  
% 1.50/1.00  ------ General Options
% 1.50/1.00  
% 1.50/1.00  --fof                                   false
% 1.50/1.00  --time_out_real                         305.
% 1.50/1.00  --time_out_virtual                      -1.
% 1.50/1.00  --symbol_type_check                     false
% 1.50/1.00  --clausify_out                          false
% 1.50/1.00  --sig_cnt_out                           false
% 1.50/1.00  --trig_cnt_out                          false
% 1.50/1.00  --trig_cnt_out_tolerance                1.
% 1.50/1.00  --trig_cnt_out_sk_spl                   false
% 1.50/1.00  --abstr_cl_out                          false
% 1.50/1.00  
% 1.50/1.00  ------ Global Options
% 1.50/1.00  
% 1.50/1.00  --schedule                              default
% 1.50/1.00  --add_important_lit                     false
% 1.50/1.00  --prop_solver_per_cl                    1000
% 1.50/1.00  --min_unsat_core                        false
% 1.50/1.00  --soft_assumptions                      false
% 1.50/1.00  --soft_lemma_size                       3
% 1.50/1.00  --prop_impl_unit_size                   0
% 1.50/1.00  --prop_impl_unit                        []
% 1.50/1.00  --share_sel_clauses                     true
% 1.50/1.00  --reset_solvers                         false
% 1.50/1.00  --bc_imp_inh                            [conj_cone]
% 1.50/1.00  --conj_cone_tolerance                   3.
% 1.50/1.00  --extra_neg_conj                        none
% 1.50/1.00  --large_theory_mode                     true
% 1.50/1.00  --prolific_symb_bound                   200
% 1.50/1.00  --lt_threshold                          2000
% 1.50/1.00  --clause_weak_htbl                      true
% 1.50/1.00  --gc_record_bc_elim                     false
% 1.50/1.00  
% 1.50/1.00  ------ Preprocessing Options
% 1.50/1.00  
% 1.50/1.00  --preprocessing_flag                    true
% 1.50/1.00  --time_out_prep_mult                    0.1
% 1.50/1.00  --splitting_mode                        input
% 1.50/1.00  --splitting_grd                         true
% 1.50/1.00  --splitting_cvd                         false
% 1.50/1.00  --splitting_cvd_svl                     false
% 1.50/1.00  --splitting_nvd                         32
% 1.50/1.00  --sub_typing                            true
% 1.50/1.00  --prep_gs_sim                           true
% 1.50/1.00  --prep_unflatten                        true
% 1.50/1.00  --prep_res_sim                          true
% 1.50/1.00  --prep_upred                            true
% 1.50/1.00  --prep_sem_filter                       exhaustive
% 1.50/1.00  --prep_sem_filter_out                   false
% 1.50/1.00  --pred_elim                             true
% 1.50/1.00  --res_sim_input                         true
% 1.50/1.00  --eq_ax_congr_red                       true
% 1.50/1.00  --pure_diseq_elim                       true
% 1.50/1.00  --brand_transform                       false
% 1.50/1.00  --non_eq_to_eq                          false
% 1.50/1.00  --prep_def_merge                        true
% 1.50/1.00  --prep_def_merge_prop_impl              false
% 1.50/1.00  --prep_def_merge_mbd                    true
% 1.50/1.00  --prep_def_merge_tr_red                 false
% 1.50/1.00  --prep_def_merge_tr_cl                  false
% 1.50/1.00  --smt_preprocessing                     true
% 1.50/1.00  --smt_ac_axioms                         fast
% 1.50/1.00  --preprocessed_out                      false
% 1.50/1.00  --preprocessed_stats                    false
% 1.50/1.00  
% 1.50/1.00  ------ Abstraction refinement Options
% 1.50/1.00  
% 1.50/1.00  --abstr_ref                             []
% 1.50/1.00  --abstr_ref_prep                        false
% 1.50/1.00  --abstr_ref_until_sat                   false
% 1.50/1.00  --abstr_ref_sig_restrict                funpre
% 1.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/1.00  --abstr_ref_under                       []
% 1.50/1.00  
% 1.50/1.00  ------ SAT Options
% 1.50/1.00  
% 1.50/1.00  --sat_mode                              false
% 1.50/1.00  --sat_fm_restart_options                ""
% 1.50/1.00  --sat_gr_def                            false
% 1.50/1.00  --sat_epr_types                         true
% 1.50/1.00  --sat_non_cyclic_types                  false
% 1.50/1.00  --sat_finite_models                     false
% 1.50/1.00  --sat_fm_lemmas                         false
% 1.50/1.00  --sat_fm_prep                           false
% 1.50/1.00  --sat_fm_uc_incr                        true
% 1.50/1.00  --sat_out_model                         small
% 1.50/1.00  --sat_out_clauses                       false
% 1.50/1.00  
% 1.50/1.00  ------ QBF Options
% 1.50/1.00  
% 1.50/1.00  --qbf_mode                              false
% 1.50/1.00  --qbf_elim_univ                         false
% 1.50/1.00  --qbf_dom_inst                          none
% 1.50/1.00  --qbf_dom_pre_inst                      false
% 1.50/1.00  --qbf_sk_in                             false
% 1.50/1.00  --qbf_pred_elim                         true
% 1.50/1.00  --qbf_split                             512
% 1.50/1.00  
% 1.50/1.00  ------ BMC1 Options
% 1.50/1.00  
% 1.50/1.00  --bmc1_incremental                      false
% 1.50/1.00  --bmc1_axioms                           reachable_all
% 1.50/1.00  --bmc1_min_bound                        0
% 1.50/1.00  --bmc1_max_bound                        -1
% 1.50/1.00  --bmc1_max_bound_default                -1
% 1.50/1.00  --bmc1_symbol_reachability              true
% 1.50/1.00  --bmc1_property_lemmas                  false
% 1.50/1.00  --bmc1_k_induction                      false
% 1.50/1.00  --bmc1_non_equiv_states                 false
% 1.50/1.00  --bmc1_deadlock                         false
% 1.50/1.00  --bmc1_ucm                              false
% 1.50/1.00  --bmc1_add_unsat_core                   none
% 1.50/1.00  --bmc1_unsat_core_children              false
% 1.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/1.00  --bmc1_out_stat                         full
% 1.50/1.00  --bmc1_ground_init                      false
% 1.50/1.00  --bmc1_pre_inst_next_state              false
% 1.50/1.00  --bmc1_pre_inst_state                   false
% 1.50/1.00  --bmc1_pre_inst_reach_state             false
% 1.50/1.00  --bmc1_out_unsat_core                   false
% 1.50/1.00  --bmc1_aig_witness_out                  false
% 1.50/1.00  --bmc1_verbose                          false
% 1.50/1.00  --bmc1_dump_clauses_tptp                false
% 1.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.50/1.00  --bmc1_dump_file                        -
% 1.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.50/1.00  --bmc1_ucm_extend_mode                  1
% 1.50/1.00  --bmc1_ucm_init_mode                    2
% 1.50/1.00  --bmc1_ucm_cone_mode                    none
% 1.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.50/1.00  --bmc1_ucm_relax_model                  4
% 1.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/1.00  --bmc1_ucm_layered_model                none
% 1.50/1.00  --bmc1_ucm_max_lemma_size               10
% 1.50/1.00  
% 1.50/1.00  ------ AIG Options
% 1.50/1.00  
% 1.50/1.00  --aig_mode                              false
% 1.50/1.00  
% 1.50/1.00  ------ Instantiation Options
% 1.50/1.00  
% 1.50/1.00  --instantiation_flag                    true
% 1.50/1.00  --inst_sos_flag                         false
% 1.50/1.00  --inst_sos_phase                        true
% 1.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/1.00  --inst_lit_sel_side                     none
% 1.50/1.00  --inst_solver_per_active                1400
% 1.50/1.00  --inst_solver_calls_frac                1.
% 1.50/1.00  --inst_passive_queue_type               priority_queues
% 1.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/1.00  --inst_passive_queues_freq              [25;2]
% 1.50/1.00  --inst_dismatching                      true
% 1.50/1.00  --inst_eager_unprocessed_to_passive     true
% 1.50/1.00  --inst_prop_sim_given                   true
% 1.50/1.00  --inst_prop_sim_new                     false
% 1.50/1.00  --inst_subs_new                         false
% 1.50/1.00  --inst_eq_res_simp                      false
% 1.50/1.00  --inst_subs_given                       false
% 1.50/1.00  --inst_orphan_elimination               true
% 1.50/1.00  --inst_learning_loop_flag               true
% 1.50/1.00  --inst_learning_start                   3000
% 1.50/1.00  --inst_learning_factor                  2
% 1.50/1.00  --inst_start_prop_sim_after_learn       3
% 1.50/1.00  --inst_sel_renew                        solver
% 1.50/1.00  --inst_lit_activity_flag                true
% 1.50/1.00  --inst_restr_to_given                   false
% 1.50/1.00  --inst_activity_threshold               500
% 1.50/1.00  --inst_out_proof                        true
% 1.50/1.00  
% 1.50/1.00  ------ Resolution Options
% 1.50/1.00  
% 1.50/1.00  --resolution_flag                       false
% 1.50/1.00  --res_lit_sel                           adaptive
% 1.50/1.00  --res_lit_sel_side                      none
% 1.50/1.00  --res_ordering                          kbo
% 1.50/1.00  --res_to_prop_solver                    active
% 1.50/1.00  --res_prop_simpl_new                    false
% 1.50/1.00  --res_prop_simpl_given                  true
% 1.50/1.00  --res_passive_queue_type                priority_queues
% 1.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/1.00  --res_passive_queues_freq               [15;5]
% 1.50/1.00  --res_forward_subs                      full
% 1.50/1.00  --res_backward_subs                     full
% 1.50/1.00  --res_forward_subs_resolution           true
% 1.50/1.00  --res_backward_subs_resolution          true
% 1.50/1.00  --res_orphan_elimination                true
% 1.50/1.00  --res_time_limit                        2.
% 1.50/1.00  --res_out_proof                         true
% 1.50/1.00  
% 1.50/1.00  ------ Superposition Options
% 1.50/1.00  
% 1.50/1.00  --superposition_flag                    true
% 1.50/1.00  --sup_passive_queue_type                priority_queues
% 1.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.50/1.00  --demod_completeness_check              fast
% 1.50/1.00  --demod_use_ground                      true
% 1.50/1.00  --sup_to_prop_solver                    passive
% 1.50/1.00  --sup_prop_simpl_new                    true
% 1.50/1.00  --sup_prop_simpl_given                  true
% 1.50/1.00  --sup_fun_splitting                     false
% 1.50/1.00  --sup_smt_interval                      50000
% 1.50/1.00  
% 1.50/1.00  ------ Superposition Simplification Setup
% 1.50/1.00  
% 1.50/1.00  --sup_indices_passive                   []
% 1.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.00  --sup_full_bw                           [BwDemod]
% 1.50/1.00  --sup_immed_triv                        [TrivRules]
% 1.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.00  --sup_immed_bw_main                     []
% 1.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.00  
% 1.50/1.00  ------ Combination Options
% 1.50/1.00  
% 1.50/1.00  --comb_res_mult                         3
% 1.50/1.00  --comb_sup_mult                         2
% 1.50/1.00  --comb_inst_mult                        10
% 1.50/1.00  
% 1.50/1.00  ------ Debug Options
% 1.50/1.00  
% 1.50/1.00  --dbg_backtrace                         false
% 1.50/1.00  --dbg_dump_prop_clauses                 false
% 1.50/1.00  --dbg_dump_prop_clauses_file            -
% 1.50/1.00  --dbg_out_stat                          false
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  ------ Proving...
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  % SZS status Theorem for theBenchmark.p
% 1.50/1.00  
% 1.50/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.50/1.00  
% 1.50/1.00  fof(f1,axiom,(
% 1.50/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f19,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/1.00    inference(nnf_transformation,[],[f1])).
% 1.50/1.00  
% 1.50/1.00  fof(f20,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/1.00    inference(flattening,[],[f19])).
% 1.50/1.00  
% 1.50/1.00  fof(f21,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/1.00    inference(rectify,[],[f20])).
% 1.50/1.00  
% 1.50/1.00  fof(f22,plain,(
% 1.50/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.50/1.00    introduced(choice_axiom,[])).
% 1.50/1.00  
% 1.50/1.00  fof(f23,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.50/1.00  
% 1.50/1.00  fof(f43,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/1.00    inference(cnf_transformation,[],[f23])).
% 1.50/1.00  
% 1.50/1.00  fof(f95,plain,(
% 1.50/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.50/1.00    inference(equality_resolution,[],[f43])).
% 1.50/1.00  
% 1.50/1.00  fof(f12,conjecture,(
% 1.50/1.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f13,negated_conjecture,(
% 1.50/1.00    ~! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.50/1.00    inference(negated_conjecture,[],[f12])).
% 1.50/1.00  
% 1.50/1.00  fof(f15,plain,(
% 1.50/1.00    ? [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <~> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.50/1.00    inference(ennf_transformation,[],[f13])).
% 1.50/1.00  
% 1.50/1.00  fof(f37,plain,(
% 1.50/1.00    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.50/1.00    inference(nnf_transformation,[],[f15])).
% 1.50/1.00  
% 1.50/1.00  fof(f38,plain,(
% 1.50/1.00    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.50/1.00    inference(flattening,[],[f37])).
% 1.50/1.00  
% 1.50/1.00  fof(f39,plain,(
% 1.50/1.00    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) => (((sK5 != sK6 & ~r2_hidden(sK5,sK6)) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (sK5 = sK6 | r2_hidden(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))))),
% 1.50/1.00    introduced(choice_axiom,[])).
% 1.50/1.00  
% 1.50/1.00  fof(f40,plain,(
% 1.50/1.00    ((sK5 != sK6 & ~r2_hidden(sK5,sK6)) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (sK5 = sK6 | r2_hidden(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6)))),
% 1.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).
% 1.50/1.00  
% 1.50/1.00  fof(f76,plain,(
% 1.50/1.00    sK5 = sK6 | r2_hidden(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 1.50/1.00    inference(cnf_transformation,[],[f40])).
% 1.50/1.00  
% 1.50/1.00  fof(f11,axiom,(
% 1.50/1.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f75,plain,(
% 1.50/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f11])).
% 1.50/1.00  
% 1.50/1.00  fof(f3,axiom,(
% 1.50/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f53,plain,(
% 1.50/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f3])).
% 1.50/1.00  
% 1.50/1.00  fof(f4,axiom,(
% 1.50/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f54,plain,(
% 1.50/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f4])).
% 1.50/1.00  
% 1.50/1.00  fof(f5,axiom,(
% 1.50/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f55,plain,(
% 1.50/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f5])).
% 1.50/1.00  
% 1.50/1.00  fof(f6,axiom,(
% 1.50/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f56,plain,(
% 1.50/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f6])).
% 1.50/1.00  
% 1.50/1.00  fof(f7,axiom,(
% 1.50/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f57,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f7])).
% 1.50/1.00  
% 1.50/1.00  fof(f8,axiom,(
% 1.50/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f58,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f8])).
% 1.50/1.00  
% 1.50/1.00  fof(f9,axiom,(
% 1.50/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f59,plain,(
% 1.50/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f9])).
% 1.50/1.00  
% 1.50/1.00  fof(f79,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f58,f59])).
% 1.50/1.00  
% 1.50/1.00  fof(f80,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f57,f79])).
% 1.50/1.00  
% 1.50/1.00  fof(f81,plain,(
% 1.50/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f56,f80])).
% 1.50/1.00  
% 1.50/1.00  fof(f82,plain,(
% 1.50/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f55,f81])).
% 1.50/1.00  
% 1.50/1.00  fof(f83,plain,(
% 1.50/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f54,f82])).
% 1.50/1.00  
% 1.50/1.00  fof(f84,plain,(
% 1.50/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f53,f83])).
% 1.50/1.00  
% 1.50/1.00  fof(f85,plain,(
% 1.50/1.00    ( ! [X0] : (k2_xboole_0(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k1_ordinal1(X0)) )),
% 1.50/1.00    inference(definition_unfolding,[],[f75,f84])).
% 1.50/1.00  
% 1.50/1.00  fof(f94,plain,(
% 1.50/1.00    sK5 = sK6 | r2_hidden(sK5,sK6) | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))),
% 1.50/1.00    inference(definition_unfolding,[],[f76,f85])).
% 1.50/1.00  
% 1.50/1.00  fof(f42,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/1.00    inference(cnf_transformation,[],[f23])).
% 1.50/1.00  
% 1.50/1.00  fof(f96,plain,(
% 1.50/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.50/1.00    inference(equality_resolution,[],[f42])).
% 1.50/1.00  
% 1.50/1.00  fof(f78,plain,(
% 1.50/1.00    sK5 != sK6 | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 1.50/1.00    inference(cnf_transformation,[],[f40])).
% 1.50/1.00  
% 1.50/1.00  fof(f92,plain,(
% 1.50/1.00    sK5 != sK6 | ~r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))),
% 1.50/1.00    inference(definition_unfolding,[],[f78,f85])).
% 1.50/1.00  
% 1.50/1.00  fof(f77,plain,(
% 1.50/1.00    ~r2_hidden(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 1.50/1.00    inference(cnf_transformation,[],[f40])).
% 1.50/1.00  
% 1.50/1.00  fof(f93,plain,(
% 1.50/1.00    ~r2_hidden(sK5,sK6) | ~r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))),
% 1.50/1.00    inference(definition_unfolding,[],[f77,f85])).
% 1.50/1.00  
% 1.50/1.00  fof(f41,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/1.00    inference(cnf_transformation,[],[f23])).
% 1.50/1.00  
% 1.50/1.00  fof(f97,plain,(
% 1.50/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 1.50/1.00    inference(equality_resolution,[],[f41])).
% 1.50/1.00  
% 1.50/1.00  fof(f2,axiom,(
% 1.50/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/1.00  
% 1.50/1.00  fof(f24,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/1.00    inference(nnf_transformation,[],[f2])).
% 1.50/1.00  
% 1.50/1.00  fof(f25,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/1.00    inference(flattening,[],[f24])).
% 1.50/1.00  
% 1.50/1.00  fof(f26,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/1.00    inference(rectify,[],[f25])).
% 1.50/1.00  
% 1.50/1.00  fof(f27,plain,(
% 1.50/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.50/1.00    introduced(choice_axiom,[])).
% 1.50/1.00  
% 1.50/1.00  fof(f28,plain,(
% 1.50/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.50/1.00  
% 1.50/1.00  fof(f47,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.50/1.00    inference(cnf_transformation,[],[f28])).
% 1.50/1.00  
% 1.50/1.00  fof(f91,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.50/1.00    inference(definition_unfolding,[],[f47,f83])).
% 1.50/1.00  
% 1.50/1.00  fof(f102,plain,(
% 1.50/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.50/1.00    inference(equality_resolution,[],[f91])).
% 1.50/1.00  
% 1.50/1.00  fof(f48,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.50/1.00    inference(cnf_transformation,[],[f28])).
% 1.50/1.00  
% 1.50/1.00  fof(f90,plain,(
% 1.50/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.50/1.00    inference(definition_unfolding,[],[f48,f83])).
% 1.50/1.00  
% 1.50/1.00  fof(f100,plain,(
% 1.50/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 1.50/1.00    inference(equality_resolution,[],[f90])).
% 1.50/1.00  
% 1.50/1.00  fof(f101,plain,(
% 1.50/1.00    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 1.50/1.00    inference(equality_resolution,[],[f100])).
% 1.50/1.00  
% 1.50/1.00  fof(f16,plain,(
% 1.50/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.50/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.50/1.00  
% 1.50/1.00  fof(f33,plain,(
% 1.50/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.50/1.00    inference(nnf_transformation,[],[f16])).
% 1.50/1.00  
% 1.50/1.00  fof(f34,plain,(
% 1.50/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.50/1.00    inference(flattening,[],[f33])).
% 1.50/1.00  
% 1.50/1.00  fof(f35,plain,(
% 1.50/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.50/1.00    inference(rectify,[],[f34])).
% 1.50/1.00  
% 1.50/1.00  fof(f65,plain,(
% 1.50/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 1.50/1.00    inference(cnf_transformation,[],[f35])).
% 1.50/1.00  
% 1.50/1.00  fof(f110,plain,(
% 1.50/1.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.50/1.00    inference(equality_resolution,[],[f65])).
% 1.50/1.00  
% 1.50/1.00  fof(f64,plain,(
% 1.50/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.50/1.00    inference(cnf_transformation,[],[f35])).
% 1.50/1.00  
% 1.50/1.00  cnf(c_856,plain,
% 1.50/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.50/1.00      theory(equality) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1595,plain,
% 1.50/1.00      ( r2_hidden(X0,X1)
% 1.50/1.00      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
% 1.50/1.00      | X0 != X2
% 1.50/1.00      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2) ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_856]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_2086,plain,
% 1.50/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 1.50/1.00      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)
% 1.50/1.00      | sK5 != X0 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_2088,plain,
% 1.50/1.00      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 1.50/1.00      | sK5 != sK6 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_2086]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_853,plain,( X0 = X0 ),theory(equality) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1754,plain,
% 1.50/1.00      ( sK5 = sK5 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_853]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_854,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1581,plain,
% 1.50/1.00      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_854]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1753,plain,
% 1.50/1.00      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_1581]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_3,plain,
% 1.50/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 1.50/1.00      inference(cnf_transformation,[],[f95]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1689,plain,
% 1.50/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | r2_hidden(sK5,k2_xboole_0(X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1691,plain,
% 1.50/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_1689]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_29,negated_conjecture,
% 1.50/1.00      ( r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
% 1.50/1.00      | r2_hidden(sK5,sK6)
% 1.50/1.00      | sK5 = sK6 ),
% 1.50/1.00      inference(cnf_transformation,[],[f94]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1336,plain,
% 1.50/1.00      ( sK5 = sK6
% 1.50/1.00      | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = iProver_top
% 1.50/1.00      | r2_hidden(sK5,sK6) = iProver_top ),
% 1.50/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_4,plain,
% 1.50/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 1.50/1.00      inference(cnf_transformation,[],[f96]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1361,plain,
% 1.50/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.50/1.00      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 1.50/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1419,plain,
% 1.50/1.00      ( sK6 = sK5
% 1.50/1.00      | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = iProver_top ),
% 1.50/1.00      inference(forward_subsumption_resolution,
% 1.50/1.00                [status(thm)],
% 1.50/1.00                [c_1336,c_1361]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_27,negated_conjecture,
% 1.50/1.00      ( ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
% 1.50/1.00      | sK5 != sK6 ),
% 1.50/1.00      inference(cnf_transformation,[],[f92]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_32,plain,
% 1.50/1.00      ( sK5 != sK6
% 1.50/1.00      | r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) != iProver_top ),
% 1.50/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_28,negated_conjecture,
% 1.50/1.00      ( ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
% 1.50/1.00      | ~ r2_hidden(sK5,sK6) ),
% 1.50/1.00      inference(cnf_transformation,[],[f93]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1337,plain,
% 1.50/1.00      ( r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))) != iProver_top
% 1.50/1.00      | r2_hidden(sK5,sK6) != iProver_top ),
% 1.50/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1414,plain,
% 1.50/1.00      ( r2_hidden(sK5,sK6) != iProver_top ),
% 1.50/1.00      inference(forward_subsumption_resolution,
% 1.50/1.00                [status(thm)],
% 1.50/1.00                [c_1337,c_1361]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1512,plain,
% 1.50/1.00      ( ~ r2_hidden(sK5,sK6) ),
% 1.50/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1414]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1527,plain,
% 1.50/1.00      ( r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
% 1.50/1.00      | sK6 = sK5 ),
% 1.50/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1419]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_5,plain,
% 1.50/1.00      ( r2_hidden(X0,X1)
% 1.50/1.00      | r2_hidden(X0,X2)
% 1.50/1.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 1.50/1.00      inference(cnf_transformation,[],[f97]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1582,plain,
% 1.50/1.00      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | ~ r2_hidden(sK5,k2_xboole_0(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))
% 1.50/1.00      | r2_hidden(sK5,sK6) ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_11,plain,
% 1.50/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 1.50/1.00      | X0 = X1
% 1.50/1.00      | X0 = X2 ),
% 1.50/1.00      inference(cnf_transformation,[],[f102]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1619,plain,
% 1.50/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
% 1.50/1.00      | sK5 = X0
% 1.50/1.00      | sK5 = sK6 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1621,plain,
% 1.50/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 1.50/1.00      | sK5 = sK6 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_1619]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_1625,plain,
% 1.50/1.00      ( sK6 = sK5 ),
% 1.50/1.00      inference(global_propositional_subsumption,
% 1.50/1.00                [status(thm)],
% 1.50/1.00                [c_1419,c_32,c_1512,c_1527,c_1582,c_1621]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_857,plain,
% 1.50/1.00      ( X0 != X1
% 1.50/1.00      | X2 != X3
% 1.50/1.00      | X4 != X5
% 1.50/1.00      | X6 != X7
% 1.50/1.00      | X8 != X9
% 1.50/1.00      | X10 != X11
% 1.50/1.00      | X12 != X13
% 1.50/1.00      | X14 != X15
% 1.50/1.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 1.50/1.00      theory(equality) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_862,plain,
% 1.50/1.00      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 1.50/1.00      | sK6 != sK6 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_857]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_10,plain,
% 1.50/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 1.50/1.00      inference(cnf_transformation,[],[f101]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_66,plain,
% 1.50/1.00      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_23,plain,
% 1.50/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 1.50/1.00      inference(cnf_transformation,[],[f110]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_43,plain,
% 1.50/1.00      ( sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_24,plain,
% 1.50/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 1.50/1.00      | X4 = X0
% 1.50/1.00      | X8 = X0
% 1.50/1.00      | X7 = X0
% 1.50/1.00      | X6 = X0
% 1.50/1.00      | X5 = X0
% 1.50/1.00      | X3 = X0
% 1.50/1.00      | X2 = X0
% 1.50/1.00      | X1 = X0 ),
% 1.50/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(c_40,plain,
% 1.50/1.00      ( ~ sP0(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) | sK6 = sK6 ),
% 1.50/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 1.50/1.00  
% 1.50/1.00  cnf(contradiction,plain,
% 1.50/1.00      ( $false ),
% 1.50/1.00      inference(minisat,
% 1.50/1.00                [status(thm)],
% 1.50/1.00                [c_2088,c_1754,c_1753,c_1691,c_1625,c_862,c_66,c_43,c_40,
% 1.50/1.00                 c_27]) ).
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.50/1.00  
% 1.50/1.00  ------                               Statistics
% 1.50/1.00  
% 1.50/1.00  ------ General
% 1.50/1.00  
% 1.50/1.00  abstr_ref_over_cycles:                  0
% 1.50/1.00  abstr_ref_under_cycles:                 0
% 1.50/1.00  gc_basic_clause_elim:                   0
% 1.50/1.00  forced_gc_time:                         0
% 1.50/1.00  parsing_time:                           0.014
% 1.50/1.00  unif_index_cands_time:                  0.
% 1.50/1.00  unif_index_add_time:                    0.
% 1.50/1.00  orderings_time:                         0.
% 1.50/1.00  out_proof_time:                         0.017
% 1.50/1.00  total_time:                             0.106
% 1.50/1.00  num_of_symbols:                         41
% 1.50/1.00  num_of_terms:                           1675
% 1.50/1.00  
% 1.50/1.00  ------ Preprocessing
% 1.50/1.00  
% 1.50/1.00  num_of_splits:                          0
% 1.50/1.00  num_of_split_atoms:                     0
% 1.50/1.00  num_of_reused_defs:                     0
% 1.50/1.00  num_eq_ax_congr_red:                    62
% 1.50/1.00  num_of_sem_filtered_clauses:            1
% 1.50/1.00  num_of_subtypes:                        0
% 1.50/1.00  monotx_restored_types:                  0
% 1.50/1.00  sat_num_of_epr_types:                   0
% 1.50/1.00  sat_num_of_non_cyclic_types:            0
% 1.50/1.00  sat_guarded_non_collapsed_types:        0
% 1.50/1.00  num_pure_diseq_elim:                    0
% 1.50/1.00  simp_replaced_by:                       0
% 1.50/1.00  res_preprocessed:                       105
% 1.50/1.00  prep_upred:                             0
% 1.50/1.00  prep_unflattend:                        298
% 1.50/1.00  smt_new_axioms:                         0
% 1.50/1.00  pred_elim_cands:                        3
% 1.50/1.00  pred_elim:                              0
% 1.50/1.00  pred_elim_cl:                           0
% 1.50/1.00  pred_elim_cycles:                       2
% 1.50/1.00  merged_defs:                            0
% 1.50/1.00  merged_defs_ncl:                        0
% 1.50/1.00  bin_hyper_res:                          0
% 1.50/1.00  prep_cycles:                            3
% 1.50/1.00  pred_elim_time:                         0.012
% 1.50/1.00  splitting_time:                         0.
% 1.50/1.00  sem_filter_time:                        0.
% 1.50/1.00  monotx_time:                            0.001
% 1.50/1.00  subtype_inf_time:                       0.
% 1.50/1.00  
% 1.50/1.00  ------ Problem properties
% 1.50/1.00  
% 1.50/1.00  clauses:                                30
% 1.50/1.00  conjectures:                            3
% 1.50/1.00  epr:                                    11
% 1.50/1.00  horn:                                   23
% 1.50/1.00  ground:                                 3
% 1.50/1.00  unary:                                  11
% 1.50/1.00  binary:                                 5
% 1.50/1.00  lits:                                   71
% 1.50/1.00  lits_eq:                                23
% 1.50/1.00  fd_pure:                                0
% 1.50/1.00  fd_pseudo:                              0
% 1.50/1.00  fd_cond:                                0
% 1.50/1.00  fd_pseudo_cond:                         8
% 1.50/1.00  ac_symbols:                             0
% 1.50/1.00  
% 1.50/1.00  ------ Propositional Solver
% 1.50/1.00  
% 1.50/1.00  prop_solver_calls:                      20
% 1.50/1.00  prop_fast_solver_calls:                 647
% 1.50/1.00  smt_solver_calls:                       0
% 1.50/1.00  smt_fast_solver_calls:                  0
% 1.50/1.00  prop_num_of_clauses:                    503
% 1.50/1.00  prop_preprocess_simplified:             3636
% 1.50/1.00  prop_fo_subsumed:                       1
% 1.50/1.00  prop_solver_time:                       0.
% 1.50/1.00  smt_solver_time:                        0.
% 1.50/1.00  smt_fast_solver_time:                   0.
% 1.50/1.00  prop_fast_solver_time:                  0.
% 1.50/1.00  prop_unsat_core_time:                   0.
% 1.50/1.00  
% 1.50/1.00  ------ QBF
% 1.50/1.00  
% 1.50/1.00  qbf_q_res:                              0
% 1.50/1.00  qbf_num_tautologies:                    0
% 1.50/1.00  qbf_prep_cycles:                        0
% 1.50/1.00  
% 1.50/1.00  ------ BMC1
% 1.50/1.00  
% 1.50/1.00  bmc1_current_bound:                     -1
% 1.50/1.00  bmc1_last_solved_bound:                 -1
% 1.50/1.00  bmc1_unsat_core_size:                   -1
% 1.50/1.00  bmc1_unsat_core_parents_size:           -1
% 1.50/1.00  bmc1_merge_next_fun:                    0
% 1.50/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.50/1.00  
% 1.50/1.00  ------ Instantiation
% 1.50/1.00  
% 1.50/1.00  inst_num_of_clauses:                    130
% 1.50/1.00  inst_num_in_passive:                    9
% 1.50/1.00  inst_num_in_active:                     66
% 1.50/1.00  inst_num_in_unprocessed:                54
% 1.50/1.00  inst_num_of_loops:                      79
% 1.50/1.00  inst_num_of_learning_restarts:          0
% 1.50/1.00  inst_num_moves_active_passive:          11
% 1.50/1.00  inst_lit_activity:                      0
% 1.50/1.00  inst_lit_activity_moves:                0
% 1.50/1.00  inst_num_tautologies:                   0
% 1.50/1.00  inst_num_prop_implied:                  0
% 1.50/1.00  inst_num_existing_simplified:           0
% 1.50/1.00  inst_num_eq_res_simplified:             0
% 1.50/1.00  inst_num_child_elim:                    0
% 1.50/1.00  inst_num_of_dismatching_blockings:      3
% 1.50/1.00  inst_num_of_non_proper_insts:           85
% 1.50/1.00  inst_num_of_duplicates:                 0
% 1.50/1.00  inst_inst_num_from_inst_to_res:         0
% 1.50/1.00  inst_dismatching_checking_time:         0.
% 1.50/1.00  
% 1.50/1.00  ------ Resolution
% 1.50/1.00  
% 1.50/1.00  res_num_of_clauses:                     0
% 1.50/1.00  res_num_in_passive:                     0
% 1.50/1.00  res_num_in_active:                      0
% 1.50/1.00  res_num_of_loops:                       108
% 1.50/1.00  res_forward_subset_subsumed:            6
% 1.50/1.00  res_backward_subset_subsumed:           0
% 1.50/1.00  res_forward_subsumed:                   0
% 1.50/1.00  res_backward_subsumed:                  0
% 1.50/1.00  res_forward_subsumption_resolution:     0
% 1.50/1.00  res_backward_subsumption_resolution:    0
% 1.50/1.00  res_clause_to_clause_subsumption:       460
% 1.50/1.00  res_orphan_elimination:                 0
% 1.50/1.00  res_tautology_del:                      16
% 1.50/1.00  res_num_eq_res_simplified:              0
% 1.50/1.00  res_num_sel_changes:                    0
% 1.50/1.00  res_moves_from_active_to_pass:          0
% 1.50/1.00  
% 1.50/1.00  ------ Superposition
% 1.50/1.00  
% 1.50/1.00  sup_time_total:                         0.
% 1.50/1.00  sup_time_generating:                    0.
% 1.50/1.00  sup_time_sim_full:                      0.
% 1.50/1.00  sup_time_sim_immed:                     0.
% 1.50/1.00  
% 1.50/1.00  sup_num_of_clauses:                     30
% 1.50/1.00  sup_num_in_active:                      12
% 1.50/1.00  sup_num_in_passive:                     18
% 1.50/1.00  sup_num_of_loops:                       14
% 1.50/1.00  sup_fw_superposition:                   0
% 1.50/1.00  sup_bw_superposition:                   0
% 1.50/1.00  sup_immediate_simplified:               0
% 1.50/1.00  sup_given_eliminated:                   0
% 1.50/1.00  comparisons_done:                       0
% 1.50/1.00  comparisons_avoided:                    0
% 1.50/1.00  
% 1.50/1.00  ------ Simplifications
% 1.50/1.00  
% 1.50/1.00  
% 1.50/1.00  sim_fw_subset_subsumed:                 0
% 1.50/1.00  sim_bw_subset_subsumed:                 0
% 1.50/1.00  sim_fw_subsumed:                        0
% 1.50/1.00  sim_bw_subsumed:                        0
% 1.50/1.00  sim_fw_subsumption_res:                 2
% 1.50/1.00  sim_bw_subsumption_res:                 0
% 1.50/1.00  sim_tautology_del:                      0
% 1.50/1.00  sim_eq_tautology_del:                   0
% 1.50/1.00  sim_eq_res_simp:                        1
% 1.50/1.00  sim_fw_demodulated:                     0
% 1.50/1.00  sim_bw_demodulated:                     2
% 1.50/1.00  sim_light_normalised:                   0
% 1.50/1.00  sim_joinable_taut:                      0
% 1.50/1.00  sim_joinable_simp:                      0
% 1.50/1.00  sim_ac_normalised:                      0
% 1.50/1.00  sim_smt_subsumption:                    0
% 1.50/1.00  
%------------------------------------------------------------------------------
