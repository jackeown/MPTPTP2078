%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:02 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 166 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 ( 442 expanded)
%              Number of equality atoms :  229 ( 386 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f96,f97])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f95,f101])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f94,f102])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f93,f103])).

fof(f114,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f104])).

fof(f128,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f114])).

fof(f129,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f128])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f92,f104])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f91,f105])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f98,f106,f106])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f46,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f47])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X9 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f144,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f77])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | X0 = X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,conjecture,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k1_tarski(X0) ),
    inference(ennf_transformation,[],[f24])).

fof(f50,plain,
    ( ? [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k1_tarski(X0)
   => k3_xboole_0(k1_tarski(sK5),k2_tarski(sK5,sK6)) != k1_tarski(sK5) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    k3_xboole_0(k1_tarski(sK5),k2_tarski(sK5,sK6)) != k1_tarski(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f29,f50])).

fof(f99,plain,(
    k3_xboole_0(k1_tarski(sK5),k2_tarski(sK5,sK6)) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f125,plain,(
    k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f99,f106,f105,f106])).

cnf(c_12,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_8944,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_36,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3888,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2053,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2985,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_2053])).

cnf(c_3887,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2985])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2822,plain,
    ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2760,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != X0
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2053])).

cnf(c_2821,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_2054,plain,
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

cnf(c_2060,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_31,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_52,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | X5 = X0
    | X3 = X0
    | X9 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X4 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_49,plain,
    ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_37,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8944,c_3888,c_3887,c_2822,c_2821,c_2060,c_52,c_49,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.58/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/1.00  
% 2.58/1.00  ------  iProver source info
% 2.58/1.00  
% 2.58/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.58/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/1.00  git: non_committed_changes: false
% 2.58/1.00  git: last_make_outside_of_git: false
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     num_symb
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       true
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  ------ Parsing...
% 2.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.00  ------ Proving...
% 2.58/1.00  ------ Problem Properties 
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  clauses                                 38
% 2.58/1.00  conjectures                             1
% 2.58/1.00  EPR                                     12
% 2.58/1.00  Horn                                    33
% 2.58/1.00  unary                                   23
% 2.58/1.00  binary                                  3
% 2.58/1.00  lits                                    75
% 2.58/1.00  lits eq                                 38
% 2.58/1.00  fd_pure                                 0
% 2.58/1.00  fd_pseudo                               0
% 2.58/1.00  fd_cond                                 0
% 2.58/1.00  fd_pseudo_cond                          8
% 2.58/1.00  AC symbols                              1
% 2.58/1.00  
% 2.58/1.00  ------ Schedule dynamic 5 is on 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  Current options:
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     none
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       false
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ Proving...
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS status Theorem for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  fof(f9,axiom,(
% 2.58/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f26,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.58/1.00    inference(ennf_transformation,[],[f9])).
% 2.58/1.00  
% 2.58/1.00  fof(f33,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(nnf_transformation,[],[f26])).
% 2.58/1.00  
% 2.58/1.00  fof(f34,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(flattening,[],[f33])).
% 2.58/1.00  
% 2.58/1.00  fof(f35,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(rectify,[],[f34])).
% 2.58/1.00  
% 2.58/1.00  fof(f36,plain,(
% 2.58/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f37,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.58/1.00  
% 2.58/1.00  fof(f62,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.58/1.00    inference(cnf_transformation,[],[f37])).
% 2.58/1.00  
% 2.58/1.00  fof(f17,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f93,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f17])).
% 2.58/1.00  
% 2.58/1.00  fof(f18,axiom,(
% 2.58/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f94,plain,(
% 2.58/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f18])).
% 2.58/1.00  
% 2.58/1.00  fof(f19,axiom,(
% 2.58/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f95,plain,(
% 2.58/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f19])).
% 2.58/1.00  
% 2.58/1.00  fof(f20,axiom,(
% 2.58/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f96,plain,(
% 2.58/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f20])).
% 2.58/1.00  
% 2.58/1.00  fof(f21,axiom,(
% 2.58/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f97,plain,(
% 2.58/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f21])).
% 2.58/1.00  
% 2.58/1.00  fof(f101,plain,(
% 2.58/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f96,f97])).
% 2.58/1.00  
% 2.58/1.00  fof(f102,plain,(
% 2.58/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f95,f101])).
% 2.58/1.00  
% 2.58/1.00  fof(f103,plain,(
% 2.58/1.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f94,f102])).
% 2.58/1.00  
% 2.58/1.00  fof(f104,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f93,f103])).
% 2.58/1.00  
% 2.58/1.00  fof(f114,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.58/1.00    inference(definition_unfolding,[],[f62,f104])).
% 2.58/1.00  
% 2.58/1.00  fof(f128,plain,(
% 2.58/1.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 2.58/1.00    inference(equality_resolution,[],[f114])).
% 2.58/1.00  
% 2.58/1.00  fof(f129,plain,(
% 2.58/1.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 2.58/1.00    inference(equality_resolution,[],[f128])).
% 2.58/1.00  
% 2.58/1.00  fof(f22,axiom,(
% 2.58/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f28,plain,(
% 2.58/1.00    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 2.58/1.00    inference(ennf_transformation,[],[f22])).
% 2.58/1.00  
% 2.58/1.00  fof(f98,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f28])).
% 2.58/1.00  
% 2.58/1.00  fof(f15,axiom,(
% 2.58/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f91,plain,(
% 2.58/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f15])).
% 2.58/1.00  
% 2.58/1.00  fof(f16,axiom,(
% 2.58/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f92,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f16])).
% 2.58/1.00  
% 2.58/1.00  fof(f105,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f92,f104])).
% 2.58/1.00  
% 2.58/1.00  fof(f106,plain,(
% 2.58/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f91,f105])).
% 2.58/1.00  
% 2.58/1.00  fof(f124,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 2.58/1.00    inference(definition_unfolding,[],[f98,f106,f106])).
% 2.58/1.00  
% 2.58/1.00  fof(f1,axiom,(
% 2.58/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f52,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f1])).
% 2.58/1.00  
% 2.58/1.00  fof(f30,plain,(
% 2.58/1.00    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 2.58/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.58/1.00  
% 2.58/1.00  fof(f46,plain,(
% 2.58/1.00    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.58/1.00    inference(nnf_transformation,[],[f30])).
% 2.58/1.00  
% 2.58/1.00  fof(f47,plain,(
% 2.58/1.00    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.58/1.00    inference(flattening,[],[f46])).
% 2.58/1.00  
% 2.58/1.00  fof(f48,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.58/1.00    inference(rectify,[],[f47])).
% 2.58/1.00  
% 2.58/1.00  fof(f77,plain,(
% 2.58/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X9) )),
% 2.58/1.00    inference(cnf_transformation,[],[f48])).
% 2.58/1.00  
% 2.58/1.00  fof(f144,plain,(
% 2.58/1.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.58/1.00    inference(equality_resolution,[],[f77])).
% 2.58/1.00  
% 2.58/1.00  fof(f76,plain,(
% 2.58/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f48])).
% 2.58/1.00  
% 2.58/1.00  fof(f23,conjecture,(
% 2.58/1.00    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 2.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f24,negated_conjecture,(
% 2.58/1.00    ~! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 2.58/1.00    inference(negated_conjecture,[],[f23])).
% 2.58/1.00  
% 2.58/1.00  fof(f29,plain,(
% 2.58/1.00    ? [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k1_tarski(X0)),
% 2.58/1.00    inference(ennf_transformation,[],[f24])).
% 2.58/1.00  
% 2.58/1.00  fof(f50,plain,(
% 2.58/1.00    ? [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k1_tarski(X0) => k3_xboole_0(k1_tarski(sK5),k2_tarski(sK5,sK6)) != k1_tarski(sK5)),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f51,plain,(
% 2.58/1.00    k3_xboole_0(k1_tarski(sK5),k2_tarski(sK5,sK6)) != k1_tarski(sK5)),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f29,f50])).
% 2.58/1.00  
% 2.58/1.00  fof(f99,plain,(
% 2.58/1.00    k3_xboole_0(k1_tarski(sK5),k2_tarski(sK5,sK6)) != k1_tarski(sK5)),
% 2.58/1.00    inference(cnf_transformation,[],[f51])).
% 2.58/1.00  
% 2.58/1.00  fof(f125,plain,(
% 2.58/1.00    k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 2.58/1.00    inference(definition_unfolding,[],[f99,f106,f105,f106])).
% 2.58/1.00  
% 2.58/1.00  cnf(c_12,plain,
% 2.58/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 2.58/1.00      inference(cnf_transformation,[],[f129]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8944,plain,
% 2.58/1.00      ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_36,plain,
% 2.58/1.00      ( ~ r2_hidden(X0,X1)
% 2.58/1.00      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f124]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3888,plain,
% 2.58/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2053,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2985,plain,
% 2.58/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X0
% 2.58/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X0 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2053]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_3887,plain,
% 2.58/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.58/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2985]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_1,plain,
% 2.58/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2822,plain,
% 2.58/1.00      ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2760,plain,
% 2.58/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X0
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != X0
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2053]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2821,plain,
% 2.58/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.58/1.00      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2760]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2054,plain,
% 2.58/1.00      ( X0 != X1
% 2.58/1.00      | X2 != X3
% 2.58/1.00      | X4 != X5
% 2.58/1.00      | X6 != X7
% 2.58/1.00      | X8 != X9
% 2.58/1.00      | X10 != X11
% 2.58/1.00      | X12 != X13
% 2.58/1.00      | X14 != X15
% 2.58/1.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.58/1.00      theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_2060,plain,
% 2.58/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.58/1.00      | sK5 != sK5 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_2054]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_31,plain,
% 2.58/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f144]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_52,plain,
% 2.58/1.00      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_32,plain,
% 2.58/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 2.58/1.00      | X5 = X0
% 2.58/1.00      | X3 = X0
% 2.58/1.00      | X9 = X0
% 2.58/1.00      | X8 = X0
% 2.58/1.00      | X7 = X0
% 2.58/1.00      | X6 = X0
% 2.58/1.00      | X4 = X0
% 2.58/1.00      | X2 = X0
% 2.58/1.00      | X1 = X0 ),
% 2.58/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_49,plain,
% 2.58/1.00      ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) | sK5 = sK5 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_37,negated_conjecture,
% 2.58/1.00      ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.58/1.00      inference(cnf_transformation,[],[f125]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(contradiction,plain,
% 2.58/1.00      ( $false ),
% 2.58/1.00      inference(minisat,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_8944,c_3888,c_3887,c_2822,c_2821,c_2060,c_52,c_49,
% 2.58/1.00                 c_37]) ).
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  ------                               Statistics
% 2.58/1.00  
% 2.58/1.00  ------ General
% 2.58/1.00  
% 2.58/1.00  abstr_ref_over_cycles:                  0
% 2.58/1.00  abstr_ref_under_cycles:                 0
% 2.58/1.00  gc_basic_clause_elim:                   0
% 2.58/1.00  forced_gc_time:                         0
% 2.58/1.00  parsing_time:                           0.012
% 2.58/1.00  unif_index_cands_time:                  0.
% 2.58/1.00  unif_index_add_time:                    0.
% 2.58/1.00  orderings_time:                         0.
% 2.58/1.00  out_proof_time:                         0.007
% 2.58/1.00  total_time:                             0.288
% 2.58/1.00  num_of_symbols:                         43
% 2.58/1.00  num_of_terms:                           9182
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing
% 2.58/1.00  
% 2.58/1.00  num_of_splits:                          0
% 2.58/1.00  num_of_split_atoms:                     0
% 2.58/1.00  num_of_reused_defs:                     0
% 2.58/1.00  num_eq_ax_congr_red:                    68
% 2.58/1.00  num_of_sem_filtered_clauses:            1
% 2.58/1.00  num_of_subtypes:                        0
% 2.58/1.00  monotx_restored_types:                  0
% 2.58/1.00  sat_num_of_epr_types:                   0
% 2.58/1.00  sat_num_of_non_cyclic_types:            0
% 2.58/1.00  sat_guarded_non_collapsed_types:        0
% 2.58/1.00  num_pure_diseq_elim:                    0
% 2.58/1.00  simp_replaced_by:                       0
% 2.58/1.00  res_preprocessed:                       131
% 2.58/1.00  prep_upred:                             0
% 2.58/1.00  prep_unflattend:                        455
% 2.58/1.00  smt_new_axioms:                         0
% 2.58/1.00  pred_elim_cands:                        3
% 2.58/1.00  pred_elim:                              0
% 2.58/1.00  pred_elim_cl:                           0
% 2.58/1.00  pred_elim_cycles:                       3
% 2.58/1.00  merged_defs:                            0
% 2.58/1.00  merged_defs_ncl:                        0
% 2.58/1.00  bin_hyper_res:                          0
% 2.58/1.00  prep_cycles:                            3
% 2.58/1.00  pred_elim_time:                         0.036
% 2.58/1.00  splitting_time:                         0.
% 2.58/1.00  sem_filter_time:                        0.
% 2.58/1.00  monotx_time:                            0.001
% 2.58/1.00  subtype_inf_time:                       0.
% 2.58/1.00  
% 2.58/1.00  ------ Problem properties
% 2.58/1.00  
% 2.58/1.00  clauses:                                38
% 2.58/1.00  conjectures:                            1
% 2.58/1.00  epr:                                    12
% 2.58/1.00  horn:                                   33
% 2.58/1.00  ground:                                 1
% 2.58/1.00  unary:                                  23
% 2.58/1.00  binary:                                 3
% 2.58/1.00  lits:                                   75
% 2.58/1.00  lits_eq:                                38
% 2.58/1.00  fd_pure:                                0
% 2.58/1.00  fd_pseudo:                              0
% 2.58/1.00  fd_cond:                                0
% 2.58/1.00  fd_pseudo_cond:                         8
% 2.58/1.00  ac_symbols:                             1
% 2.58/1.00  
% 2.58/1.00  ------ Propositional Solver
% 2.58/1.00  
% 2.58/1.00  prop_solver_calls:                      22
% 2.58/1.00  prop_fast_solver_calls:                 958
% 2.58/1.00  smt_solver_calls:                       0
% 2.58/1.00  smt_fast_solver_calls:                  0
% 2.58/1.00  prop_num_of_clauses:                    1978
% 2.58/1.00  prop_preprocess_simplified:             5836
% 2.58/1.00  prop_fo_subsumed:                       0
% 2.58/1.00  prop_solver_time:                       0.
% 2.58/1.00  smt_solver_time:                        0.
% 2.58/1.00  smt_fast_solver_time:                   0.
% 2.58/1.00  prop_fast_solver_time:                  0.
% 2.58/1.00  prop_unsat_core_time:                   0.
% 2.58/1.00  
% 2.58/1.00  ------ QBF
% 2.58/1.00  
% 2.58/1.00  qbf_q_res:                              0
% 2.58/1.00  qbf_num_tautologies:                    0
% 2.58/1.00  qbf_prep_cycles:                        0
% 2.58/1.00  
% 2.58/1.00  ------ BMC1
% 2.58/1.00  
% 2.58/1.00  bmc1_current_bound:                     -1
% 2.58/1.00  bmc1_last_solved_bound:                 -1
% 2.58/1.00  bmc1_unsat_core_size:                   -1
% 2.58/1.00  bmc1_unsat_core_parents_size:           -1
% 2.58/1.00  bmc1_merge_next_fun:                    0
% 2.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation
% 2.58/1.00  
% 2.58/1.00  inst_num_of_clauses:                    318
% 2.58/1.00  inst_num_in_passive:                    35
% 2.58/1.00  inst_num_in_active:                     177
% 2.58/1.00  inst_num_in_unprocessed:                105
% 2.58/1.00  inst_num_of_loops:                      203
% 2.58/1.00  inst_num_of_learning_restarts:          0
% 2.58/1.00  inst_num_moves_active_passive:          23
% 2.58/1.00  inst_lit_activity:                      0
% 2.58/1.00  inst_lit_activity_moves:                0
% 2.58/1.00  inst_num_tautologies:                   0
% 2.58/1.00  inst_num_prop_implied:                  0
% 2.58/1.00  inst_num_existing_simplified:           0
% 2.58/1.00  inst_num_eq_res_simplified:             0
% 2.58/1.00  inst_num_child_elim:                    0
% 2.58/1.00  inst_num_of_dismatching_blockings:      52
% 2.58/1.00  inst_num_of_non_proper_insts:           213
% 2.58/1.00  inst_num_of_duplicates:                 0
% 2.58/1.00  inst_inst_num_from_inst_to_res:         0
% 2.58/1.00  inst_dismatching_checking_time:         0.
% 2.58/1.00  
% 2.58/1.00  ------ Resolution
% 2.58/1.00  
% 2.58/1.00  res_num_of_clauses:                     0
% 2.58/1.00  res_num_in_passive:                     0
% 2.58/1.00  res_num_in_active:                      0
% 2.58/1.00  res_num_of_loops:                       134
% 2.58/1.00  res_forward_subset_subsumed:            72
% 2.58/1.00  res_backward_subset_subsumed:           0
% 2.58/1.00  res_forward_subsumed:                   2
% 2.58/1.00  res_backward_subsumed:                  0
% 2.58/1.00  res_forward_subsumption_resolution:     0
% 2.58/1.00  res_backward_subsumption_resolution:    0
% 2.58/1.00  res_clause_to_clause_subsumption:       12073
% 2.58/1.00  res_orphan_elimination:                 0
% 2.58/1.00  res_tautology_del:                      21
% 2.58/1.00  res_num_eq_res_simplified:              0
% 2.58/1.00  res_num_sel_changes:                    0
% 2.58/1.00  res_moves_from_active_to_pass:          0
% 2.58/1.00  
% 2.58/1.00  ------ Superposition
% 2.58/1.00  
% 2.58/1.00  sup_time_total:                         0.
% 2.58/1.00  sup_time_generating:                    0.
% 2.58/1.00  sup_time_sim_full:                      0.
% 2.58/1.00  sup_time_sim_immed:                     0.
% 2.58/1.00  
% 2.58/1.00  sup_num_of_clauses:                     599
% 2.58/1.00  sup_num_in_active:                      37
% 2.58/1.00  sup_num_in_passive:                     562
% 2.58/1.00  sup_num_of_loops:                       40
% 2.58/1.00  sup_fw_superposition:                   1501
% 2.58/1.00  sup_bw_superposition:                   853
% 2.58/1.00  sup_immediate_simplified:               423
% 2.58/1.00  sup_given_eliminated:                   0
% 2.58/1.00  comparisons_done:                       0
% 2.58/1.00  comparisons_avoided:                    0
% 2.58/1.00  
% 2.58/1.00  ------ Simplifications
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  sim_fw_subset_subsumed:                 0
% 2.58/1.00  sim_bw_subset_subsumed:                 0
% 2.58/1.00  sim_fw_subsumed:                        44
% 2.58/1.00  sim_bw_subsumed:                        2
% 2.58/1.00  sim_fw_subsumption_res:                 0
% 2.58/1.00  sim_bw_subsumption_res:                 0
% 2.58/1.00  sim_tautology_del:                      0
% 2.58/1.00  sim_eq_tautology_del:                   81
% 2.58/1.00  sim_eq_res_simp:                        0
% 2.58/1.00  sim_fw_demodulated:                     124
% 2.58/1.00  sim_bw_demodulated:                     22
% 2.58/1.00  sim_light_normalised:                   207
% 2.58/1.00  sim_joinable_taut:                      53
% 2.58/1.00  sim_joinable_simp:                      0
% 2.58/1.00  sim_ac_normalised:                      0
% 2.58/1.00  sim_smt_subsumption:                    0
% 2.58/1.00  
%------------------------------------------------------------------------------
