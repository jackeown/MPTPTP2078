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
% DateTime   : Thu Dec  3 11:31:18 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 170 expanded)
%              Number of clauses        :   34 (  41 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  264 ( 407 expanded)
%              Number of equality atoms :  188 ( 292 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f44])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f81,f57,f93])).

fof(f124,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f107])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f71,f93])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK3 != sK6
      & sK3 != sK5
      & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( sK3 != sK6
    & sK3 != sK5
    & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f34,f49])).

fof(f89,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f89,f93,f93])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f78,f57,f93])).

fof(f90,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f93])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(definition_unfolding,[],[f84,f93])).

fof(f127,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f113])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f87,f57])).

fof(f129,plain,(
    ! [X1] : k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X1))) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f117])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_769,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_780,plain,
    ( k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_769,c_1])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_760,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_776,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3474,plain,
    ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_760,c_776])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X2),k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_766,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) != k1_tarski(X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12967,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4)) != k1_tarski(sK3)
    | r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3474,c_766])).

cnf(c_32,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_819,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,X0))
    | sK3 = X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1455,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6))
    | sK3 = sK5
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1456,plain,
    ( sK3 = sK5
    | sK3 = sK6
    | r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_13277,plain,
    ( r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12967,c_32,c_31,c_1456])).

cnf(c_13281,plain,
    ( k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k2_enumset1(sK5,sK5,sK5,sK6))) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_780,c_13277])).

cnf(c_26,plain,
    ( r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_763,plain,
    ( r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_777,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3641,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_777])).

cnf(c_4317,plain,
    ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top
    | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3474,c_3641])).

cnf(c_4535,plain,
    ( r1_tarski(k1_tarski(sK3),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_763,c_4317])).

cnf(c_4824,plain,
    ( k3_xboole_0(k1_tarski(sK3),k2_enumset1(sK5,sK5,sK5,sK6)) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_4535,c_776])).

cnf(c_13283,plain,
    ( k5_xboole_0(k1_tarski(sK3),k1_tarski(sK3)) = k1_tarski(sK3) ),
    inference(light_normalisation,[status(thm)],[c_13281,c_4824])).

cnf(c_30,plain,
    ( k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_779,plain,
    ( k5_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(demodulation,[status(thm)],[c_30,c_5])).

cnf(c_23174,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_13283,c_779])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.61/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.49  
% 7.61/1.49  ------  iProver source info
% 7.61/1.49  
% 7.61/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.49  git: non_committed_changes: false
% 7.61/1.49  git: last_make_outside_of_git: false
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  
% 7.61/1.49  ------ Input Options
% 7.61/1.49  
% 7.61/1.49  --out_options                           all
% 7.61/1.49  --tptp_safe_out                         true
% 7.61/1.49  --problem_path                          ""
% 7.61/1.49  --include_path                          ""
% 7.61/1.49  --clausifier                            res/vclausify_rel
% 7.61/1.49  --clausifier_options                    ""
% 7.61/1.49  --stdin                                 false
% 7.61/1.49  --stats_out                             all
% 7.61/1.49  
% 7.61/1.49  ------ General Options
% 7.61/1.49  
% 7.61/1.49  --fof                                   false
% 7.61/1.49  --time_out_real                         305.
% 7.61/1.49  --time_out_virtual                      -1.
% 7.61/1.49  --symbol_type_check                     false
% 7.61/1.49  --clausify_out                          false
% 7.61/1.49  --sig_cnt_out                           false
% 7.61/1.49  --trig_cnt_out                          false
% 7.61/1.49  --trig_cnt_out_tolerance                1.
% 7.61/1.49  --trig_cnt_out_sk_spl                   false
% 7.61/1.49  --abstr_cl_out                          false
% 7.61/1.49  
% 7.61/1.49  ------ Global Options
% 7.61/1.49  
% 7.61/1.49  --schedule                              default
% 7.61/1.49  --add_important_lit                     false
% 7.61/1.49  --prop_solver_per_cl                    1000
% 7.61/1.49  --min_unsat_core                        false
% 7.61/1.49  --soft_assumptions                      false
% 7.61/1.49  --soft_lemma_size                       3
% 7.61/1.49  --prop_impl_unit_size                   0
% 7.61/1.49  --prop_impl_unit                        []
% 7.61/1.49  --share_sel_clauses                     true
% 7.61/1.49  --reset_solvers                         false
% 7.61/1.49  --bc_imp_inh                            [conj_cone]
% 7.61/1.49  --conj_cone_tolerance                   3.
% 7.61/1.49  --extra_neg_conj                        none
% 7.61/1.49  --large_theory_mode                     true
% 7.61/1.49  --prolific_symb_bound                   200
% 7.61/1.49  --lt_threshold                          2000
% 7.61/1.49  --clause_weak_htbl                      true
% 7.61/1.49  --gc_record_bc_elim                     false
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing Options
% 7.61/1.49  
% 7.61/1.49  --preprocessing_flag                    true
% 7.61/1.49  --time_out_prep_mult                    0.1
% 7.61/1.49  --splitting_mode                        input
% 7.61/1.49  --splitting_grd                         true
% 7.61/1.49  --splitting_cvd                         false
% 7.61/1.49  --splitting_cvd_svl                     false
% 7.61/1.49  --splitting_nvd                         32
% 7.61/1.49  --sub_typing                            true
% 7.61/1.49  --prep_gs_sim                           true
% 7.61/1.49  --prep_unflatten                        true
% 7.61/1.49  --prep_res_sim                          true
% 7.61/1.49  --prep_upred                            true
% 7.61/1.49  --prep_sem_filter                       exhaustive
% 7.61/1.49  --prep_sem_filter_out                   false
% 7.61/1.49  --pred_elim                             true
% 7.61/1.49  --res_sim_input                         true
% 7.61/1.49  --eq_ax_congr_red                       true
% 7.61/1.49  --pure_diseq_elim                       true
% 7.61/1.49  --brand_transform                       false
% 7.61/1.49  --non_eq_to_eq                          false
% 7.61/1.49  --prep_def_merge                        true
% 7.61/1.49  --prep_def_merge_prop_impl              false
% 7.61/1.49  --prep_def_merge_mbd                    true
% 7.61/1.49  --prep_def_merge_tr_red                 false
% 7.61/1.49  --prep_def_merge_tr_cl                  false
% 7.61/1.49  --smt_preprocessing                     true
% 7.61/1.49  --smt_ac_axioms                         fast
% 7.61/1.49  --preprocessed_out                      false
% 7.61/1.49  --preprocessed_stats                    false
% 7.61/1.49  
% 7.61/1.49  ------ Abstraction refinement Options
% 7.61/1.49  
% 7.61/1.49  --abstr_ref                             []
% 7.61/1.49  --abstr_ref_prep                        false
% 7.61/1.49  --abstr_ref_until_sat                   false
% 7.61/1.49  --abstr_ref_sig_restrict                funpre
% 7.61/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.61/1.49  --abstr_ref_under                       []
% 7.61/1.49  
% 7.61/1.49  ------ SAT Options
% 7.61/1.49  
% 7.61/1.49  --sat_mode                              false
% 7.61/1.49  --sat_fm_restart_options                ""
% 7.61/1.49  --sat_gr_def                            false
% 7.61/1.49  --sat_epr_types                         true
% 7.61/1.49  --sat_non_cyclic_types                  false
% 7.61/1.49  --sat_finite_models                     false
% 7.61/1.49  --sat_fm_lemmas                         false
% 7.61/1.49  --sat_fm_prep                           false
% 7.61/1.49  --sat_fm_uc_incr                        true
% 7.61/1.49  --sat_out_model                         small
% 7.61/1.49  --sat_out_clauses                       false
% 7.61/1.49  
% 7.61/1.49  ------ QBF Options
% 7.61/1.49  
% 7.61/1.49  --qbf_mode                              false
% 7.61/1.49  --qbf_elim_univ                         false
% 7.61/1.49  --qbf_dom_inst                          none
% 7.61/1.49  --qbf_dom_pre_inst                      false
% 7.61/1.49  --qbf_sk_in                             false
% 7.61/1.49  --qbf_pred_elim                         true
% 7.61/1.49  --qbf_split                             512
% 7.61/1.49  
% 7.61/1.49  ------ BMC1 Options
% 7.61/1.49  
% 7.61/1.49  --bmc1_incremental                      false
% 7.61/1.49  --bmc1_axioms                           reachable_all
% 7.61/1.49  --bmc1_min_bound                        0
% 7.61/1.49  --bmc1_max_bound                        -1
% 7.61/1.49  --bmc1_max_bound_default                -1
% 7.61/1.49  --bmc1_symbol_reachability              true
% 7.61/1.49  --bmc1_property_lemmas                  false
% 7.61/1.49  --bmc1_k_induction                      false
% 7.61/1.49  --bmc1_non_equiv_states                 false
% 7.61/1.49  --bmc1_deadlock                         false
% 7.61/1.49  --bmc1_ucm                              false
% 7.61/1.49  --bmc1_add_unsat_core                   none
% 7.61/1.49  --bmc1_unsat_core_children              false
% 7.61/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.61/1.49  --bmc1_out_stat                         full
% 7.61/1.49  --bmc1_ground_init                      false
% 7.61/1.49  --bmc1_pre_inst_next_state              false
% 7.61/1.49  --bmc1_pre_inst_state                   false
% 7.61/1.49  --bmc1_pre_inst_reach_state             false
% 7.61/1.49  --bmc1_out_unsat_core                   false
% 7.61/1.49  --bmc1_aig_witness_out                  false
% 7.61/1.49  --bmc1_verbose                          false
% 7.61/1.49  --bmc1_dump_clauses_tptp                false
% 7.61/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.61/1.49  --bmc1_dump_file                        -
% 7.61/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.61/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.61/1.49  --bmc1_ucm_extend_mode                  1
% 7.61/1.49  --bmc1_ucm_init_mode                    2
% 7.61/1.49  --bmc1_ucm_cone_mode                    none
% 7.61/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.61/1.49  --bmc1_ucm_relax_model                  4
% 7.61/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.61/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.61/1.49  --bmc1_ucm_layered_model                none
% 7.61/1.49  --bmc1_ucm_max_lemma_size               10
% 7.61/1.49  
% 7.61/1.49  ------ AIG Options
% 7.61/1.49  
% 7.61/1.49  --aig_mode                              false
% 7.61/1.49  
% 7.61/1.49  ------ Instantiation Options
% 7.61/1.49  
% 7.61/1.49  --instantiation_flag                    true
% 7.61/1.49  --inst_sos_flag                         true
% 7.61/1.49  --inst_sos_phase                        true
% 7.61/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.61/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.61/1.49  --inst_lit_sel_side                     num_symb
% 7.61/1.49  --inst_solver_per_active                1400
% 7.61/1.49  --inst_solver_calls_frac                1.
% 7.61/1.49  --inst_passive_queue_type               priority_queues
% 7.61/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.61/1.49  --inst_passive_queues_freq              [25;2]
% 7.61/1.49  --inst_dismatching                      true
% 7.61/1.49  --inst_eager_unprocessed_to_passive     true
% 7.61/1.49  --inst_prop_sim_given                   true
% 7.61/1.49  --inst_prop_sim_new                     false
% 7.61/1.49  --inst_subs_new                         false
% 7.61/1.49  --inst_eq_res_simp                      false
% 7.61/1.49  --inst_subs_given                       false
% 7.61/1.49  --inst_orphan_elimination               true
% 7.61/1.49  --inst_learning_loop_flag               true
% 7.61/1.49  --inst_learning_start                   3000
% 7.61/1.49  --inst_learning_factor                  2
% 7.61/1.49  --inst_start_prop_sim_after_learn       3
% 7.61/1.49  --inst_sel_renew                        solver
% 7.61/1.49  --inst_lit_activity_flag                true
% 7.61/1.49  --inst_restr_to_given                   false
% 7.61/1.49  --inst_activity_threshold               500
% 7.61/1.49  --inst_out_proof                        true
% 7.61/1.49  
% 7.61/1.49  ------ Resolution Options
% 7.61/1.49  
% 7.61/1.49  --resolution_flag                       true
% 7.61/1.49  --res_lit_sel                           adaptive
% 7.61/1.49  --res_lit_sel_side                      none
% 7.61/1.49  --res_ordering                          kbo
% 7.61/1.49  --res_to_prop_solver                    active
% 7.61/1.49  --res_prop_simpl_new                    false
% 7.61/1.49  --res_prop_simpl_given                  true
% 7.61/1.49  --res_passive_queue_type                priority_queues
% 7.61/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.61/1.49  --res_passive_queues_freq               [15;5]
% 7.61/1.49  --res_forward_subs                      full
% 7.61/1.49  --res_backward_subs                     full
% 7.61/1.49  --res_forward_subs_resolution           true
% 7.61/1.49  --res_backward_subs_resolution          true
% 7.61/1.49  --res_orphan_elimination                true
% 7.61/1.49  --res_time_limit                        2.
% 7.61/1.49  --res_out_proof                         true
% 7.61/1.49  
% 7.61/1.49  ------ Superposition Options
% 7.61/1.49  
% 7.61/1.49  --superposition_flag                    true
% 7.61/1.49  --sup_passive_queue_type                priority_queues
% 7.61/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.61/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.61/1.49  --demod_completeness_check              fast
% 7.61/1.49  --demod_use_ground                      true
% 7.61/1.49  --sup_to_prop_solver                    passive
% 7.61/1.49  --sup_prop_simpl_new                    true
% 7.61/1.49  --sup_prop_simpl_given                  true
% 7.61/1.49  --sup_fun_splitting                     true
% 7.61/1.49  --sup_smt_interval                      50000
% 7.61/1.49  
% 7.61/1.49  ------ Superposition Simplification Setup
% 7.61/1.49  
% 7.61/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.61/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.61/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.61/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.61/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.61/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.61/1.49  --sup_immed_triv                        [TrivRules]
% 7.61/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.49  --sup_immed_bw_main                     []
% 7.61/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.61/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.61/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.49  --sup_input_bw                          []
% 7.61/1.49  
% 7.61/1.49  ------ Combination Options
% 7.61/1.49  
% 7.61/1.49  --comb_res_mult                         3
% 7.61/1.49  --comb_sup_mult                         2
% 7.61/1.49  --comb_inst_mult                        10
% 7.61/1.49  
% 7.61/1.49  ------ Debug Options
% 7.61/1.49  
% 7.61/1.49  --dbg_backtrace                         false
% 7.61/1.49  --dbg_dump_prop_clauses                 false
% 7.61/1.49  --dbg_dump_prop_clauses_file            -
% 7.61/1.49  --dbg_out_stat                          false
% 7.61/1.49  ------ Parsing...
% 7.61/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.49  ------ Proving...
% 7.61/1.49  ------ Problem Properties 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  clauses                                 33
% 7.61/1.49  conjectures                             3
% 7.61/1.49  EPR                                     2
% 7.61/1.49  Horn                                    25
% 7.61/1.49  unary                                   19
% 7.61/1.49  binary                                  7
% 7.61/1.49  lits                                    57
% 7.61/1.49  lits eq                                 33
% 7.61/1.49  fd_pure                                 0
% 7.61/1.49  fd_pseudo                               0
% 7.61/1.49  fd_cond                                 1
% 7.61/1.49  fd_pseudo_cond                          6
% 7.61/1.49  AC symbols                              0
% 7.61/1.49  
% 7.61/1.49  ------ Schedule dynamic 5 is on 
% 7.61/1.49  
% 7.61/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  Current options:
% 7.61/1.49  ------ 
% 7.61/1.49  
% 7.61/1.49  ------ Input Options
% 7.61/1.49  
% 7.61/1.49  --out_options                           all
% 7.61/1.49  --tptp_safe_out                         true
% 7.61/1.49  --problem_path                          ""
% 7.61/1.49  --include_path                          ""
% 7.61/1.49  --clausifier                            res/vclausify_rel
% 7.61/1.49  --clausifier_options                    ""
% 7.61/1.49  --stdin                                 false
% 7.61/1.49  --stats_out                             all
% 7.61/1.49  
% 7.61/1.49  ------ General Options
% 7.61/1.49  
% 7.61/1.49  --fof                                   false
% 7.61/1.49  --time_out_real                         305.
% 7.61/1.49  --time_out_virtual                      -1.
% 7.61/1.49  --symbol_type_check                     false
% 7.61/1.49  --clausify_out                          false
% 7.61/1.49  --sig_cnt_out                           false
% 7.61/1.49  --trig_cnt_out                          false
% 7.61/1.49  --trig_cnt_out_tolerance                1.
% 7.61/1.49  --trig_cnt_out_sk_spl                   false
% 7.61/1.49  --abstr_cl_out                          false
% 7.61/1.49  
% 7.61/1.49  ------ Global Options
% 7.61/1.49  
% 7.61/1.49  --schedule                              default
% 7.61/1.49  --add_important_lit                     false
% 7.61/1.49  --prop_solver_per_cl                    1000
% 7.61/1.49  --min_unsat_core                        false
% 7.61/1.49  --soft_assumptions                      false
% 7.61/1.49  --soft_lemma_size                       3
% 7.61/1.49  --prop_impl_unit_size                   0
% 7.61/1.49  --prop_impl_unit                        []
% 7.61/1.49  --share_sel_clauses                     true
% 7.61/1.49  --reset_solvers                         false
% 7.61/1.49  --bc_imp_inh                            [conj_cone]
% 7.61/1.49  --conj_cone_tolerance                   3.
% 7.61/1.49  --extra_neg_conj                        none
% 7.61/1.49  --large_theory_mode                     true
% 7.61/1.49  --prolific_symb_bound                   200
% 7.61/1.49  --lt_threshold                          2000
% 7.61/1.49  --clause_weak_htbl                      true
% 7.61/1.49  --gc_record_bc_elim                     false
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing Options
% 7.61/1.49  
% 7.61/1.49  --preprocessing_flag                    true
% 7.61/1.49  --time_out_prep_mult                    0.1
% 7.61/1.49  --splitting_mode                        input
% 7.61/1.49  --splitting_grd                         true
% 7.61/1.49  --splitting_cvd                         false
% 7.61/1.49  --splitting_cvd_svl                     false
% 7.61/1.49  --splitting_nvd                         32
% 7.61/1.49  --sub_typing                            true
% 7.61/1.49  --prep_gs_sim                           true
% 7.61/1.49  --prep_unflatten                        true
% 7.61/1.49  --prep_res_sim                          true
% 7.61/1.49  --prep_upred                            true
% 7.61/1.49  --prep_sem_filter                       exhaustive
% 7.61/1.49  --prep_sem_filter_out                   false
% 7.61/1.49  --pred_elim                             true
% 7.61/1.49  --res_sim_input                         true
% 7.61/1.49  --eq_ax_congr_red                       true
% 7.61/1.49  --pure_diseq_elim                       true
% 7.61/1.49  --brand_transform                       false
% 7.61/1.49  --non_eq_to_eq                          false
% 7.61/1.49  --prep_def_merge                        true
% 7.61/1.49  --prep_def_merge_prop_impl              false
% 7.61/1.49  --prep_def_merge_mbd                    true
% 7.61/1.49  --prep_def_merge_tr_red                 false
% 7.61/1.49  --prep_def_merge_tr_cl                  false
% 7.61/1.49  --smt_preprocessing                     true
% 7.61/1.49  --smt_ac_axioms                         fast
% 7.61/1.49  --preprocessed_out                      false
% 7.61/1.49  --preprocessed_stats                    false
% 7.61/1.49  
% 7.61/1.49  ------ Abstraction refinement Options
% 7.61/1.49  
% 7.61/1.49  --abstr_ref                             []
% 7.61/1.49  --abstr_ref_prep                        false
% 7.61/1.49  --abstr_ref_until_sat                   false
% 7.61/1.49  --abstr_ref_sig_restrict                funpre
% 7.61/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.61/1.49  --abstr_ref_under                       []
% 7.61/1.49  
% 7.61/1.49  ------ SAT Options
% 7.61/1.49  
% 7.61/1.49  --sat_mode                              false
% 7.61/1.49  --sat_fm_restart_options                ""
% 7.61/1.49  --sat_gr_def                            false
% 7.61/1.49  --sat_epr_types                         true
% 7.61/1.49  --sat_non_cyclic_types                  false
% 7.61/1.49  --sat_finite_models                     false
% 7.61/1.49  --sat_fm_lemmas                         false
% 7.61/1.49  --sat_fm_prep                           false
% 7.61/1.49  --sat_fm_uc_incr                        true
% 7.61/1.49  --sat_out_model                         small
% 7.61/1.49  --sat_out_clauses                       false
% 7.61/1.49  
% 7.61/1.49  ------ QBF Options
% 7.61/1.49  
% 7.61/1.49  --qbf_mode                              false
% 7.61/1.49  --qbf_elim_univ                         false
% 7.61/1.49  --qbf_dom_inst                          none
% 7.61/1.49  --qbf_dom_pre_inst                      false
% 7.61/1.49  --qbf_sk_in                             false
% 7.61/1.49  --qbf_pred_elim                         true
% 7.61/1.49  --qbf_split                             512
% 7.61/1.49  
% 7.61/1.49  ------ BMC1 Options
% 7.61/1.49  
% 7.61/1.49  --bmc1_incremental                      false
% 7.61/1.49  --bmc1_axioms                           reachable_all
% 7.61/1.49  --bmc1_min_bound                        0
% 7.61/1.49  --bmc1_max_bound                        -1
% 7.61/1.49  --bmc1_max_bound_default                -1
% 7.61/1.49  --bmc1_symbol_reachability              true
% 7.61/1.49  --bmc1_property_lemmas                  false
% 7.61/1.49  --bmc1_k_induction                      false
% 7.61/1.49  --bmc1_non_equiv_states                 false
% 7.61/1.49  --bmc1_deadlock                         false
% 7.61/1.49  --bmc1_ucm                              false
% 7.61/1.49  --bmc1_add_unsat_core                   none
% 7.61/1.49  --bmc1_unsat_core_children              false
% 7.61/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.61/1.49  --bmc1_out_stat                         full
% 7.61/1.49  --bmc1_ground_init                      false
% 7.61/1.49  --bmc1_pre_inst_next_state              false
% 7.61/1.49  --bmc1_pre_inst_state                   false
% 7.61/1.49  --bmc1_pre_inst_reach_state             false
% 7.61/1.49  --bmc1_out_unsat_core                   false
% 7.61/1.49  --bmc1_aig_witness_out                  false
% 7.61/1.49  --bmc1_verbose                          false
% 7.61/1.49  --bmc1_dump_clauses_tptp                false
% 7.61/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.61/1.49  --bmc1_dump_file                        -
% 7.61/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.61/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.61/1.49  --bmc1_ucm_extend_mode                  1
% 7.61/1.49  --bmc1_ucm_init_mode                    2
% 7.61/1.49  --bmc1_ucm_cone_mode                    none
% 7.61/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.61/1.49  --bmc1_ucm_relax_model                  4
% 7.61/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.61/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.61/1.49  --bmc1_ucm_layered_model                none
% 7.61/1.49  --bmc1_ucm_max_lemma_size               10
% 7.61/1.49  
% 7.61/1.49  ------ AIG Options
% 7.61/1.49  
% 7.61/1.49  --aig_mode                              false
% 7.61/1.49  
% 7.61/1.49  ------ Instantiation Options
% 7.61/1.49  
% 7.61/1.49  --instantiation_flag                    true
% 7.61/1.49  --inst_sos_flag                         true
% 7.61/1.49  --inst_sos_phase                        true
% 7.61/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.61/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.61/1.49  --inst_lit_sel_side                     none
% 7.61/1.49  --inst_solver_per_active                1400
% 7.61/1.49  --inst_solver_calls_frac                1.
% 7.61/1.49  --inst_passive_queue_type               priority_queues
% 7.61/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.61/1.49  --inst_passive_queues_freq              [25;2]
% 7.61/1.49  --inst_dismatching                      true
% 7.61/1.49  --inst_eager_unprocessed_to_passive     true
% 7.61/1.49  --inst_prop_sim_given                   true
% 7.61/1.49  --inst_prop_sim_new                     false
% 7.61/1.49  --inst_subs_new                         false
% 7.61/1.49  --inst_eq_res_simp                      false
% 7.61/1.49  --inst_subs_given                       false
% 7.61/1.49  --inst_orphan_elimination               true
% 7.61/1.49  --inst_learning_loop_flag               true
% 7.61/1.49  --inst_learning_start                   3000
% 7.61/1.49  --inst_learning_factor                  2
% 7.61/1.49  --inst_start_prop_sim_after_learn       3
% 7.61/1.49  --inst_sel_renew                        solver
% 7.61/1.49  --inst_lit_activity_flag                true
% 7.61/1.49  --inst_restr_to_given                   false
% 7.61/1.49  --inst_activity_threshold               500
% 7.61/1.49  --inst_out_proof                        true
% 7.61/1.49  
% 7.61/1.49  ------ Resolution Options
% 7.61/1.49  
% 7.61/1.49  --resolution_flag                       false
% 7.61/1.49  --res_lit_sel                           adaptive
% 7.61/1.49  --res_lit_sel_side                      none
% 7.61/1.49  --res_ordering                          kbo
% 7.61/1.49  --res_to_prop_solver                    active
% 7.61/1.49  --res_prop_simpl_new                    false
% 7.61/1.49  --res_prop_simpl_given                  true
% 7.61/1.49  --res_passive_queue_type                priority_queues
% 7.61/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.61/1.49  --res_passive_queues_freq               [15;5]
% 7.61/1.49  --res_forward_subs                      full
% 7.61/1.49  --res_backward_subs                     full
% 7.61/1.49  --res_forward_subs_resolution           true
% 7.61/1.49  --res_backward_subs_resolution          true
% 7.61/1.49  --res_orphan_elimination                true
% 7.61/1.49  --res_time_limit                        2.
% 7.61/1.49  --res_out_proof                         true
% 7.61/1.49  
% 7.61/1.49  ------ Superposition Options
% 7.61/1.49  
% 7.61/1.49  --superposition_flag                    true
% 7.61/1.49  --sup_passive_queue_type                priority_queues
% 7.61/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.61/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.61/1.49  --demod_completeness_check              fast
% 7.61/1.49  --demod_use_ground                      true
% 7.61/1.49  --sup_to_prop_solver                    passive
% 7.61/1.49  --sup_prop_simpl_new                    true
% 7.61/1.49  --sup_prop_simpl_given                  true
% 7.61/1.49  --sup_fun_splitting                     true
% 7.61/1.49  --sup_smt_interval                      50000
% 7.61/1.49  
% 7.61/1.49  ------ Superposition Simplification Setup
% 7.61/1.49  
% 7.61/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.61/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.61/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.61/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.61/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.61/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.61/1.49  --sup_immed_triv                        [TrivRules]
% 7.61/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.49  --sup_immed_bw_main                     []
% 7.61/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.61/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.61/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.49  --sup_input_bw                          []
% 7.61/1.49  
% 7.61/1.49  ------ Combination Options
% 7.61/1.49  
% 7.61/1.49  --comb_res_mult                         3
% 7.61/1.49  --comb_sup_mult                         2
% 7.61/1.49  --comb_inst_mult                        10
% 7.61/1.49  
% 7.61/1.49  ------ Debug Options
% 7.61/1.49  
% 7.61/1.49  --dbg_backtrace                         false
% 7.61/1.49  --dbg_dump_prop_clauses                 false
% 7.61/1.49  --dbg_dump_prop_clauses_file            -
% 7.61/1.49  --dbg_out_stat                          false
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ Proving...
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS status Theorem for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49   Resolution empty clause
% 7.61/1.49  
% 7.61/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  fof(f22,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f44,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 7.61/1.49    inference(nnf_transformation,[],[f22])).
% 7.61/1.49  
% 7.61/1.49  fof(f45,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 7.61/1.49    inference(flattening,[],[f44])).
% 7.61/1.49  
% 7.61/1.49  fof(f81,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f45])).
% 7.61/1.49  
% 7.61/1.49  fof(f6,axiom,(
% 7.61/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f57,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f6])).
% 7.61/1.49  
% 7.61/1.49  fof(f16,axiom,(
% 7.61/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f72,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f16])).
% 7.61/1.49  
% 7.61/1.49  fof(f17,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f73,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f17])).
% 7.61/1.49  
% 7.61/1.49  fof(f93,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f72,f73])).
% 7.61/1.49  
% 7.61/1.49  fof(f107,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) = k1_tarski(X0) | X0 != X1 | r2_hidden(X0,X2)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f81,f57,f93])).
% 7.61/1.49  
% 7.61/1.49  fof(f124,plain,(
% 7.61/1.49    ( ! [X2,X1] : (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k1_tarski(X1) | r2_hidden(X1,X2)) )),
% 7.61/1.49    inference(equality_resolution,[],[f107])).
% 7.61/1.49  
% 7.61/1.49  fof(f15,axiom,(
% 7.61/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f71,plain,(
% 7.61/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f15])).
% 7.61/1.49  
% 7.61/1.49  fof(f97,plain,(
% 7.61/1.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f71,f93])).
% 7.61/1.49  
% 7.61/1.49  fof(f25,conjecture,(
% 7.61/1.49    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f26,negated_conjecture,(
% 7.61/1.49    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.61/1.49    inference(negated_conjecture,[],[f25])).
% 7.61/1.49  
% 7.61/1.49  fof(f34,plain,(
% 7.61/1.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.61/1.49    inference(ennf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f49,plain,(
% 7.61/1.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f50,plain,(
% 7.61/1.49    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f34,f49])).
% 7.61/1.49  
% 7.61/1.49  fof(f89,plain,(
% 7.61/1.49    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.61/1.49    inference(cnf_transformation,[],[f50])).
% 7.61/1.49  
% 7.61/1.49  fof(f118,plain,(
% 7.61/1.49    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))),
% 7.61/1.49    inference(definition_unfolding,[],[f89,f93,f93])).
% 7.61/1.49  
% 7.61/1.49  fof(f8,axiom,(
% 7.61/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f32,plain,(
% 7.61/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.61/1.49    inference(ennf_transformation,[],[f8])).
% 7.61/1.49  
% 7.61/1.49  fof(f59,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f32])).
% 7.61/1.49  
% 7.61/1.49  fof(f78,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f45])).
% 7.61/1.49  
% 7.61/1.49  fof(f110,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) != k1_tarski(X0)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f78,f57,f93])).
% 7.61/1.49  
% 7.61/1.49  fof(f90,plain,(
% 7.61/1.49    sK3 != sK5),
% 7.61/1.49    inference(cnf_transformation,[],[f50])).
% 7.61/1.49  
% 7.61/1.49  fof(f91,plain,(
% 7.61/1.49    sK3 != sK6),
% 7.61/1.49    inference(cnf_transformation,[],[f50])).
% 7.61/1.49  
% 7.61/1.49  fof(f13,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f39,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.49    inference(nnf_transformation,[],[f13])).
% 7.61/1.49  
% 7.61/1.49  fof(f40,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.49    inference(flattening,[],[f39])).
% 7.61/1.49  
% 7.61/1.49  fof(f41,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.49    inference(rectify,[],[f40])).
% 7.61/1.49  
% 7.61/1.49  fof(f42,plain,(
% 7.61/1.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f43,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 7.61/1.49  
% 7.61/1.49  fof(f64,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.61/1.49    inference(cnf_transformation,[],[f43])).
% 7.61/1.49  
% 7.61/1.49  fof(f105,plain,(
% 7.61/1.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.61/1.49    inference(definition_unfolding,[],[f64,f93])).
% 7.61/1.49  
% 7.61/1.49  fof(f123,plain,(
% 7.61/1.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.61/1.49    inference(equality_resolution,[],[f105])).
% 7.61/1.49  
% 7.61/1.49  fof(f23,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f33,plain,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f23])).
% 7.61/1.49  
% 7.61/1.49  fof(f46,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.61/1.49    inference(nnf_transformation,[],[f33])).
% 7.61/1.49  
% 7.61/1.49  fof(f47,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.61/1.49    inference(flattening,[],[f46])).
% 7.61/1.49  
% 7.61/1.49  fof(f84,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 7.61/1.49    inference(cnf_transformation,[],[f47])).
% 7.61/1.49  
% 7.61/1.49  fof(f113,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k1_tarski(X1) != X0) )),
% 7.61/1.49    inference(definition_unfolding,[],[f84,f93])).
% 7.61/1.49  
% 7.61/1.49  fof(f127,plain,(
% 7.61/1.49    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_enumset1(X1,X1,X1,X2))) )),
% 7.61/1.49    inference(equality_resolution,[],[f113])).
% 7.61/1.49  
% 7.61/1.49  fof(f2,axiom,(
% 7.61/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f52,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f2])).
% 7.61/1.49  
% 7.61/1.49  fof(f7,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f31,plain,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.61/1.49    inference(ennf_transformation,[],[f7])).
% 7.61/1.49  
% 7.61/1.49  fof(f58,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 7.61/1.49    inference(cnf_transformation,[],[f31])).
% 7.61/1.49  
% 7.61/1.49  fof(f24,axiom,(
% 7.61/1.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f48,plain,(
% 7.61/1.49    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.61/1.49    inference(nnf_transformation,[],[f24])).
% 7.61/1.49  
% 7.61/1.49  fof(f87,plain,(
% 7.61/1.49    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f48])).
% 7.61/1.49  
% 7.61/1.49  fof(f117,plain,(
% 7.61/1.49    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) != k1_tarski(X0)) )),
% 7.61/1.49    inference(definition_unfolding,[],[f87,f57])).
% 7.61/1.49  
% 7.61/1.49  fof(f129,plain,(
% 7.61/1.49    ( ! [X1] : (k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X1))) != k1_tarski(X1)) )),
% 7.61/1.49    inference(equality_resolution,[],[f117])).
% 7.61/1.49  
% 7.61/1.49  fof(f3,axiom,(
% 7.61/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f27,plain,(
% 7.61/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.61/1.49    inference(rectify,[],[f3])).
% 7.61/1.49  
% 7.61/1.49  fof(f53,plain,(
% 7.61/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.61/1.49    inference(cnf_transformation,[],[f27])).
% 7.61/1.49  
% 7.61/1.49  cnf(c_20,plain,
% 7.61/1.49      ( r2_hidden(X0,X1)
% 7.61/1.49      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k1_tarski(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_769,plain,
% 7.61/1.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k1_tarski(X0)
% 7.61/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1,plain,
% 7.61/1.49      ( k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_780,plain,
% 7.61/1.49      ( k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
% 7.61/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 7.61/1.49      inference(light_normalisation,[status(thm)],[c_769,c_1]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_33,negated_conjecture,
% 7.61/1.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_760,plain,
% 7.61/1.49      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_10,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.61/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_776,plain,
% 7.61/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_3474,plain,
% 7.61/1.49      ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_760,c_776]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_23,plain,
% 7.61/1.49      ( ~ r2_hidden(X0,X1)
% 7.61/1.49      | k5_xboole_0(k2_enumset1(X0,X0,X0,X2),k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)) != k1_tarski(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_766,plain,
% 7.61/1.49      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) != k1_tarski(X0)
% 7.61/1.49      | r2_hidden(X0,X2) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12967,plain,
% 7.61/1.49      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4)) != k1_tarski(sK3)
% 7.61/1.49      | r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_3474,c_766]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_32,negated_conjecture,
% 7.61/1.49      ( sK3 != sK5 ),
% 7.61/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_31,negated_conjecture,
% 7.61/1.49      ( sK3 != sK6 ),
% 7.61/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_18,plain,
% 7.61/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.61/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_819,plain,
% 7.61/1.49      ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,X0)) | sK3 = X0 | sK3 = sK5 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1455,plain,
% 7.61/1.49      ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) | sK3 = sK5 | sK3 = sK6 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_819]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1456,plain,
% 7.61/1.49      ( sK3 = sK5
% 7.61/1.49      | sK3 = sK6
% 7.61/1.49      | r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13277,plain,
% 7.61/1.49      ( r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK6)) != iProver_top ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_12967,c_32,c_31,c_1456]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13281,plain,
% 7.61/1.49      ( k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k2_enumset1(sK5,sK5,sK5,sK6))) = k1_tarski(sK3) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_780,c_13277]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_26,plain,
% 7.61/1.49      ( r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_763,plain,
% 7.61/1.49      ( r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4,plain,
% 7.61/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_9,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_777,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.61/1.49      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_3641,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.61/1.49      | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_4,c_777]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4317,plain,
% 7.61/1.49      ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top
% 7.61/1.49      | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_3474,c_3641]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4535,plain,
% 7.61/1.49      ( r1_tarski(k1_tarski(sK3),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_763,c_4317]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4824,plain,
% 7.61/1.49      ( k3_xboole_0(k1_tarski(sK3),k2_enumset1(sK5,sK5,sK5,sK6)) = k1_tarski(sK3) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_4535,c_776]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13283,plain,
% 7.61/1.49      ( k5_xboole_0(k1_tarski(sK3),k1_tarski(sK3)) = k1_tarski(sK3) ),
% 7.61/1.49      inference(light_normalisation,[status(thm)],[c_13281,c_4824]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_30,plain,
% 7.61/1.49      ( k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) != k1_tarski(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f129]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5,plain,
% 7.61/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.61/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_779,plain,
% 7.61/1.49      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
% 7.61/1.49      inference(demodulation,[status(thm)],[c_30,c_5]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_23174,plain,
% 7.61/1.49      ( $false ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_13283,c_779]) ).
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  ------                               Statistics
% 7.61/1.49  
% 7.61/1.49  ------ General
% 7.61/1.49  
% 7.61/1.49  abstr_ref_over_cycles:                  0
% 7.61/1.49  abstr_ref_under_cycles:                 0
% 7.61/1.49  gc_basic_clause_elim:                   0
% 7.61/1.49  forced_gc_time:                         0
% 7.61/1.49  parsing_time:                           0.013
% 7.61/1.49  unif_index_cands_time:                  0.
% 7.61/1.49  unif_index_add_time:                    0.
% 7.61/1.49  orderings_time:                         0.
% 7.61/1.49  out_proof_time:                         0.008
% 7.61/1.49  total_time:                             0.819
% 7.61/1.49  num_of_symbols:                         47
% 7.61/1.49  num_of_terms:                           29572
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing
% 7.61/1.49  
% 7.61/1.49  num_of_splits:                          0
% 7.61/1.49  num_of_split_atoms:                     0
% 7.61/1.49  num_of_reused_defs:                     0
% 7.61/1.49  num_eq_ax_congr_red:                    46
% 7.61/1.49  num_of_sem_filtered_clauses:            1
% 7.61/1.49  num_of_subtypes:                        0
% 7.61/1.49  monotx_restored_types:                  0
% 7.61/1.49  sat_num_of_epr_types:                   0
% 7.61/1.49  sat_num_of_non_cyclic_types:            0
% 7.61/1.49  sat_guarded_non_collapsed_types:        0
% 7.61/1.49  num_pure_diseq_elim:                    0
% 7.61/1.49  simp_replaced_by:                       0
% 7.61/1.49  res_preprocessed:                       148
% 7.61/1.49  prep_upred:                             0
% 7.61/1.49  prep_unflattend:                        4
% 7.61/1.49  smt_new_axioms:                         0
% 7.61/1.49  pred_elim_cands:                        2
% 7.61/1.49  pred_elim:                              1
% 7.61/1.49  pred_elim_cl:                           1
% 7.61/1.49  pred_elim_cycles:                       3
% 7.61/1.49  merged_defs:                            0
% 7.61/1.49  merged_defs_ncl:                        0
% 7.61/1.49  bin_hyper_res:                          0
% 7.61/1.49  prep_cycles:                            4
% 7.61/1.49  pred_elim_time:                         0.002
% 7.61/1.49  splitting_time:                         0.
% 7.61/1.49  sem_filter_time:                        0.
% 7.61/1.49  monotx_time:                            0.
% 7.61/1.49  subtype_inf_time:                       0.
% 7.61/1.49  
% 7.61/1.49  ------ Problem properties
% 7.61/1.49  
% 7.61/1.49  clauses:                                33
% 7.61/1.49  conjectures:                            3
% 7.61/1.49  epr:                                    2
% 7.61/1.49  horn:                                   25
% 7.61/1.49  ground:                                 3
% 7.61/1.49  unary:                                  19
% 7.61/1.49  binary:                                 7
% 7.61/1.49  lits:                                   57
% 7.61/1.49  lits_eq:                                33
% 7.61/1.49  fd_pure:                                0
% 7.61/1.49  fd_pseudo:                              0
% 7.61/1.49  fd_cond:                                1
% 7.61/1.49  fd_pseudo_cond:                         6
% 7.61/1.49  ac_symbols:                             0
% 7.61/1.49  
% 7.61/1.49  ------ Propositional Solver
% 7.61/1.49  
% 7.61/1.49  prop_solver_calls:                      32
% 7.61/1.49  prop_fast_solver_calls:                 1577
% 7.61/1.49  smt_solver_calls:                       0
% 7.61/1.49  smt_fast_solver_calls:                  0
% 7.61/1.49  prop_num_of_clauses:                    8415
% 7.61/1.49  prop_preprocess_simplified:             16958
% 7.61/1.49  prop_fo_subsumed:                       161
% 7.61/1.49  prop_solver_time:                       0.
% 7.61/1.49  smt_solver_time:                        0.
% 7.61/1.49  smt_fast_solver_time:                   0.
% 7.61/1.49  prop_fast_solver_time:                  0.
% 7.61/1.49  prop_unsat_core_time:                   0.
% 7.61/1.49  
% 7.61/1.49  ------ QBF
% 7.61/1.49  
% 7.61/1.49  qbf_q_res:                              0
% 7.61/1.49  qbf_num_tautologies:                    0
% 7.61/1.49  qbf_prep_cycles:                        0
% 7.61/1.49  
% 7.61/1.49  ------ BMC1
% 7.61/1.49  
% 7.61/1.49  bmc1_current_bound:                     -1
% 7.61/1.49  bmc1_last_solved_bound:                 -1
% 7.61/1.49  bmc1_unsat_core_size:                   -1
% 7.61/1.49  bmc1_unsat_core_parents_size:           -1
% 7.61/1.49  bmc1_merge_next_fun:                    0
% 7.61/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.61/1.49  
% 7.61/1.49  ------ Instantiation
% 7.61/1.49  
% 7.61/1.49  inst_num_of_clauses:                    2065
% 7.61/1.49  inst_num_in_passive:                    1067
% 7.61/1.49  inst_num_in_active:                     725
% 7.61/1.49  inst_num_in_unprocessed:                273
% 7.61/1.49  inst_num_of_loops:                      1080
% 7.61/1.49  inst_num_of_learning_restarts:          0
% 7.61/1.49  inst_num_moves_active_passive:          351
% 7.61/1.49  inst_lit_activity:                      0
% 7.61/1.49  inst_lit_activity_moves:                0
% 7.61/1.49  inst_num_tautologies:                   0
% 7.61/1.49  inst_num_prop_implied:                  0
% 7.61/1.49  inst_num_existing_simplified:           0
% 7.61/1.49  inst_num_eq_res_simplified:             0
% 7.61/1.49  inst_num_child_elim:                    0
% 7.61/1.49  inst_num_of_dismatching_blockings:      2507
% 7.61/1.49  inst_num_of_non_proper_insts:           3306
% 7.61/1.49  inst_num_of_duplicates:                 0
% 7.61/1.49  inst_inst_num_from_inst_to_res:         0
% 7.61/1.49  inst_dismatching_checking_time:         0.
% 7.61/1.49  
% 7.61/1.49  ------ Resolution
% 7.61/1.49  
% 7.61/1.49  res_num_of_clauses:                     0
% 7.61/1.49  res_num_in_passive:                     0
% 7.61/1.49  res_num_in_active:                      0
% 7.61/1.49  res_num_of_loops:                       152
% 7.61/1.49  res_forward_subset_subsumed:            609
% 7.61/1.49  res_backward_subset_subsumed:           16
% 7.61/1.49  res_forward_subsumed:                   0
% 7.61/1.49  res_backward_subsumed:                  0
% 7.61/1.49  res_forward_subsumption_resolution:     0
% 7.61/1.49  res_backward_subsumption_resolution:    0
% 7.61/1.49  res_clause_to_clause_subsumption:       6499
% 7.61/1.49  res_orphan_elimination:                 0
% 7.61/1.49  res_tautology_del:                      122
% 7.61/1.49  res_num_eq_res_simplified:              0
% 7.61/1.49  res_num_sel_changes:                    0
% 7.61/1.49  res_moves_from_active_to_pass:          0
% 7.61/1.49  
% 7.61/1.49  ------ Superposition
% 7.61/1.49  
% 7.61/1.49  sup_time_total:                         0.
% 7.61/1.49  sup_time_generating:                    0.
% 7.61/1.49  sup_time_sim_full:                      0.
% 7.61/1.49  sup_time_sim_immed:                     0.
% 7.61/1.49  
% 7.61/1.49  sup_num_of_clauses:                     807
% 7.61/1.49  sup_num_in_active:                      161
% 7.61/1.49  sup_num_in_passive:                     646
% 7.61/1.49  sup_num_of_loops:                       214
% 7.61/1.49  sup_fw_superposition:                   2327
% 7.61/1.49  sup_bw_superposition:                   1881
% 7.61/1.49  sup_immediate_simplified:               1091
% 7.61/1.49  sup_given_eliminated:                   5
% 7.61/1.49  comparisons_done:                       0
% 7.61/1.49  comparisons_avoided:                    321
% 7.61/1.49  
% 7.61/1.49  ------ Simplifications
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  sim_fw_subset_subsumed:                 113
% 7.61/1.49  sim_bw_subset_subsumed:                 377
% 7.61/1.49  sim_fw_subsumed:                        100
% 7.61/1.49  sim_bw_subsumed:                        15
% 7.61/1.49  sim_fw_subsumption_res:                 0
% 7.61/1.49  sim_bw_subsumption_res:                 0
% 7.61/1.49  sim_tautology_del:                      26
% 7.61/1.49  sim_eq_tautology_del:                   378
% 7.61/1.49  sim_eq_res_simp:                        12
% 7.61/1.49  sim_fw_demodulated:                     748
% 7.61/1.49  sim_bw_demodulated:                     30
% 7.61/1.49  sim_light_normalised:                   303
% 7.61/1.49  sim_joinable_taut:                      0
% 7.61/1.49  sim_joinable_simp:                      0
% 7.61/1.49  sim_ac_normalised:                      0
% 7.61/1.49  sim_smt_subsumption:                    0
% 7.61/1.49  
%------------------------------------------------------------------------------
