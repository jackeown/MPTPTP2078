%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:33 EST 2020

% Result     : Theorem 19.86s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 561 expanded)
%              Number of clauses        :   60 ( 103 expanded)
%              Number of leaves         :   15 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  368 (2207 expanded)
%              Number of equality atoms :  181 ( 920 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f22])).

fof(f39,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f63,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f40,plain,(
    k3_xboole_0(sK3,sK4) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f40,f31,f44])).

fof(f42,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f42,f31,f44])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f61,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f62,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f61])).

fof(f41,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f31])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_346,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_336,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_342,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_768,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_336,c_342])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_344,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1829,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_344])).

cnf(c_2055,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_346,c_1829])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_338,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3230,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,X1))
    | sK0(sK2,X1,k2_enumset1(X0,X0,X0,X0)) = X0
    | r2_hidden(sK0(sK2,X1,k2_enumset1(X0,X0,X0,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_338])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_347,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_345,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_627,plain,
    ( sK5 = X0
    | r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_338])).

cnf(c_1188,plain,
    ( sK5 = X0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_345,c_627])).

cnf(c_2287,plain,
    ( sK0(X0,sK4,X1) = sK5
    | k4_xboole_0(X0,k4_xboole_0(X0,sK4)) = X1
    | r2_hidden(sK0(X0,sK4,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,sK4,X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_347,c_1188])).

cnf(c_68162,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | sK0(sK2,sK4,k2_enumset1(X0,X0,X0,X0)) = X0
    | sK0(sK2,sK4,k2_enumset1(X0,X0,X0,X0)) = sK5
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3230,c_2287])).

cnf(c_68267,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_68162])).

cnf(c_126,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_479,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_7685,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
    | X1 != X0
    | k2_enumset1(X2,X3,X4,X5) != k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_55227,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(X0,X0,X0,X0)
    | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_7685])).

cnf(c_55229,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_55227])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2395,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
    inference(resolution,[status(thm)],[c_1,c_11])).

cnf(c_2687,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
    | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(resolution,[status(thm)],[c_2395,c_10])).

cnf(c_1051,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_126,c_13])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1083,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
    | X0 != sK5 ),
    inference(resolution,[status(thm)],[c_1051,c_9])).

cnf(c_1210,plain,
    ( r2_hidden(X0,sK4)
    | X0 != sK5 ),
    inference(resolution,[status(thm)],[c_1083,c_4])).

cnf(c_3001,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2687,c_1210])).

cnf(c_3002,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3001])).

cnf(c_2457,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_123,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_579,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_484,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK2)
    | X0 != sK5
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_578,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(sK5,sK2)
    | X0 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_719,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | ~ r2_hidden(sK5,sK2)
    | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1633,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2692,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2457,c_12,c_579,c_719,c_1633])).

cnf(c_2694,plain,
    ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2692])).

cnf(c_615,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_124,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_455,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_614,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_522,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
    | ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_523,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_128,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_132,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK5,sK5,sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_21,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_68267,c_55229,c_3002,c_3001,c_2694,c_2692,c_615,c_614,c_523,c_522,c_132,c_21,c_18,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.86/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.86/2.99  
% 19.86/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.86/2.99  
% 19.86/2.99  ------  iProver source info
% 19.86/2.99  
% 19.86/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.86/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.86/2.99  git: non_committed_changes: false
% 19.86/2.99  git: last_make_outside_of_git: false
% 19.86/2.99  
% 19.86/2.99  ------ 
% 19.86/2.99  
% 19.86/2.99  ------ Input Options
% 19.86/2.99  
% 19.86/2.99  --out_options                           all
% 19.86/2.99  --tptp_safe_out                         true
% 19.86/2.99  --problem_path                          ""
% 19.86/2.99  --include_path                          ""
% 19.86/2.99  --clausifier                            res/vclausify_rel
% 19.86/2.99  --clausifier_options                    --mode clausify
% 19.86/2.99  --stdin                                 false
% 19.86/2.99  --stats_out                             sel
% 19.86/2.99  
% 19.86/2.99  ------ General Options
% 19.86/2.99  
% 19.86/2.99  --fof                                   false
% 19.86/2.99  --time_out_real                         604.99
% 19.86/2.99  --time_out_virtual                      -1.
% 19.86/2.99  --symbol_type_check                     false
% 19.86/2.99  --clausify_out                          false
% 19.86/2.99  --sig_cnt_out                           false
% 19.86/2.99  --trig_cnt_out                          false
% 19.86/2.99  --trig_cnt_out_tolerance                1.
% 19.86/2.99  --trig_cnt_out_sk_spl                   false
% 19.86/2.99  --abstr_cl_out                          false
% 19.86/2.99  
% 19.86/2.99  ------ Global Options
% 19.86/2.99  
% 19.86/2.99  --schedule                              none
% 19.86/2.99  --add_important_lit                     false
% 19.86/2.99  --prop_solver_per_cl                    1000
% 19.86/2.99  --min_unsat_core                        false
% 19.86/2.99  --soft_assumptions                      false
% 19.86/2.99  --soft_lemma_size                       3
% 19.86/2.99  --prop_impl_unit_size                   0
% 19.86/2.99  --prop_impl_unit                        []
% 19.86/2.99  --share_sel_clauses                     true
% 19.86/2.99  --reset_solvers                         false
% 19.86/2.99  --bc_imp_inh                            [conj_cone]
% 19.86/2.99  --conj_cone_tolerance                   3.
% 19.86/2.99  --extra_neg_conj                        none
% 19.86/2.99  --large_theory_mode                     true
% 19.86/2.99  --prolific_symb_bound                   200
% 19.86/2.99  --lt_threshold                          2000
% 19.86/2.99  --clause_weak_htbl                      true
% 19.86/2.99  --gc_record_bc_elim                     false
% 19.86/2.99  
% 19.86/2.99  ------ Preprocessing Options
% 19.86/2.99  
% 19.86/2.99  --preprocessing_flag                    true
% 19.86/2.99  --time_out_prep_mult                    0.1
% 19.86/2.99  --splitting_mode                        input
% 19.86/2.99  --splitting_grd                         true
% 19.86/2.99  --splitting_cvd                         false
% 19.86/2.99  --splitting_cvd_svl                     false
% 19.86/2.99  --splitting_nvd                         32
% 19.86/2.99  --sub_typing                            true
% 19.86/2.99  --prep_gs_sim                           false
% 19.86/2.99  --prep_unflatten                        true
% 19.86/2.99  --prep_res_sim                          true
% 19.86/2.99  --prep_upred                            true
% 19.86/2.99  --prep_sem_filter                       exhaustive
% 19.86/2.99  --prep_sem_filter_out                   false
% 19.86/2.99  --pred_elim                             false
% 19.86/2.99  --res_sim_input                         true
% 19.86/2.99  --eq_ax_congr_red                       true
% 19.86/2.99  --pure_diseq_elim                       true
% 19.86/2.99  --brand_transform                       false
% 19.86/2.99  --non_eq_to_eq                          false
% 19.86/2.99  --prep_def_merge                        true
% 19.86/2.99  --prep_def_merge_prop_impl              false
% 19.86/2.99  --prep_def_merge_mbd                    true
% 19.86/2.99  --prep_def_merge_tr_red                 false
% 19.86/2.99  --prep_def_merge_tr_cl                  false
% 19.86/2.99  --smt_preprocessing                     true
% 19.86/2.99  --smt_ac_axioms                         fast
% 19.86/2.99  --preprocessed_out                      false
% 19.86/2.99  --preprocessed_stats                    false
% 19.86/2.99  
% 19.86/2.99  ------ Abstraction refinement Options
% 19.86/2.99  
% 19.86/2.99  --abstr_ref                             []
% 19.86/2.99  --abstr_ref_prep                        false
% 19.86/2.99  --abstr_ref_until_sat                   false
% 19.86/2.99  --abstr_ref_sig_restrict                funpre
% 19.86/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.86/2.99  --abstr_ref_under                       []
% 19.86/2.99  
% 19.86/2.99  ------ SAT Options
% 19.86/2.99  
% 19.86/2.99  --sat_mode                              false
% 19.86/2.99  --sat_fm_restart_options                ""
% 19.86/2.99  --sat_gr_def                            false
% 19.86/2.99  --sat_epr_types                         true
% 19.86/2.99  --sat_non_cyclic_types                  false
% 19.86/2.99  --sat_finite_models                     false
% 19.86/2.99  --sat_fm_lemmas                         false
% 19.86/2.99  --sat_fm_prep                           false
% 19.86/2.99  --sat_fm_uc_incr                        true
% 19.86/2.99  --sat_out_model                         small
% 19.86/2.99  --sat_out_clauses                       false
% 19.86/2.99  
% 19.86/2.99  ------ QBF Options
% 19.86/2.99  
% 19.86/2.99  --qbf_mode                              false
% 19.86/2.99  --qbf_elim_univ                         false
% 19.86/2.99  --qbf_dom_inst                          none
% 19.86/2.99  --qbf_dom_pre_inst                      false
% 19.86/2.99  --qbf_sk_in                             false
% 19.86/2.99  --qbf_pred_elim                         true
% 19.86/2.99  --qbf_split                             512
% 19.86/2.99  
% 19.86/2.99  ------ BMC1 Options
% 19.86/2.99  
% 19.86/2.99  --bmc1_incremental                      false
% 19.86/2.99  --bmc1_axioms                           reachable_all
% 19.86/2.99  --bmc1_min_bound                        0
% 19.86/2.99  --bmc1_max_bound                        -1
% 19.86/2.99  --bmc1_max_bound_default                -1
% 19.86/2.99  --bmc1_symbol_reachability              true
% 19.86/2.99  --bmc1_property_lemmas                  false
% 19.86/2.99  --bmc1_k_induction                      false
% 19.86/2.99  --bmc1_non_equiv_states                 false
% 19.86/2.99  --bmc1_deadlock                         false
% 19.86/2.99  --bmc1_ucm                              false
% 19.86/2.99  --bmc1_add_unsat_core                   none
% 19.86/2.99  --bmc1_unsat_core_children              false
% 19.86/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.86/2.99  --bmc1_out_stat                         full
% 19.86/2.99  --bmc1_ground_init                      false
% 19.86/2.99  --bmc1_pre_inst_next_state              false
% 19.86/2.99  --bmc1_pre_inst_state                   false
% 19.86/2.99  --bmc1_pre_inst_reach_state             false
% 19.86/2.99  --bmc1_out_unsat_core                   false
% 19.86/2.99  --bmc1_aig_witness_out                  false
% 19.86/2.99  --bmc1_verbose                          false
% 19.86/2.99  --bmc1_dump_clauses_tptp                false
% 19.86/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.86/2.99  --bmc1_dump_file                        -
% 19.86/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.86/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.86/2.99  --bmc1_ucm_extend_mode                  1
% 19.86/2.99  --bmc1_ucm_init_mode                    2
% 19.86/2.99  --bmc1_ucm_cone_mode                    none
% 19.86/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.86/2.99  --bmc1_ucm_relax_model                  4
% 19.86/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.86/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.86/2.99  --bmc1_ucm_layered_model                none
% 19.86/2.99  --bmc1_ucm_max_lemma_size               10
% 19.86/2.99  
% 19.86/2.99  ------ AIG Options
% 19.86/2.99  
% 19.86/2.99  --aig_mode                              false
% 19.86/2.99  
% 19.86/2.99  ------ Instantiation Options
% 19.86/2.99  
% 19.86/2.99  --instantiation_flag                    true
% 19.86/2.99  --inst_sos_flag                         false
% 19.86/2.99  --inst_sos_phase                        true
% 19.86/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.86/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.86/2.99  --inst_lit_sel_side                     num_symb
% 19.86/2.99  --inst_solver_per_active                1400
% 19.86/2.99  --inst_solver_calls_frac                1.
% 19.86/2.99  --inst_passive_queue_type               priority_queues
% 19.86/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.86/2.99  --inst_passive_queues_freq              [25;2]
% 19.86/2.99  --inst_dismatching                      true
% 19.86/2.99  --inst_eager_unprocessed_to_passive     true
% 19.86/2.99  --inst_prop_sim_given                   true
% 19.86/2.99  --inst_prop_sim_new                     false
% 19.86/2.99  --inst_subs_new                         false
% 19.86/2.99  --inst_eq_res_simp                      false
% 19.86/2.99  --inst_subs_given                       false
% 19.86/2.99  --inst_orphan_elimination               true
% 19.86/2.99  --inst_learning_loop_flag               true
% 19.86/2.99  --inst_learning_start                   3000
% 19.86/2.99  --inst_learning_factor                  2
% 19.86/2.99  --inst_start_prop_sim_after_learn       3
% 19.86/2.99  --inst_sel_renew                        solver
% 19.86/2.99  --inst_lit_activity_flag                true
% 19.86/2.99  --inst_restr_to_given                   false
% 19.86/2.99  --inst_activity_threshold               500
% 19.86/2.99  --inst_out_proof                        true
% 19.86/2.99  
% 19.86/2.99  ------ Resolution Options
% 19.86/2.99  
% 19.86/2.99  --resolution_flag                       true
% 19.86/2.99  --res_lit_sel                           adaptive
% 19.86/2.99  --res_lit_sel_side                      none
% 19.86/2.99  --res_ordering                          kbo
% 19.86/2.99  --res_to_prop_solver                    active
% 19.86/2.99  --res_prop_simpl_new                    false
% 19.86/2.99  --res_prop_simpl_given                  true
% 19.86/2.99  --res_passive_queue_type                priority_queues
% 19.86/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.86/2.99  --res_passive_queues_freq               [15;5]
% 19.86/2.99  --res_forward_subs                      full
% 19.86/2.99  --res_backward_subs                     full
% 19.86/2.99  --res_forward_subs_resolution           true
% 19.86/2.99  --res_backward_subs_resolution          true
% 19.86/2.99  --res_orphan_elimination                true
% 19.86/2.99  --res_time_limit                        2.
% 19.86/2.99  --res_out_proof                         true
% 19.86/2.99  
% 19.86/2.99  ------ Superposition Options
% 19.86/2.99  
% 19.86/2.99  --superposition_flag                    true
% 19.86/2.99  --sup_passive_queue_type                priority_queues
% 19.86/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.86/2.99  --sup_passive_queues_freq               [1;4]
% 19.86/2.99  --demod_completeness_check              fast
% 19.86/2.99  --demod_use_ground                      true
% 19.86/2.99  --sup_to_prop_solver                    passive
% 19.86/2.99  --sup_prop_simpl_new                    true
% 19.86/2.99  --sup_prop_simpl_given                  true
% 19.86/2.99  --sup_fun_splitting                     false
% 19.86/2.99  --sup_smt_interval                      50000
% 19.86/2.99  
% 19.86/2.99  ------ Superposition Simplification Setup
% 19.86/2.99  
% 19.86/2.99  --sup_indices_passive                   []
% 19.86/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.86/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/2.99  --sup_full_bw                           [BwDemod]
% 19.86/2.99  --sup_immed_triv                        [TrivRules]
% 19.86/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/2.99  --sup_immed_bw_main                     []
% 19.86/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.86/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/2.99  
% 19.86/2.99  ------ Combination Options
% 19.86/2.99  
% 19.86/2.99  --comb_res_mult                         3
% 19.86/2.99  --comb_sup_mult                         2
% 19.86/2.99  --comb_inst_mult                        10
% 19.86/2.99  
% 19.86/2.99  ------ Debug Options
% 19.86/2.99  
% 19.86/2.99  --dbg_backtrace                         false
% 19.86/2.99  --dbg_dump_prop_clauses                 false
% 19.86/2.99  --dbg_dump_prop_clauses_file            -
% 19.86/2.99  --dbg_out_stat                          false
% 19.86/2.99  ------ Parsing...
% 19.86/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.86/2.99  
% 19.86/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.86/2.99  
% 19.86/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.86/2.99  
% 19.86/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.86/2.99  ------ Proving...
% 19.86/2.99  ------ Problem Properties 
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  clauses                                 15
% 19.86/2.99  conjectures                             4
% 19.86/2.99  EPR                                     2
% 19.86/2.99  Horn                                    12
% 19.86/2.99  unary                                   5
% 19.86/2.99  binary                                  4
% 19.86/2.99  lits                                    32
% 19.86/2.99  lits eq                                 11
% 19.86/2.99  fd_pure                                 0
% 19.86/2.99  fd_pseudo                               0
% 19.86/2.99  fd_cond                                 0
% 19.86/2.99  fd_pseudo_cond                          5
% 19.86/2.99  AC symbols                              0
% 19.86/2.99  
% 19.86/2.99  ------ Input Options Time Limit: Unbounded
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  ------ 
% 19.86/2.99  Current options:
% 19.86/2.99  ------ 
% 19.86/2.99  
% 19.86/2.99  ------ Input Options
% 19.86/2.99  
% 19.86/2.99  --out_options                           all
% 19.86/2.99  --tptp_safe_out                         true
% 19.86/2.99  --problem_path                          ""
% 19.86/2.99  --include_path                          ""
% 19.86/2.99  --clausifier                            res/vclausify_rel
% 19.86/2.99  --clausifier_options                    --mode clausify
% 19.86/2.99  --stdin                                 false
% 19.86/2.99  --stats_out                             sel
% 19.86/2.99  
% 19.86/2.99  ------ General Options
% 19.86/2.99  
% 19.86/2.99  --fof                                   false
% 19.86/2.99  --time_out_real                         604.99
% 19.86/2.99  --time_out_virtual                      -1.
% 19.86/2.99  --symbol_type_check                     false
% 19.86/2.99  --clausify_out                          false
% 19.86/2.99  --sig_cnt_out                           false
% 19.86/2.99  --trig_cnt_out                          false
% 19.86/2.99  --trig_cnt_out_tolerance                1.
% 19.86/2.99  --trig_cnt_out_sk_spl                   false
% 19.86/2.99  --abstr_cl_out                          false
% 19.86/2.99  
% 19.86/2.99  ------ Global Options
% 19.86/2.99  
% 19.86/2.99  --schedule                              none
% 19.86/2.99  --add_important_lit                     false
% 19.86/2.99  --prop_solver_per_cl                    1000
% 19.86/2.99  --min_unsat_core                        false
% 19.86/2.99  --soft_assumptions                      false
% 19.86/2.99  --soft_lemma_size                       3
% 19.86/2.99  --prop_impl_unit_size                   0
% 19.86/2.99  --prop_impl_unit                        []
% 19.86/2.99  --share_sel_clauses                     true
% 19.86/2.99  --reset_solvers                         false
% 19.86/2.99  --bc_imp_inh                            [conj_cone]
% 19.86/2.99  --conj_cone_tolerance                   3.
% 19.86/2.99  --extra_neg_conj                        none
% 19.86/2.99  --large_theory_mode                     true
% 19.86/2.99  --prolific_symb_bound                   200
% 19.86/2.99  --lt_threshold                          2000
% 19.86/2.99  --clause_weak_htbl                      true
% 19.86/2.99  --gc_record_bc_elim                     false
% 19.86/2.99  
% 19.86/2.99  ------ Preprocessing Options
% 19.86/2.99  
% 19.86/2.99  --preprocessing_flag                    true
% 19.86/2.99  --time_out_prep_mult                    0.1
% 19.86/2.99  --splitting_mode                        input
% 19.86/2.99  --splitting_grd                         true
% 19.86/2.99  --splitting_cvd                         false
% 19.86/2.99  --splitting_cvd_svl                     false
% 19.86/2.99  --splitting_nvd                         32
% 19.86/2.99  --sub_typing                            true
% 19.86/2.99  --prep_gs_sim                           false
% 19.86/2.99  --prep_unflatten                        true
% 19.86/2.99  --prep_res_sim                          true
% 19.86/2.99  --prep_upred                            true
% 19.86/2.99  --prep_sem_filter                       exhaustive
% 19.86/2.99  --prep_sem_filter_out                   false
% 19.86/2.99  --pred_elim                             false
% 19.86/2.99  --res_sim_input                         true
% 19.86/2.99  --eq_ax_congr_red                       true
% 19.86/2.99  --pure_diseq_elim                       true
% 19.86/2.99  --brand_transform                       false
% 19.86/2.99  --non_eq_to_eq                          false
% 19.86/2.99  --prep_def_merge                        true
% 19.86/2.99  --prep_def_merge_prop_impl              false
% 19.86/2.99  --prep_def_merge_mbd                    true
% 19.86/2.99  --prep_def_merge_tr_red                 false
% 19.86/2.99  --prep_def_merge_tr_cl                  false
% 19.86/2.99  --smt_preprocessing                     true
% 19.86/2.99  --smt_ac_axioms                         fast
% 19.86/2.99  --preprocessed_out                      false
% 19.86/2.99  --preprocessed_stats                    false
% 19.86/2.99  
% 19.86/2.99  ------ Abstraction refinement Options
% 19.86/2.99  
% 19.86/2.99  --abstr_ref                             []
% 19.86/2.99  --abstr_ref_prep                        false
% 19.86/2.99  --abstr_ref_until_sat                   false
% 19.86/2.99  --abstr_ref_sig_restrict                funpre
% 19.86/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.86/2.99  --abstr_ref_under                       []
% 19.86/2.99  
% 19.86/2.99  ------ SAT Options
% 19.86/2.99  
% 19.86/2.99  --sat_mode                              false
% 19.86/2.99  --sat_fm_restart_options                ""
% 19.86/2.99  --sat_gr_def                            false
% 19.86/2.99  --sat_epr_types                         true
% 19.86/2.99  --sat_non_cyclic_types                  false
% 19.86/2.99  --sat_finite_models                     false
% 19.86/2.99  --sat_fm_lemmas                         false
% 19.86/2.99  --sat_fm_prep                           false
% 19.86/2.99  --sat_fm_uc_incr                        true
% 19.86/2.99  --sat_out_model                         small
% 19.86/2.99  --sat_out_clauses                       false
% 19.86/2.99  
% 19.86/2.99  ------ QBF Options
% 19.86/2.99  
% 19.86/2.99  --qbf_mode                              false
% 19.86/2.99  --qbf_elim_univ                         false
% 19.86/2.99  --qbf_dom_inst                          none
% 19.86/2.99  --qbf_dom_pre_inst                      false
% 19.86/2.99  --qbf_sk_in                             false
% 19.86/2.99  --qbf_pred_elim                         true
% 19.86/2.99  --qbf_split                             512
% 19.86/2.99  
% 19.86/2.99  ------ BMC1 Options
% 19.86/2.99  
% 19.86/2.99  --bmc1_incremental                      false
% 19.86/2.99  --bmc1_axioms                           reachable_all
% 19.86/2.99  --bmc1_min_bound                        0
% 19.86/2.99  --bmc1_max_bound                        -1
% 19.86/2.99  --bmc1_max_bound_default                -1
% 19.86/2.99  --bmc1_symbol_reachability              true
% 19.86/2.99  --bmc1_property_lemmas                  false
% 19.86/2.99  --bmc1_k_induction                      false
% 19.86/2.99  --bmc1_non_equiv_states                 false
% 19.86/2.99  --bmc1_deadlock                         false
% 19.86/2.99  --bmc1_ucm                              false
% 19.86/2.99  --bmc1_add_unsat_core                   none
% 19.86/2.99  --bmc1_unsat_core_children              false
% 19.86/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.86/2.99  --bmc1_out_stat                         full
% 19.86/2.99  --bmc1_ground_init                      false
% 19.86/2.99  --bmc1_pre_inst_next_state              false
% 19.86/2.99  --bmc1_pre_inst_state                   false
% 19.86/2.99  --bmc1_pre_inst_reach_state             false
% 19.86/2.99  --bmc1_out_unsat_core                   false
% 19.86/2.99  --bmc1_aig_witness_out                  false
% 19.86/2.99  --bmc1_verbose                          false
% 19.86/2.99  --bmc1_dump_clauses_tptp                false
% 19.86/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.86/2.99  --bmc1_dump_file                        -
% 19.86/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.86/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.86/2.99  --bmc1_ucm_extend_mode                  1
% 19.86/2.99  --bmc1_ucm_init_mode                    2
% 19.86/2.99  --bmc1_ucm_cone_mode                    none
% 19.86/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.86/2.99  --bmc1_ucm_relax_model                  4
% 19.86/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.86/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.86/2.99  --bmc1_ucm_layered_model                none
% 19.86/2.99  --bmc1_ucm_max_lemma_size               10
% 19.86/2.99  
% 19.86/2.99  ------ AIG Options
% 19.86/2.99  
% 19.86/2.99  --aig_mode                              false
% 19.86/2.99  
% 19.86/2.99  ------ Instantiation Options
% 19.86/2.99  
% 19.86/2.99  --instantiation_flag                    true
% 19.86/2.99  --inst_sos_flag                         false
% 19.86/2.99  --inst_sos_phase                        true
% 19.86/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.86/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.86/2.99  --inst_lit_sel_side                     num_symb
% 19.86/2.99  --inst_solver_per_active                1400
% 19.86/2.99  --inst_solver_calls_frac                1.
% 19.86/2.99  --inst_passive_queue_type               priority_queues
% 19.86/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.86/2.99  --inst_passive_queues_freq              [25;2]
% 19.86/2.99  --inst_dismatching                      true
% 19.86/2.99  --inst_eager_unprocessed_to_passive     true
% 19.86/2.99  --inst_prop_sim_given                   true
% 19.86/2.99  --inst_prop_sim_new                     false
% 19.86/2.99  --inst_subs_new                         false
% 19.86/2.99  --inst_eq_res_simp                      false
% 19.86/2.99  --inst_subs_given                       false
% 19.86/2.99  --inst_orphan_elimination               true
% 19.86/2.99  --inst_learning_loop_flag               true
% 19.86/2.99  --inst_learning_start                   3000
% 19.86/2.99  --inst_learning_factor                  2
% 19.86/2.99  --inst_start_prop_sim_after_learn       3
% 19.86/2.99  --inst_sel_renew                        solver
% 19.86/2.99  --inst_lit_activity_flag                true
% 19.86/2.99  --inst_restr_to_given                   false
% 19.86/2.99  --inst_activity_threshold               500
% 19.86/2.99  --inst_out_proof                        true
% 19.86/2.99  
% 19.86/2.99  ------ Resolution Options
% 19.86/2.99  
% 19.86/2.99  --resolution_flag                       true
% 19.86/2.99  --res_lit_sel                           adaptive
% 19.86/2.99  --res_lit_sel_side                      none
% 19.86/2.99  --res_ordering                          kbo
% 19.86/2.99  --res_to_prop_solver                    active
% 19.86/2.99  --res_prop_simpl_new                    false
% 19.86/2.99  --res_prop_simpl_given                  true
% 19.86/2.99  --res_passive_queue_type                priority_queues
% 19.86/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.86/2.99  --res_passive_queues_freq               [15;5]
% 19.86/2.99  --res_forward_subs                      full
% 19.86/2.99  --res_backward_subs                     full
% 19.86/2.99  --res_forward_subs_resolution           true
% 19.86/2.99  --res_backward_subs_resolution          true
% 19.86/2.99  --res_orphan_elimination                true
% 19.86/2.99  --res_time_limit                        2.
% 19.86/2.99  --res_out_proof                         true
% 19.86/2.99  
% 19.86/2.99  ------ Superposition Options
% 19.86/2.99  
% 19.86/2.99  --superposition_flag                    true
% 19.86/2.99  --sup_passive_queue_type                priority_queues
% 19.86/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.86/2.99  --sup_passive_queues_freq               [1;4]
% 19.86/2.99  --demod_completeness_check              fast
% 19.86/2.99  --demod_use_ground                      true
% 19.86/2.99  --sup_to_prop_solver                    passive
% 19.86/2.99  --sup_prop_simpl_new                    true
% 19.86/2.99  --sup_prop_simpl_given                  true
% 19.86/2.99  --sup_fun_splitting                     false
% 19.86/2.99  --sup_smt_interval                      50000
% 19.86/2.99  
% 19.86/2.99  ------ Superposition Simplification Setup
% 19.86/2.99  
% 19.86/2.99  --sup_indices_passive                   []
% 19.86/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.86/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/2.99  --sup_full_bw                           [BwDemod]
% 19.86/2.99  --sup_immed_triv                        [TrivRules]
% 19.86/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/2.99  --sup_immed_bw_main                     []
% 19.86/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.86/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/2.99  
% 19.86/2.99  ------ Combination Options
% 19.86/2.99  
% 19.86/2.99  --comb_res_mult                         3
% 19.86/2.99  --comb_sup_mult                         2
% 19.86/2.99  --comb_inst_mult                        10
% 19.86/2.99  
% 19.86/2.99  ------ Debug Options
% 19.86/2.99  
% 19.86/2.99  --dbg_backtrace                         false
% 19.86/2.99  --dbg_dump_prop_clauses                 false
% 19.86/2.99  --dbg_dump_prop_clauses_file            -
% 19.86/2.99  --dbg_out_stat                          false
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  ------ Proving...
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  % SZS status Theorem for theBenchmark.p
% 19.86/2.99  
% 19.86/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.86/2.99  
% 19.86/2.99  fof(f1,axiom,(
% 19.86/2.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f13,plain,(
% 19.86/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/2.99    inference(nnf_transformation,[],[f1])).
% 19.86/2.99  
% 19.86/2.99  fof(f14,plain,(
% 19.86/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/2.99    inference(flattening,[],[f13])).
% 19.86/2.99  
% 19.86/2.99  fof(f15,plain,(
% 19.86/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/2.99    inference(rectify,[],[f14])).
% 19.86/2.99  
% 19.86/2.99  fof(f16,plain,(
% 19.86/2.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.86/2.99    introduced(choice_axiom,[])).
% 19.86/2.99  
% 19.86/2.99  fof(f17,plain,(
% 19.86/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.86/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 19.86/2.99  
% 19.86/2.99  fof(f27,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f17])).
% 19.86/2.99  
% 19.86/2.99  fof(f3,axiom,(
% 19.86/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f31,plain,(
% 19.86/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.86/2.99    inference(cnf_transformation,[],[f3])).
% 19.86/2.99  
% 19.86/2.99  fof(f47,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.86/2.99    inference(definition_unfolding,[],[f27,f31])).
% 19.86/2.99  
% 19.86/2.99  fof(f8,conjecture,(
% 19.86/2.99    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f9,negated_conjecture,(
% 19.86/2.99    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 19.86/2.99    inference(negated_conjecture,[],[f8])).
% 19.86/2.99  
% 19.86/2.99  fof(f11,plain,(
% 19.86/2.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 19.86/2.99    inference(ennf_transformation,[],[f9])).
% 19.86/2.99  
% 19.86/2.99  fof(f12,plain,(
% 19.86/2.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 19.86/2.99    inference(flattening,[],[f11])).
% 19.86/2.99  
% 19.86/2.99  fof(f22,plain,(
% 19.86/2.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3))),
% 19.86/2.99    introduced(choice_axiom,[])).
% 19.86/2.99  
% 19.86/2.99  fof(f23,plain,(
% 19.86/2.99    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3)),
% 19.86/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f22])).
% 19.86/2.99  
% 19.86/2.99  fof(f39,plain,(
% 19.86/2.99    r1_tarski(sK2,sK3)),
% 19.86/2.99    inference(cnf_transformation,[],[f23])).
% 19.86/2.99  
% 19.86/2.99  fof(f2,axiom,(
% 19.86/2.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f10,plain,(
% 19.86/2.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.86/2.99    inference(ennf_transformation,[],[f2])).
% 19.86/2.99  
% 19.86/2.99  fof(f30,plain,(
% 19.86/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f10])).
% 19.86/2.99  
% 19.86/2.99  fof(f51,plain,(
% 19.86/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.86/2.99    inference(definition_unfolding,[],[f30,f31])).
% 19.86/2.99  
% 19.86/2.99  fof(f25,plain,(
% 19.86/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 19.86/2.99    inference(cnf_transformation,[],[f17])).
% 19.86/2.99  
% 19.86/2.99  fof(f49,plain,(
% 19.86/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 19.86/2.99    inference(definition_unfolding,[],[f25,f31])).
% 19.86/2.99  
% 19.86/2.99  fof(f59,plain,(
% 19.86/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.86/2.99    inference(equality_resolution,[],[f49])).
% 19.86/2.99  
% 19.86/2.99  fof(f4,axiom,(
% 19.86/2.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f18,plain,(
% 19.86/2.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.86/2.99    inference(nnf_transformation,[],[f4])).
% 19.86/2.99  
% 19.86/2.99  fof(f19,plain,(
% 19.86/2.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.86/2.99    inference(rectify,[],[f18])).
% 19.86/2.99  
% 19.86/2.99  fof(f20,plain,(
% 19.86/2.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 19.86/2.99    introduced(choice_axiom,[])).
% 19.86/2.99  
% 19.86/2.99  fof(f21,plain,(
% 19.86/2.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.86/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 19.86/2.99  
% 19.86/2.99  fof(f32,plain,(
% 19.86/2.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.86/2.99    inference(cnf_transformation,[],[f21])).
% 19.86/2.99  
% 19.86/2.99  fof(f5,axiom,(
% 19.86/2.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f36,plain,(
% 19.86/2.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f5])).
% 19.86/2.99  
% 19.86/2.99  fof(f6,axiom,(
% 19.86/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f37,plain,(
% 19.86/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f6])).
% 19.86/2.99  
% 19.86/2.99  fof(f7,axiom,(
% 19.86/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.86/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/2.99  
% 19.86/2.99  fof(f38,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f7])).
% 19.86/2.99  
% 19.86/2.99  fof(f43,plain,(
% 19.86/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.86/2.99    inference(definition_unfolding,[],[f37,f38])).
% 19.86/2.99  
% 19.86/2.99  fof(f44,plain,(
% 19.86/2.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.86/2.99    inference(definition_unfolding,[],[f36,f43])).
% 19.86/2.99  
% 19.86/2.99  fof(f55,plain,(
% 19.86/2.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.86/2.99    inference(definition_unfolding,[],[f32,f44])).
% 19.86/2.99  
% 19.86/2.99  fof(f63,plain,(
% 19.86/2.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 19.86/2.99    inference(equality_resolution,[],[f55])).
% 19.86/2.99  
% 19.86/2.99  fof(f28,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f17])).
% 19.86/2.99  
% 19.86/2.99  fof(f46,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.86/2.99    inference(definition_unfolding,[],[f28,f31])).
% 19.86/2.99  
% 19.86/2.99  fof(f26,plain,(
% 19.86/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 19.86/2.99    inference(cnf_transformation,[],[f17])).
% 19.86/2.99  
% 19.86/2.99  fof(f48,plain,(
% 19.86/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 19.86/2.99    inference(definition_unfolding,[],[f26,f31])).
% 19.86/2.99  
% 19.86/2.99  fof(f58,plain,(
% 19.86/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 19.86/2.99    inference(equality_resolution,[],[f48])).
% 19.86/2.99  
% 19.86/2.99  fof(f40,plain,(
% 19.86/2.99    k3_xboole_0(sK3,sK4) = k1_tarski(sK5)),
% 19.86/2.99    inference(cnf_transformation,[],[f23])).
% 19.86/2.99  
% 19.86/2.99  fof(f57,plain,(
% 19.86/2.99    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)),
% 19.86/2.99    inference(definition_unfolding,[],[f40,f31,f44])).
% 19.86/2.99  
% 19.86/2.99  fof(f42,plain,(
% 19.86/2.99    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 19.86/2.99    inference(cnf_transformation,[],[f23])).
% 19.86/2.99  
% 19.86/2.99  fof(f56,plain,(
% 19.86/2.99    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5)),
% 19.86/2.99    inference(definition_unfolding,[],[f42,f31,f44])).
% 19.86/2.99  
% 19.86/2.99  fof(f33,plain,(
% 19.86/2.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.86/2.99    inference(cnf_transformation,[],[f21])).
% 19.86/2.99  
% 19.86/2.99  fof(f54,plain,(
% 19.86/2.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 19.86/2.99    inference(definition_unfolding,[],[f33,f44])).
% 19.86/2.99  
% 19.86/2.99  fof(f61,plain,(
% 19.86/2.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 19.86/2.99    inference(equality_resolution,[],[f54])).
% 19.86/2.99  
% 19.86/2.99  fof(f62,plain,(
% 19.86/2.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 19.86/2.99    inference(equality_resolution,[],[f61])).
% 19.86/2.99  
% 19.86/2.99  fof(f41,plain,(
% 19.86/2.99    r2_hidden(sK5,sK2)),
% 19.86/2.99    inference(cnf_transformation,[],[f23])).
% 19.86/2.99  
% 19.86/2.99  fof(f29,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.86/2.99    inference(cnf_transformation,[],[f17])).
% 19.86/2.99  
% 19.86/2.99  fof(f45,plain,(
% 19.86/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.86/2.99    inference(definition_unfolding,[],[f29,f31])).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2,plain,
% 19.86/2.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.86/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.86/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 19.86/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_346,plain,
% 19.86/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 19.86/2.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 19.86/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_14,negated_conjecture,
% 19.86/2.99      ( r1_tarski(sK2,sK3) ),
% 19.86/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_336,plain,
% 19.86/2.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_6,plain,
% 19.86/2.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.86/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_342,plain,
% 19.86/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 19.86/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_768,plain,
% 19.86/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_336,c_342]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_4,plain,
% 19.86/2.99      ( r2_hidden(X0,X1)
% 19.86/2.99      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 19.86/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_344,plain,
% 19.86/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.86/2.99      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1829,plain,
% 19.86/2.99      ( r2_hidden(X0,sK3) = iProver_top
% 19.86/2.99      | r2_hidden(X0,sK2) != iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_768,c_344]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2055,plain,
% 19.86/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = X1
% 19.86/2.99      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
% 19.86/2.99      | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_346,c_1829]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_10,plain,
% 19.86/2.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 19.86/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_338,plain,
% 19.86/2.99      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_3230,plain,
% 19.86/2.99      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,X1))
% 19.86/2.99      | sK0(sK2,X1,k2_enumset1(X0,X0,X0,X0)) = X0
% 19.86/2.99      | r2_hidden(sK0(sK2,X1,k2_enumset1(X0,X0,X0,X0)),sK3) = iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_2055,c_338]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1,plain,
% 19.86/2.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 19.86/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.86/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 19.86/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_347,plain,
% 19.86/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 19.86/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.86/2.99      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_3,plain,
% 19.86/2.99      ( ~ r2_hidden(X0,X1)
% 19.86/2.99      | ~ r2_hidden(X0,X2)
% 19.86/2.99      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 19.86/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_345,plain,
% 19.86/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.86/2.99      | r2_hidden(X0,X2) != iProver_top
% 19.86/2.99      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_13,negated_conjecture,
% 19.86/2.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.86/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_627,plain,
% 19.86/2.99      ( sK5 = X0
% 19.86/2.99      | r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) != iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_13,c_338]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1188,plain,
% 19.86/2.99      ( sK5 = X0
% 19.86/2.99      | r2_hidden(X0,sK3) != iProver_top
% 19.86/2.99      | r2_hidden(X0,sK4) != iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_345,c_627]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2287,plain,
% 19.86/2.99      ( sK0(X0,sK4,X1) = sK5
% 19.86/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,sK4)) = X1
% 19.86/2.99      | r2_hidden(sK0(X0,sK4,X1),X1) = iProver_top
% 19.86/2.99      | r2_hidden(sK0(X0,sK4,X1),sK3) != iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_347,c_1188]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_68162,plain,
% 19.86/2.99      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(X0,X0,X0,X0)) = X0
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(X0,X0,X0,X0)) = sK5
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 19.86/2.99      inference(superposition,[status(thm)],[c_3230,c_2287]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_68267,plain,
% 19.86/2.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_68162]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_126,plain,
% 19.86/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.86/2.99      theory(equality) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_479,plain,
% 19.86/2.99      ( r2_hidden(X0,X1)
% 19.86/2.99      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
% 19.86/2.99      | X0 != X2
% 19.86/2.99      | X1 != k2_enumset1(X2,X2,X2,X2) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_126]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_7685,plain,
% 19.86/2.99      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 19.86/2.99      | r2_hidden(X1,k2_enumset1(X2,X3,X4,X5))
% 19.86/2.99      | X1 != X0
% 19.86/2.99      | k2_enumset1(X2,X3,X4,X5) != k2_enumset1(X0,X0,X0,X0) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_479]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_55227,plain,
% 19.86/2.99      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(X0,X0,X0,X0)
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != X0 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_7685]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_55229,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_55227]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_11,negated_conjecture,
% 19.86/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.86/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2395,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
% 19.86/2.99      inference(resolution,[status(thm)],[c_1,c_11]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2687,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 19.86/2.99      inference(resolution,[status(thm)],[c_2395,c_10]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1051,plain,
% 19.86/2.99      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
% 19.86/2.99      | X1 != X0 ),
% 19.86/2.99      inference(resolution,[status(thm)],[c_126,c_13]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_9,plain,
% 19.86/2.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 19.86/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1083,plain,
% 19.86/2.99      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) | X0 != sK5 ),
% 19.86/2.99      inference(resolution,[status(thm)],[c_1051,c_9]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1210,plain,
% 19.86/2.99      ( r2_hidden(X0,sK4) | X0 != sK5 ),
% 19.86/2.99      inference(resolution,[status(thm)],[c_1083,c_4]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_3001,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
% 19.86/2.99      inference(forward_subsumption_resolution,
% 19.86/2.99                [status(thm)],
% 19.86/2.99                [c_2687,c_1210]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_3002,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) = iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_3001]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2457,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
% 19.86/2.99      inference(resolution,[status(thm)],[c_2,c_11]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_12,negated_conjecture,
% 19.86/2.99      ( r2_hidden(sK5,sK2) ),
% 19.86/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_123,plain,( X0 = X0 ),theory(equality) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_579,plain,
% 19.86/2.99      ( sK2 = sK2 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_123]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_484,plain,
% 19.86/2.99      ( r2_hidden(X0,X1) | ~ r2_hidden(sK5,sK2) | X0 != sK5 | X1 != sK2 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_126]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_578,plain,
% 19.86/2.99      ( r2_hidden(X0,sK2)
% 19.86/2.99      | ~ r2_hidden(sK5,sK2)
% 19.86/2.99      | X0 != sK5
% 19.86/2.99      | sK2 != sK2 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_484]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_719,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 19.86/2.99      | ~ r2_hidden(sK5,sK2)
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK5
% 19.86/2.99      | sK2 != sK2 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_578]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_1633,plain,
% 19.86/2.99      ( ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_10]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2692,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
% 19.86/2.99      inference(global_propositional_subsumption,
% 19.86/2.99                [status(thm)],
% 19.86/2.99                [c_2457,c_12,c_579,c_719,c_1633]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_2694,plain,
% 19.86/2.99      ( r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) = iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_2692]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_615,plain,
% 19.86/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_123]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_124,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_455,plain,
% 19.86/2.99      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 19.86/2.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != X0
% 19.86/2.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_124]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_614,plain,
% 19.86/2.99      ( k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))
% 19.86/2.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
% 19.86/2.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_455]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_0,plain,
% 19.86/2.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 19.86/2.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 19.86/2.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 19.86/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 19.86/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_522,plain,
% 19.86/2.99      ( ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 19.86/2.99      | ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
% 19.86/2.99      | ~ r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 19.86/2.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_0]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_523,plain,
% 19.86/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) != iProver_top
% 19.86/2.99      | r2_hidden(sK0(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
% 19.86/2.99      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_128,plain,
% 19.86/2.99      ( X0 != X1
% 19.86/2.99      | X2 != X3
% 19.86/2.99      | X4 != X5
% 19.86/2.99      | X6 != X7
% 19.86/2.99      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 19.86/2.99      theory(equality) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_132,plain,
% 19.86/2.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK5,sK5,sK5,sK5)
% 19.86/2.99      | sK5 != sK5 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_128]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_21,plain,
% 19.86/2.99      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(c_18,plain,
% 19.86/2.99      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 19.86/2.99      inference(instantiation,[status(thm)],[c_10]) ).
% 19.86/2.99  
% 19.86/2.99  cnf(contradiction,plain,
% 19.86/2.99      ( $false ),
% 19.86/2.99      inference(minisat,
% 19.86/2.99                [status(thm)],
% 19.86/2.99                [c_68267,c_55229,c_3002,c_3001,c_2694,c_2692,c_615,c_614,
% 19.86/2.99                 c_523,c_522,c_132,c_21,c_18,c_11]) ).
% 19.86/2.99  
% 19.86/2.99  
% 19.86/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.86/2.99  
% 19.86/2.99  ------                               Statistics
% 19.86/2.99  
% 19.86/2.99  ------ Selected
% 19.86/2.99  
% 19.86/2.99  total_time:                             2.276
% 19.86/2.99  
%------------------------------------------------------------------------------
