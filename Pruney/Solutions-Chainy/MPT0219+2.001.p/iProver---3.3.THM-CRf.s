%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:09 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 225 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 ( 655 expanded)
%              Number of equality atoms :  168 ( 545 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( sK1 != sK2
    & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33])).

fof(f63,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f71,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f83,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f63,f65,f71,f71,f71])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f55,f65,f62,f71])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f87,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f86])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f92,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f90,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f91,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

fof(f64,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1428,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_20,c_0])).

cnf(c_15,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_837,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_23200,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_837])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_919,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_920,plain,
    ( sK2 = X0
    | sK2 = X1
    | sK2 = X2
    | r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_922,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_645,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_888,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_889,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_17,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_25,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23200,c_922,c_889,c_25,c_22,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.44/1.46  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/1.46  
% 7.44/1.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.46  
% 7.44/1.46  ------  iProver source info
% 7.44/1.46  
% 7.44/1.46  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.46  git: non_committed_changes: false
% 7.44/1.46  git: last_make_outside_of_git: false
% 7.44/1.46  
% 7.44/1.46  ------ 
% 7.44/1.46  ------ Parsing...
% 7.44/1.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.46  
% 7.44/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.44/1.46  
% 7.44/1.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.46  
% 7.44/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.44/1.46  ------ Proving...
% 7.44/1.46  ------ Problem Properties 
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  clauses                                 20
% 7.44/1.46  conjectures                             2
% 7.44/1.46  EPR                                     3
% 7.44/1.46  Horn                                    18
% 7.44/1.46  unary                                   13
% 7.44/1.46  binary                                  1
% 7.44/1.46  lits                                    36
% 7.44/1.46  lits eq                                 24
% 7.44/1.46  fd_pure                                 0
% 7.44/1.46  fd_pseudo                               0
% 7.44/1.46  fd_cond                                 0
% 7.44/1.46  fd_pseudo_cond                          5
% 7.44/1.46  AC symbols                              1
% 7.44/1.46  
% 7.44/1.46  ------ Input Options Time Limit: Unbounded
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  ------ 
% 7.44/1.46  Current options:
% 7.44/1.46  ------ 
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  ------ Proving...
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  % SZS status Theorem for theBenchmark.p
% 7.44/1.46  
% 7.44/1.46  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.46  
% 7.44/1.46  fof(f20,conjecture,(
% 7.44/1.46    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f21,negated_conjecture,(
% 7.44/1.46    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.44/1.46    inference(negated_conjecture,[],[f20])).
% 7.44/1.46  
% 7.44/1.46  fof(f25,plain,(
% 7.44/1.46    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.44/1.46    inference(ennf_transformation,[],[f21])).
% 7.44/1.46  
% 7.44/1.46  fof(f33,plain,(
% 7.44/1.46    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 7.44/1.46    introduced(choice_axiom,[])).
% 7.44/1.46  
% 7.44/1.46  fof(f34,plain,(
% 7.44/1.46    sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.44/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33])).
% 7.44/1.46  
% 7.44/1.46  fof(f63,plain,(
% 7.44/1.46    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 7.44/1.46    inference(cnf_transformation,[],[f34])).
% 7.44/1.46  
% 7.44/1.46  fof(f9,axiom,(
% 7.44/1.46    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f45,plain,(
% 7.44/1.46    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f9])).
% 7.44/1.46  
% 7.44/1.46  fof(f5,axiom,(
% 7.44/1.46    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f41,plain,(
% 7.44/1.46    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f5])).
% 7.44/1.46  
% 7.44/1.46  fof(f65,plain,(
% 7.44/1.46    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f45,f41])).
% 7.44/1.46  
% 7.44/1.46  fof(f13,axiom,(
% 7.44/1.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f56,plain,(
% 7.44/1.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f13])).
% 7.44/1.46  
% 7.44/1.46  fof(f14,axiom,(
% 7.44/1.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f57,plain,(
% 7.44/1.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f14])).
% 7.44/1.46  
% 7.44/1.46  fof(f15,axiom,(
% 7.44/1.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f58,plain,(
% 7.44/1.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f15])).
% 7.44/1.46  
% 7.44/1.46  fof(f16,axiom,(
% 7.44/1.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f59,plain,(
% 7.44/1.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f16])).
% 7.44/1.46  
% 7.44/1.46  fof(f17,axiom,(
% 7.44/1.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f60,plain,(
% 7.44/1.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f17])).
% 7.44/1.46  
% 7.44/1.46  fof(f18,axiom,(
% 7.44/1.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f61,plain,(
% 7.44/1.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f18])).
% 7.44/1.46  
% 7.44/1.46  fof(f19,axiom,(
% 7.44/1.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f62,plain,(
% 7.44/1.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f19])).
% 7.44/1.46  
% 7.44/1.46  fof(f66,plain,(
% 7.44/1.46    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f61,f62])).
% 7.44/1.46  
% 7.44/1.46  fof(f67,plain,(
% 7.44/1.46    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f60,f66])).
% 7.44/1.46  
% 7.44/1.46  fof(f68,plain,(
% 7.44/1.46    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f59,f67])).
% 7.44/1.46  
% 7.44/1.46  fof(f69,plain,(
% 7.44/1.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f58,f68])).
% 7.44/1.46  
% 7.44/1.46  fof(f70,plain,(
% 7.44/1.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f57,f69])).
% 7.44/1.46  
% 7.44/1.46  fof(f71,plain,(
% 7.44/1.46    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f56,f70])).
% 7.44/1.46  
% 7.44/1.46  fof(f83,plain,(
% 7.44/1.46    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 7.44/1.46    inference(definition_unfolding,[],[f63,f65,f71,f71,f71])).
% 7.44/1.46  
% 7.44/1.46  fof(f12,axiom,(
% 7.44/1.46    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f55,plain,(
% 7.44/1.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.44/1.46    inference(cnf_transformation,[],[f12])).
% 7.44/1.46  
% 7.44/1.46  fof(f72,plain,(
% 7.44/1.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.44/1.46    inference(definition_unfolding,[],[f55,f65,f62,f71])).
% 7.44/1.46  
% 7.44/1.46  fof(f11,axiom,(
% 7.44/1.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.44/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.44/1.46  
% 7.44/1.46  fof(f24,plain,(
% 7.44/1.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.44/1.46    inference(ennf_transformation,[],[f11])).
% 7.44/1.46  
% 7.44/1.46  fof(f28,plain,(
% 7.44/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.44/1.46    inference(nnf_transformation,[],[f24])).
% 7.44/1.46  
% 7.44/1.46  fof(f29,plain,(
% 7.44/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.44/1.46    inference(flattening,[],[f28])).
% 7.44/1.46  
% 7.44/1.46  fof(f30,plain,(
% 7.44/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.44/1.46    inference(rectify,[],[f29])).
% 7.44/1.46  
% 7.44/1.46  fof(f31,plain,(
% 7.44/1.46    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.44/1.46    introduced(choice_axiom,[])).
% 7.44/1.46  
% 7.44/1.46  fof(f32,plain,(
% 7.44/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.44/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.44/1.46  
% 7.44/1.46  fof(f50,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.44/1.46    inference(cnf_transformation,[],[f32])).
% 7.44/1.46  
% 7.44/1.46  fof(f79,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.44/1.46    inference(definition_unfolding,[],[f50,f69])).
% 7.44/1.46  
% 7.44/1.46  fof(f86,plain,(
% 7.44/1.46    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 7.44/1.46    inference(equality_resolution,[],[f79])).
% 7.44/1.46  
% 7.44/1.46  fof(f87,plain,(
% 7.44/1.46    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 7.44/1.46    inference(equality_resolution,[],[f86])).
% 7.44/1.46  
% 7.44/1.46  fof(f47,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.44/1.46    inference(cnf_transformation,[],[f32])).
% 7.44/1.46  
% 7.44/1.46  fof(f82,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.44/1.46    inference(definition_unfolding,[],[f47,f69])).
% 7.44/1.46  
% 7.44/1.46  fof(f92,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 7.44/1.46    inference(equality_resolution,[],[f82])).
% 7.44/1.46  
% 7.44/1.46  fof(f48,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.44/1.46    inference(cnf_transformation,[],[f32])).
% 7.44/1.46  
% 7.44/1.46  fof(f81,plain,(
% 7.44/1.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.44/1.46    inference(definition_unfolding,[],[f48,f69])).
% 7.44/1.46  
% 7.44/1.46  fof(f90,plain,(
% 7.44/1.46    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.44/1.46    inference(equality_resolution,[],[f81])).
% 7.44/1.46  
% 7.44/1.46  fof(f91,plain,(
% 7.44/1.46    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 7.44/1.46    inference(equality_resolution,[],[f90])).
% 7.44/1.46  
% 7.44/1.46  fof(f64,plain,(
% 7.44/1.46    sK1 != sK2),
% 7.44/1.46    inference(cnf_transformation,[],[f34])).
% 7.44/1.46  
% 7.44/1.46  cnf(c_20,negated_conjecture,
% 7.44/1.46      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 7.44/1.46      inference(cnf_transformation,[],[f83]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_0,plain,
% 7.44/1.46      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 7.44/1.46      inference(cnf_transformation,[],[f72]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_1428,plain,
% 7.44/1.46      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 7.44/1.46      inference(superposition,[status(thm)],[c_20,c_0]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_15,plain,
% 7.44/1.46      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 7.44/1.46      inference(cnf_transformation,[],[f87]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_837,plain,
% 7.44/1.46      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 7.44/1.46      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_23200,plain,
% 7.44/1.46      ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.44/1.46      inference(superposition,[status(thm)],[c_1428,c_837]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_18,plain,
% 7.44/1.46      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 7.44/1.46      | X0 = X1
% 7.44/1.46      | X0 = X2
% 7.44/1.46      | X0 = X3 ),
% 7.44/1.46      inference(cnf_transformation,[],[f92]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_919,plain,
% 7.44/1.46      ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
% 7.44/1.46      | sK2 = X0
% 7.44/1.46      | sK2 = X1
% 7.44/1.46      | sK2 = X2 ),
% 7.44/1.46      inference(instantiation,[status(thm)],[c_18]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_920,plain,
% 7.44/1.46      ( sK2 = X0
% 7.44/1.46      | sK2 = X1
% 7.44/1.46      | sK2 = X2
% 7.44/1.46      | r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
% 7.44/1.46      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_922,plain,
% 7.44/1.46      ( sK2 = sK1
% 7.44/1.46      | r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 7.44/1.46      inference(instantiation,[status(thm)],[c_920]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_645,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_888,plain,
% 7.44/1.46      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 7.44/1.46      inference(instantiation,[status(thm)],[c_645]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_889,plain,
% 7.44/1.46      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 7.44/1.46      inference(instantiation,[status(thm)],[c_888]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_17,plain,
% 7.44/1.46      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 7.44/1.46      inference(cnf_transformation,[],[f91]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_25,plain,
% 7.44/1.46      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.44/1.46      inference(instantiation,[status(thm)],[c_17]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_22,plain,
% 7.44/1.46      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.44/1.46      | sK1 = sK1 ),
% 7.44/1.46      inference(instantiation,[status(thm)],[c_18]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(c_19,negated_conjecture,
% 7.44/1.46      ( sK1 != sK2 ),
% 7.44/1.46      inference(cnf_transformation,[],[f64]) ).
% 7.44/1.46  
% 7.44/1.46  cnf(contradiction,plain,
% 7.44/1.46      ( $false ),
% 7.44/1.46      inference(minisat,
% 7.44/1.46                [status(thm)],
% 7.44/1.46                [c_23200,c_922,c_889,c_25,c_22,c_19]) ).
% 7.44/1.46  
% 7.44/1.46  
% 7.44/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.46  
% 7.44/1.46  ------                               Statistics
% 7.44/1.46  
% 7.44/1.46  ------ Selected
% 7.44/1.46  
% 7.44/1.46  total_time:                             0.893
% 7.44/1.46  
%------------------------------------------------------------------------------
