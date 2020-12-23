%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:54 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 417 expanded)
%              Number of clauses        :   61 ( 119 expanded)
%              Number of leaves         :   12 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  355 (1895 expanded)
%              Number of equality atoms :  168 ( 718 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f15])).

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

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK2,sK4)
        | ~ r1_tarski(k2_tarski(sK2,sK3),sK4) )
      & ( ( r2_hidden(sK3,sK4)
          & r2_hidden(sK2,sK4) )
        | r1_tarski(k2_tarski(sK2,sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK2,sK4)
      | ~ r1_tarski(k2_tarski(sK2,sK3),sK4) )
    & ( ( r2_hidden(sK3,sK4)
        & r2_hidden(sK2,sK4) )
      | r1_tarski(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f38])).

fof(f66,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | ~ r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(definition_unfolding,[],[f66,f59])).

fof(f65,plain,
    ( r2_hidden(sK3,sK4)
    | r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,
    ( r2_hidden(sK3,sK4)
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f75,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f74])).

fof(f64,plain,
    ( r2_hidden(sK2,sK4)
    | r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,
    ( r2_hidden(sK2,sK4)
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f77,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f76])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1087,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1070,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1081,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2403,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_1081])).

cnf(c_3288,plain,
    ( k2_xboole_0(k1_tarski(sK0(X0,X1)),X0) = X0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_2403])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK3,sK4)
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1066,plain,
    ( r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9206,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK2,sK2,sK3),sK4)),k1_enumset1(sK2,sK2,sK3)) = k1_enumset1(sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3288,c_1066])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1065,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1934,plain,
    ( k2_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = sK4
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_1081])).

cnf(c_27,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1321,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_enumset1(X2,X3,X0))
    | ~ r1_tarski(k1_enumset1(X2,X3,X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1725,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3))
    | r2_hidden(sK3,sK4)
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1726,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1725])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1920,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1921,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_1956,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1934,c_27,c_1726,c_1921])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1064,plain,
    ( r2_hidden(sK2,sK4) = iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1935,plain,
    ( k2_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = sK4
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1081])).

cnf(c_26,plain,
    ( r2_hidden(sK2,sK4) = iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1326,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_enumset1(X2,X0,X3))
    | ~ r1_tarski(k1_enumset1(X2,X0,X3),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1749,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3))
    | r2_hidden(sK2,sK4)
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1750,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1923,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1924,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1923])).

cnf(c_2090,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1935,c_26,c_1750,c_1924])).

cnf(c_9513,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK2,sK2,sK3),sK4)),k1_enumset1(sK2,sK2,sK3)) = k1_enumset1(sK2,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9206,c_26,c_27,c_1726,c_1750,c_1921,c_1924])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1080,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1069,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2304,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_1069])).

cnf(c_9529,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9513,c_2304])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1071,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9589,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK3),sK4) = sK2
    | sK0(k1_enumset1(sK2,sK2,sK3),sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_9529,c_1071])).

cnf(c_1958,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1956])).

cnf(c_2092,plain,
    ( r2_hidden(sK2,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2090])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1700,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(X0,X1,X2),X3),X3)
    | r1_tarski(k1_enumset1(X0,X1,X2),X3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5988,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_539,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12698,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_542,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2599,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(X2,X3,X4),X5),X5)
    | X5 != X1
    | sK0(k1_enumset1(X2,X3,X4),X5) != X0 ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_12617,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
    | sK0(k1_enumset1(sK2,sK2,sK3),sK4) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_26290,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
    | sK0(k1_enumset1(sK2,sK2,sK3),sK4) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_12617])).

cnf(c_26292,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
    | ~ r2_hidden(sK2,sK4)
    | sK0(k1_enumset1(sK2,sK2,sK3),sK4) != sK2
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_26290])).

cnf(c_30821,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK3),sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9589,c_23,c_1958,c_2092,c_5988,c_12698,c_26292])).

cnf(c_1088,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_31178,plain,
    ( r2_hidden(sK3,sK4) != iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_30821,c_1088])).

cnf(c_28,plain,
    ( r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31178,c_2090,c_1956,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.36/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.36/1.50  
% 7.36/1.50  ------  iProver source info
% 7.36/1.50  
% 7.36/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.36/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.36/1.50  git: non_committed_changes: false
% 7.36/1.50  git: last_make_outside_of_git: false
% 7.36/1.50  
% 7.36/1.50  ------ 
% 7.36/1.50  
% 7.36/1.50  ------ Input Options
% 7.36/1.50  
% 7.36/1.50  --out_options                           all
% 7.36/1.50  --tptp_safe_out                         true
% 7.36/1.50  --problem_path                          ""
% 7.36/1.50  --include_path                          ""
% 7.36/1.50  --clausifier                            res/vclausify_rel
% 7.36/1.50  --clausifier_options                    --mode clausify
% 7.36/1.50  --stdin                                 false
% 7.36/1.50  --stats_out                             all
% 7.36/1.50  
% 7.36/1.50  ------ General Options
% 7.36/1.50  
% 7.36/1.50  --fof                                   false
% 7.36/1.50  --time_out_real                         305.
% 7.36/1.50  --time_out_virtual                      -1.
% 7.36/1.50  --symbol_type_check                     false
% 7.36/1.50  --clausify_out                          false
% 7.36/1.50  --sig_cnt_out                           false
% 7.36/1.50  --trig_cnt_out                          false
% 7.36/1.50  --trig_cnt_out_tolerance                1.
% 7.36/1.50  --trig_cnt_out_sk_spl                   false
% 7.36/1.50  --abstr_cl_out                          false
% 7.36/1.50  
% 7.36/1.50  ------ Global Options
% 7.36/1.50  
% 7.36/1.50  --schedule                              default
% 7.36/1.50  --add_important_lit                     false
% 7.36/1.50  --prop_solver_per_cl                    1000
% 7.36/1.50  --min_unsat_core                        false
% 7.36/1.50  --soft_assumptions                      false
% 7.36/1.50  --soft_lemma_size                       3
% 7.36/1.50  --prop_impl_unit_size                   0
% 7.36/1.50  --prop_impl_unit                        []
% 7.36/1.50  --share_sel_clauses                     true
% 7.36/1.50  --reset_solvers                         false
% 7.36/1.50  --bc_imp_inh                            [conj_cone]
% 7.36/1.50  --conj_cone_tolerance                   3.
% 7.36/1.50  --extra_neg_conj                        none
% 7.36/1.50  --large_theory_mode                     true
% 7.36/1.50  --prolific_symb_bound                   200
% 7.36/1.50  --lt_threshold                          2000
% 7.36/1.50  --clause_weak_htbl                      true
% 7.36/1.50  --gc_record_bc_elim                     false
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing Options
% 7.36/1.50  
% 7.36/1.50  --preprocessing_flag                    true
% 7.36/1.50  --time_out_prep_mult                    0.1
% 7.36/1.50  --splitting_mode                        input
% 7.36/1.50  --splitting_grd                         true
% 7.36/1.50  --splitting_cvd                         false
% 7.36/1.50  --splitting_cvd_svl                     false
% 7.36/1.50  --splitting_nvd                         32
% 7.36/1.50  --sub_typing                            true
% 7.36/1.50  --prep_gs_sim                           true
% 7.36/1.50  --prep_unflatten                        true
% 7.36/1.50  --prep_res_sim                          true
% 7.36/1.50  --prep_upred                            true
% 7.36/1.50  --prep_sem_filter                       exhaustive
% 7.36/1.50  --prep_sem_filter_out                   false
% 7.36/1.50  --pred_elim                             true
% 7.36/1.50  --res_sim_input                         true
% 7.36/1.50  --eq_ax_congr_red                       true
% 7.36/1.50  --pure_diseq_elim                       true
% 7.36/1.50  --brand_transform                       false
% 7.36/1.50  --non_eq_to_eq                          false
% 7.36/1.50  --prep_def_merge                        true
% 7.36/1.50  --prep_def_merge_prop_impl              false
% 7.36/1.50  --prep_def_merge_mbd                    true
% 7.36/1.50  --prep_def_merge_tr_red                 false
% 7.36/1.50  --prep_def_merge_tr_cl                  false
% 7.36/1.50  --smt_preprocessing                     true
% 7.36/1.50  --smt_ac_axioms                         fast
% 7.36/1.50  --preprocessed_out                      false
% 7.36/1.50  --preprocessed_stats                    false
% 7.36/1.50  
% 7.36/1.50  ------ Abstraction refinement Options
% 7.36/1.50  
% 7.36/1.50  --abstr_ref                             []
% 7.36/1.50  --abstr_ref_prep                        false
% 7.36/1.50  --abstr_ref_until_sat                   false
% 7.36/1.50  --abstr_ref_sig_restrict                funpre
% 7.36/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.50  --abstr_ref_under                       []
% 7.36/1.50  
% 7.36/1.50  ------ SAT Options
% 7.36/1.50  
% 7.36/1.50  --sat_mode                              false
% 7.36/1.50  --sat_fm_restart_options                ""
% 7.36/1.50  --sat_gr_def                            false
% 7.36/1.50  --sat_epr_types                         true
% 7.36/1.50  --sat_non_cyclic_types                  false
% 7.36/1.50  --sat_finite_models                     false
% 7.36/1.50  --sat_fm_lemmas                         false
% 7.36/1.50  --sat_fm_prep                           false
% 7.36/1.50  --sat_fm_uc_incr                        true
% 7.36/1.50  --sat_out_model                         small
% 7.36/1.50  --sat_out_clauses                       false
% 7.36/1.50  
% 7.36/1.50  ------ QBF Options
% 7.36/1.50  
% 7.36/1.50  --qbf_mode                              false
% 7.36/1.50  --qbf_elim_univ                         false
% 7.36/1.50  --qbf_dom_inst                          none
% 7.36/1.50  --qbf_dom_pre_inst                      false
% 7.36/1.50  --qbf_sk_in                             false
% 7.36/1.50  --qbf_pred_elim                         true
% 7.36/1.50  --qbf_split                             512
% 7.36/1.50  
% 7.36/1.50  ------ BMC1 Options
% 7.36/1.50  
% 7.36/1.50  --bmc1_incremental                      false
% 7.36/1.50  --bmc1_axioms                           reachable_all
% 7.36/1.50  --bmc1_min_bound                        0
% 7.36/1.50  --bmc1_max_bound                        -1
% 7.36/1.50  --bmc1_max_bound_default                -1
% 7.36/1.50  --bmc1_symbol_reachability              true
% 7.36/1.50  --bmc1_property_lemmas                  false
% 7.36/1.50  --bmc1_k_induction                      false
% 7.36/1.50  --bmc1_non_equiv_states                 false
% 7.36/1.50  --bmc1_deadlock                         false
% 7.36/1.50  --bmc1_ucm                              false
% 7.36/1.50  --bmc1_add_unsat_core                   none
% 7.36/1.50  --bmc1_unsat_core_children              false
% 7.36/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.50  --bmc1_out_stat                         full
% 7.36/1.50  --bmc1_ground_init                      false
% 7.36/1.50  --bmc1_pre_inst_next_state              false
% 7.36/1.50  --bmc1_pre_inst_state                   false
% 7.36/1.50  --bmc1_pre_inst_reach_state             false
% 7.36/1.50  --bmc1_out_unsat_core                   false
% 7.36/1.50  --bmc1_aig_witness_out                  false
% 7.36/1.50  --bmc1_verbose                          false
% 7.36/1.50  --bmc1_dump_clauses_tptp                false
% 7.36/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.50  --bmc1_dump_file                        -
% 7.36/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.50  --bmc1_ucm_extend_mode                  1
% 7.36/1.50  --bmc1_ucm_init_mode                    2
% 7.36/1.50  --bmc1_ucm_cone_mode                    none
% 7.36/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.50  --bmc1_ucm_relax_model                  4
% 7.36/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.50  --bmc1_ucm_layered_model                none
% 7.36/1.50  --bmc1_ucm_max_lemma_size               10
% 7.36/1.50  
% 7.36/1.50  ------ AIG Options
% 7.36/1.50  
% 7.36/1.50  --aig_mode                              false
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation Options
% 7.36/1.50  
% 7.36/1.50  --instantiation_flag                    true
% 7.36/1.50  --inst_sos_flag                         false
% 7.36/1.50  --inst_sos_phase                        true
% 7.36/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel_side                     num_symb
% 7.36/1.50  --inst_solver_per_active                1400
% 7.36/1.50  --inst_solver_calls_frac                1.
% 7.36/1.50  --inst_passive_queue_type               priority_queues
% 7.36/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.50  --inst_passive_queues_freq              [25;2]
% 7.36/1.50  --inst_dismatching                      true
% 7.36/1.50  --inst_eager_unprocessed_to_passive     true
% 7.36/1.50  --inst_prop_sim_given                   true
% 7.36/1.50  --inst_prop_sim_new                     false
% 7.36/1.50  --inst_subs_new                         false
% 7.36/1.50  --inst_eq_res_simp                      false
% 7.36/1.50  --inst_subs_given                       false
% 7.36/1.50  --inst_orphan_elimination               true
% 7.36/1.50  --inst_learning_loop_flag               true
% 7.36/1.50  --inst_learning_start                   3000
% 7.36/1.50  --inst_learning_factor                  2
% 7.36/1.50  --inst_start_prop_sim_after_learn       3
% 7.36/1.50  --inst_sel_renew                        solver
% 7.36/1.50  --inst_lit_activity_flag                true
% 7.36/1.50  --inst_restr_to_given                   false
% 7.36/1.50  --inst_activity_threshold               500
% 7.36/1.50  --inst_out_proof                        true
% 7.36/1.50  
% 7.36/1.50  ------ Resolution Options
% 7.36/1.50  
% 7.36/1.50  --resolution_flag                       true
% 7.36/1.50  --res_lit_sel                           adaptive
% 7.36/1.50  --res_lit_sel_side                      none
% 7.36/1.50  --res_ordering                          kbo
% 7.36/1.50  --res_to_prop_solver                    active
% 7.36/1.50  --res_prop_simpl_new                    false
% 7.36/1.50  --res_prop_simpl_given                  true
% 7.36/1.50  --res_passive_queue_type                priority_queues
% 7.36/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.50  --res_passive_queues_freq               [15;5]
% 7.36/1.50  --res_forward_subs                      full
% 7.36/1.50  --res_backward_subs                     full
% 7.36/1.50  --res_forward_subs_resolution           true
% 7.36/1.50  --res_backward_subs_resolution          true
% 7.36/1.50  --res_orphan_elimination                true
% 7.36/1.50  --res_time_limit                        2.
% 7.36/1.50  --res_out_proof                         true
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Options
% 7.36/1.50  
% 7.36/1.50  --superposition_flag                    true
% 7.36/1.50  --sup_passive_queue_type                priority_queues
% 7.36/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.50  --demod_completeness_check              fast
% 7.36/1.50  --demod_use_ground                      true
% 7.36/1.50  --sup_to_prop_solver                    passive
% 7.36/1.50  --sup_prop_simpl_new                    true
% 7.36/1.50  --sup_prop_simpl_given                  true
% 7.36/1.50  --sup_fun_splitting                     false
% 7.36/1.50  --sup_smt_interval                      50000
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Simplification Setup
% 7.36/1.50  
% 7.36/1.50  --sup_indices_passive                   []
% 7.36/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.50  --sup_full_bw                           [BwDemod]
% 7.36/1.50  --sup_immed_triv                        [TrivRules]
% 7.36/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.50  --sup_immed_bw_main                     []
% 7.36/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.50  
% 7.36/1.50  ------ Combination Options
% 7.36/1.50  
% 7.36/1.50  --comb_res_mult                         3
% 7.36/1.50  --comb_sup_mult                         2
% 7.36/1.50  --comb_inst_mult                        10
% 7.36/1.50  
% 7.36/1.50  ------ Debug Options
% 7.36/1.50  
% 7.36/1.50  --dbg_backtrace                         false
% 7.36/1.50  --dbg_dump_prop_clauses                 false
% 7.36/1.50  --dbg_dump_prop_clauses_file            -
% 7.36/1.50  --dbg_out_stat                          false
% 7.36/1.50  ------ Parsing...
% 7.36/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.36/1.50  ------ Proving...
% 7.36/1.50  ------ Problem Properties 
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  clauses                                 25
% 7.36/1.50  conjectures                             3
% 7.36/1.50  EPR                                     3
% 7.36/1.50  Horn                                    19
% 7.36/1.50  unary                                   6
% 7.36/1.50  binary                                  9
% 7.36/1.50  lits                                    57
% 7.36/1.50  lits eq                                 17
% 7.36/1.50  fd_pure                                 0
% 7.36/1.50  fd_pseudo                               0
% 7.36/1.50  fd_cond                                 0
% 7.36/1.50  fd_pseudo_cond                          6
% 7.36/1.50  AC symbols                              0
% 7.36/1.50  
% 7.36/1.50  ------ Schedule dynamic 5 is on 
% 7.36/1.50  
% 7.36/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  ------ 
% 7.36/1.50  Current options:
% 7.36/1.50  ------ 
% 7.36/1.50  
% 7.36/1.50  ------ Input Options
% 7.36/1.50  
% 7.36/1.50  --out_options                           all
% 7.36/1.50  --tptp_safe_out                         true
% 7.36/1.50  --problem_path                          ""
% 7.36/1.50  --include_path                          ""
% 7.36/1.50  --clausifier                            res/vclausify_rel
% 7.36/1.50  --clausifier_options                    --mode clausify
% 7.36/1.50  --stdin                                 false
% 7.36/1.50  --stats_out                             all
% 7.36/1.50  
% 7.36/1.50  ------ General Options
% 7.36/1.50  
% 7.36/1.50  --fof                                   false
% 7.36/1.50  --time_out_real                         305.
% 7.36/1.50  --time_out_virtual                      -1.
% 7.36/1.50  --symbol_type_check                     false
% 7.36/1.50  --clausify_out                          false
% 7.36/1.50  --sig_cnt_out                           false
% 7.36/1.50  --trig_cnt_out                          false
% 7.36/1.50  --trig_cnt_out_tolerance                1.
% 7.36/1.50  --trig_cnt_out_sk_spl                   false
% 7.36/1.50  --abstr_cl_out                          false
% 7.36/1.50  
% 7.36/1.50  ------ Global Options
% 7.36/1.50  
% 7.36/1.50  --schedule                              default
% 7.36/1.50  --add_important_lit                     false
% 7.36/1.50  --prop_solver_per_cl                    1000
% 7.36/1.50  --min_unsat_core                        false
% 7.36/1.50  --soft_assumptions                      false
% 7.36/1.50  --soft_lemma_size                       3
% 7.36/1.50  --prop_impl_unit_size                   0
% 7.36/1.50  --prop_impl_unit                        []
% 7.36/1.50  --share_sel_clauses                     true
% 7.36/1.50  --reset_solvers                         false
% 7.36/1.50  --bc_imp_inh                            [conj_cone]
% 7.36/1.50  --conj_cone_tolerance                   3.
% 7.36/1.50  --extra_neg_conj                        none
% 7.36/1.50  --large_theory_mode                     true
% 7.36/1.50  --prolific_symb_bound                   200
% 7.36/1.50  --lt_threshold                          2000
% 7.36/1.50  --clause_weak_htbl                      true
% 7.36/1.50  --gc_record_bc_elim                     false
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing Options
% 7.36/1.50  
% 7.36/1.50  --preprocessing_flag                    true
% 7.36/1.50  --time_out_prep_mult                    0.1
% 7.36/1.50  --splitting_mode                        input
% 7.36/1.50  --splitting_grd                         true
% 7.36/1.50  --splitting_cvd                         false
% 7.36/1.50  --splitting_cvd_svl                     false
% 7.36/1.50  --splitting_nvd                         32
% 7.36/1.50  --sub_typing                            true
% 7.36/1.50  --prep_gs_sim                           true
% 7.36/1.50  --prep_unflatten                        true
% 7.36/1.50  --prep_res_sim                          true
% 7.36/1.50  --prep_upred                            true
% 7.36/1.50  --prep_sem_filter                       exhaustive
% 7.36/1.50  --prep_sem_filter_out                   false
% 7.36/1.50  --pred_elim                             true
% 7.36/1.50  --res_sim_input                         true
% 7.36/1.50  --eq_ax_congr_red                       true
% 7.36/1.50  --pure_diseq_elim                       true
% 7.36/1.50  --brand_transform                       false
% 7.36/1.50  --non_eq_to_eq                          false
% 7.36/1.50  --prep_def_merge                        true
% 7.36/1.50  --prep_def_merge_prop_impl              false
% 7.36/1.50  --prep_def_merge_mbd                    true
% 7.36/1.50  --prep_def_merge_tr_red                 false
% 7.36/1.50  --prep_def_merge_tr_cl                  false
% 7.36/1.50  --smt_preprocessing                     true
% 7.36/1.50  --smt_ac_axioms                         fast
% 7.36/1.50  --preprocessed_out                      false
% 7.36/1.50  --preprocessed_stats                    false
% 7.36/1.50  
% 7.36/1.50  ------ Abstraction refinement Options
% 7.36/1.50  
% 7.36/1.50  --abstr_ref                             []
% 7.36/1.50  --abstr_ref_prep                        false
% 7.36/1.50  --abstr_ref_until_sat                   false
% 7.36/1.50  --abstr_ref_sig_restrict                funpre
% 7.36/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.50  --abstr_ref_under                       []
% 7.36/1.50  
% 7.36/1.50  ------ SAT Options
% 7.36/1.50  
% 7.36/1.50  --sat_mode                              false
% 7.36/1.50  --sat_fm_restart_options                ""
% 7.36/1.50  --sat_gr_def                            false
% 7.36/1.50  --sat_epr_types                         true
% 7.36/1.50  --sat_non_cyclic_types                  false
% 7.36/1.50  --sat_finite_models                     false
% 7.36/1.50  --sat_fm_lemmas                         false
% 7.36/1.50  --sat_fm_prep                           false
% 7.36/1.50  --sat_fm_uc_incr                        true
% 7.36/1.50  --sat_out_model                         small
% 7.36/1.50  --sat_out_clauses                       false
% 7.36/1.50  
% 7.36/1.50  ------ QBF Options
% 7.36/1.50  
% 7.36/1.50  --qbf_mode                              false
% 7.36/1.50  --qbf_elim_univ                         false
% 7.36/1.50  --qbf_dom_inst                          none
% 7.36/1.50  --qbf_dom_pre_inst                      false
% 7.36/1.50  --qbf_sk_in                             false
% 7.36/1.50  --qbf_pred_elim                         true
% 7.36/1.50  --qbf_split                             512
% 7.36/1.50  
% 7.36/1.50  ------ BMC1 Options
% 7.36/1.50  
% 7.36/1.50  --bmc1_incremental                      false
% 7.36/1.50  --bmc1_axioms                           reachable_all
% 7.36/1.50  --bmc1_min_bound                        0
% 7.36/1.50  --bmc1_max_bound                        -1
% 7.36/1.50  --bmc1_max_bound_default                -1
% 7.36/1.50  --bmc1_symbol_reachability              true
% 7.36/1.50  --bmc1_property_lemmas                  false
% 7.36/1.50  --bmc1_k_induction                      false
% 7.36/1.50  --bmc1_non_equiv_states                 false
% 7.36/1.50  --bmc1_deadlock                         false
% 7.36/1.50  --bmc1_ucm                              false
% 7.36/1.50  --bmc1_add_unsat_core                   none
% 7.36/1.50  --bmc1_unsat_core_children              false
% 7.36/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.50  --bmc1_out_stat                         full
% 7.36/1.50  --bmc1_ground_init                      false
% 7.36/1.50  --bmc1_pre_inst_next_state              false
% 7.36/1.50  --bmc1_pre_inst_state                   false
% 7.36/1.50  --bmc1_pre_inst_reach_state             false
% 7.36/1.50  --bmc1_out_unsat_core                   false
% 7.36/1.50  --bmc1_aig_witness_out                  false
% 7.36/1.50  --bmc1_verbose                          false
% 7.36/1.50  --bmc1_dump_clauses_tptp                false
% 7.36/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.50  --bmc1_dump_file                        -
% 7.36/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.50  --bmc1_ucm_extend_mode                  1
% 7.36/1.50  --bmc1_ucm_init_mode                    2
% 7.36/1.50  --bmc1_ucm_cone_mode                    none
% 7.36/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.50  --bmc1_ucm_relax_model                  4
% 7.36/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.50  --bmc1_ucm_layered_model                none
% 7.36/1.50  --bmc1_ucm_max_lemma_size               10
% 7.36/1.50  
% 7.36/1.50  ------ AIG Options
% 7.36/1.50  
% 7.36/1.50  --aig_mode                              false
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation Options
% 7.36/1.50  
% 7.36/1.50  --instantiation_flag                    true
% 7.36/1.50  --inst_sos_flag                         false
% 7.36/1.50  --inst_sos_phase                        true
% 7.36/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.50  --inst_lit_sel_side                     none
% 7.36/1.50  --inst_solver_per_active                1400
% 7.36/1.50  --inst_solver_calls_frac                1.
% 7.36/1.50  --inst_passive_queue_type               priority_queues
% 7.36/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.50  --inst_passive_queues_freq              [25;2]
% 7.36/1.50  --inst_dismatching                      true
% 7.36/1.50  --inst_eager_unprocessed_to_passive     true
% 7.36/1.50  --inst_prop_sim_given                   true
% 7.36/1.50  --inst_prop_sim_new                     false
% 7.36/1.50  --inst_subs_new                         false
% 7.36/1.50  --inst_eq_res_simp                      false
% 7.36/1.50  --inst_subs_given                       false
% 7.36/1.50  --inst_orphan_elimination               true
% 7.36/1.50  --inst_learning_loop_flag               true
% 7.36/1.50  --inst_learning_start                   3000
% 7.36/1.50  --inst_learning_factor                  2
% 7.36/1.50  --inst_start_prop_sim_after_learn       3
% 7.36/1.50  --inst_sel_renew                        solver
% 7.36/1.50  --inst_lit_activity_flag                true
% 7.36/1.50  --inst_restr_to_given                   false
% 7.36/1.50  --inst_activity_threshold               500
% 7.36/1.50  --inst_out_proof                        true
% 7.36/1.50  
% 7.36/1.50  ------ Resolution Options
% 7.36/1.50  
% 7.36/1.50  --resolution_flag                       false
% 7.36/1.50  --res_lit_sel                           adaptive
% 7.36/1.50  --res_lit_sel_side                      none
% 7.36/1.50  --res_ordering                          kbo
% 7.36/1.50  --res_to_prop_solver                    active
% 7.36/1.50  --res_prop_simpl_new                    false
% 7.36/1.50  --res_prop_simpl_given                  true
% 7.36/1.50  --res_passive_queue_type                priority_queues
% 7.36/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.50  --res_passive_queues_freq               [15;5]
% 7.36/1.50  --res_forward_subs                      full
% 7.36/1.50  --res_backward_subs                     full
% 7.36/1.50  --res_forward_subs_resolution           true
% 7.36/1.50  --res_backward_subs_resolution          true
% 7.36/1.50  --res_orphan_elimination                true
% 7.36/1.50  --res_time_limit                        2.
% 7.36/1.50  --res_out_proof                         true
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Options
% 7.36/1.50  
% 7.36/1.50  --superposition_flag                    true
% 7.36/1.50  --sup_passive_queue_type                priority_queues
% 7.36/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.50  --demod_completeness_check              fast
% 7.36/1.50  --demod_use_ground                      true
% 7.36/1.50  --sup_to_prop_solver                    passive
% 7.36/1.50  --sup_prop_simpl_new                    true
% 7.36/1.50  --sup_prop_simpl_given                  true
% 7.36/1.50  --sup_fun_splitting                     false
% 7.36/1.50  --sup_smt_interval                      50000
% 7.36/1.50  
% 7.36/1.50  ------ Superposition Simplification Setup
% 7.36/1.50  
% 7.36/1.50  --sup_indices_passive                   []
% 7.36/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.50  --sup_full_bw                           [BwDemod]
% 7.36/1.50  --sup_immed_triv                        [TrivRules]
% 7.36/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.50  --sup_immed_bw_main                     []
% 7.36/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.50  
% 7.36/1.50  ------ Combination Options
% 7.36/1.50  
% 7.36/1.50  --comb_res_mult                         3
% 7.36/1.50  --comb_sup_mult                         2
% 7.36/1.50  --comb_inst_mult                        10
% 7.36/1.50  
% 7.36/1.50  ------ Debug Options
% 7.36/1.50  
% 7.36/1.50  --dbg_backtrace                         false
% 7.36/1.50  --dbg_dump_prop_clauses                 false
% 7.36/1.50  --dbg_dump_prop_clauses_file            -
% 7.36/1.50  --dbg_out_stat                          false
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  ------ Proving...
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  % SZS status Theorem for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  fof(f1,axiom,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f15,plain,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.36/1.50    inference(ennf_transformation,[],[f1])).
% 7.36/1.50  
% 7.36/1.50  fof(f24,plain,(
% 7.36/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.36/1.50    inference(nnf_transformation,[],[f15])).
% 7.36/1.50  
% 7.36/1.50  fof(f25,plain,(
% 7.36/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.36/1.50    inference(rectify,[],[f24])).
% 7.36/1.50  
% 7.36/1.50  fof(f26,plain,(
% 7.36/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f27,plain,(
% 7.36/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.36/1.50  
% 7.36/1.50  fof(f41,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f27])).
% 7.36/1.50  
% 7.36/1.50  fof(f10,axiom,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f35,plain,(
% 7.36/1.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.36/1.50    inference(nnf_transformation,[],[f10])).
% 7.36/1.50  
% 7.36/1.50  fof(f61,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f35])).
% 7.36/1.50  
% 7.36/1.50  fof(f5,axiom,(
% 7.36/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f18,plain,(
% 7.36/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.36/1.50    inference(ennf_transformation,[],[f5])).
% 7.36/1.50  
% 7.36/1.50  fof(f48,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f18])).
% 7.36/1.50  
% 7.36/1.50  fof(f13,conjecture,(
% 7.36/1.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f14,negated_conjecture,(
% 7.36/1.50    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.36/1.50    inference(negated_conjecture,[],[f13])).
% 7.36/1.50  
% 7.36/1.50  fof(f23,plain,(
% 7.36/1.50    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.36/1.50    inference(ennf_transformation,[],[f14])).
% 7.36/1.50  
% 7.36/1.50  fof(f36,plain,(
% 7.36/1.50    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.36/1.50    inference(nnf_transformation,[],[f23])).
% 7.36/1.50  
% 7.36/1.50  fof(f37,plain,(
% 7.36/1.50    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.36/1.50    inference(flattening,[],[f36])).
% 7.36/1.50  
% 7.36/1.50  fof(f38,plain,(
% 7.36/1.50    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | ~r1_tarski(k2_tarski(sK2,sK3),sK4)) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | r1_tarski(k2_tarski(sK2,sK3),sK4)))),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f39,plain,(
% 7.36/1.50    (~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | ~r1_tarski(k2_tarski(sK2,sK3),sK4)) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | r1_tarski(k2_tarski(sK2,sK3),sK4))),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f38])).
% 7.36/1.50  
% 7.36/1.50  fof(f66,plain,(
% 7.36/1.50    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | ~r1_tarski(k2_tarski(sK2,sK3),sK4)),
% 7.36/1.50    inference(cnf_transformation,[],[f39])).
% 7.36/1.50  
% 7.36/1.50  fof(f9,axiom,(
% 7.36/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f59,plain,(
% 7.36/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f9])).
% 7.36/1.50  
% 7.36/1.50  fof(f69,plain,(
% 7.36/1.50    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | ~r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4)),
% 7.36/1.50    inference(definition_unfolding,[],[f66,f59])).
% 7.36/1.50  
% 7.36/1.50  fof(f65,plain,(
% 7.36/1.50    r2_hidden(sK3,sK4) | r1_tarski(k2_tarski(sK2,sK3),sK4)),
% 7.36/1.50    inference(cnf_transformation,[],[f39])).
% 7.36/1.50  
% 7.36/1.50  fof(f70,plain,(
% 7.36/1.50    r2_hidden(sK3,sK4) | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4)),
% 7.36/1.50    inference(definition_unfolding,[],[f65,f59])).
% 7.36/1.50  
% 7.36/1.50  fof(f40,plain,(
% 7.36/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f27])).
% 7.36/1.50  
% 7.36/1.50  fof(f8,axiom,(
% 7.36/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f21,plain,(
% 7.36/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.36/1.50    inference(ennf_transformation,[],[f8])).
% 7.36/1.50  
% 7.36/1.50  fof(f30,plain,(
% 7.36/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.36/1.50    inference(nnf_transformation,[],[f21])).
% 7.36/1.50  
% 7.36/1.50  fof(f31,plain,(
% 7.36/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.36/1.50    inference(flattening,[],[f30])).
% 7.36/1.50  
% 7.36/1.50  fof(f32,plain,(
% 7.36/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.36/1.50    inference(rectify,[],[f31])).
% 7.36/1.50  
% 7.36/1.50  fof(f33,plain,(
% 7.36/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.36/1.50    introduced(choice_axiom,[])).
% 7.36/1.50  
% 7.36/1.50  fof(f34,plain,(
% 7.36/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.36/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 7.36/1.50  
% 7.36/1.50  fof(f54,plain,(
% 7.36/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.36/1.50    inference(cnf_transformation,[],[f34])).
% 7.36/1.50  
% 7.36/1.50  fof(f74,plain,(
% 7.36/1.50    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 7.36/1.50    inference(equality_resolution,[],[f54])).
% 7.36/1.50  
% 7.36/1.50  fof(f75,plain,(
% 7.36/1.50    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 7.36/1.50    inference(equality_resolution,[],[f74])).
% 7.36/1.50  
% 7.36/1.50  fof(f64,plain,(
% 7.36/1.50    r2_hidden(sK2,sK4) | r1_tarski(k2_tarski(sK2,sK3),sK4)),
% 7.36/1.50    inference(cnf_transformation,[],[f39])).
% 7.36/1.50  
% 7.36/1.50  fof(f71,plain,(
% 7.36/1.50    r2_hidden(sK2,sK4) | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4)),
% 7.36/1.50    inference(definition_unfolding,[],[f64,f59])).
% 7.36/1.50  
% 7.36/1.50  fof(f53,plain,(
% 7.36/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.36/1.50    inference(cnf_transformation,[],[f34])).
% 7.36/1.50  
% 7.36/1.50  fof(f76,plain,(
% 7.36/1.50    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 7.36/1.50    inference(equality_resolution,[],[f53])).
% 7.36/1.50  
% 7.36/1.50  fof(f77,plain,(
% 7.36/1.50    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 7.36/1.50    inference(equality_resolution,[],[f76])).
% 7.36/1.50  
% 7.36/1.50  fof(f6,axiom,(
% 7.36/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.36/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.50  
% 7.36/1.50  fof(f49,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.36/1.50    inference(cnf_transformation,[],[f6])).
% 7.36/1.50  
% 7.36/1.50  fof(f60,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f35])).
% 7.36/1.50  
% 7.36/1.50  fof(f51,plain,(
% 7.36/1.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.36/1.50    inference(cnf_transformation,[],[f34])).
% 7.36/1.50  
% 7.36/1.50  fof(f80,plain,(
% 7.36/1.50    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 7.36/1.50    inference(equality_resolution,[],[f51])).
% 7.36/1.50  
% 7.36/1.50  fof(f42,plain,(
% 7.36/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.36/1.50    inference(cnf_transformation,[],[f27])).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1,plain,
% 7.36/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.36/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1087,plain,
% 7.36/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.36/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_19,plain,
% 7.36/1.50      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 7.36/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1070,plain,
% 7.36/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.50      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_8,plain,
% 7.36/1.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.36/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1081,plain,
% 7.36/1.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2403,plain,
% 7.36/1.50      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 7.36/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1070,c_1081]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_3288,plain,
% 7.36/1.50      ( k2_xboole_0(k1_tarski(sK0(X0,X1)),X0) = X0
% 7.36/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1087,c_2403]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_23,negated_conjecture,
% 7.36/1.50      ( ~ r2_hidden(sK2,sK4)
% 7.36/1.50      | ~ r2_hidden(sK3,sK4)
% 7.36/1.50      | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 7.36/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1066,plain,
% 7.36/1.50      ( r2_hidden(sK2,sK4) != iProver_top
% 7.36/1.50      | r2_hidden(sK3,sK4) != iProver_top
% 7.36/1.50      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_9206,plain,
% 7.36/1.50      ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK2,sK2,sK3),sK4)),k1_enumset1(sK2,sK2,sK3)) = k1_enumset1(sK2,sK2,sK3)
% 7.36/1.50      | r2_hidden(sK2,sK4) != iProver_top
% 7.36/1.50      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_3288,c_1066]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_24,negated_conjecture,
% 7.36/1.50      ( r2_hidden(sK3,sK4) | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 7.36/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1065,plain,
% 7.36/1.50      ( r2_hidden(sK3,sK4) = iProver_top
% 7.36/1.50      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1934,plain,
% 7.36/1.50      ( k2_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = sK4
% 7.36/1.50      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_1065,c_1081]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_27,plain,
% 7.36/1.50      ( r2_hidden(sK3,sK4) = iProver_top
% 7.36/1.50      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_2,plain,
% 7.36/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.36/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1321,plain,
% 7.36/1.50      ( r2_hidden(X0,X1)
% 7.36/1.50      | ~ r2_hidden(X0,k1_enumset1(X2,X3,X0))
% 7.36/1.50      | ~ r1_tarski(k1_enumset1(X2,X3,X0),X1) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1725,plain,
% 7.36/1.50      ( ~ r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3))
% 7.36/1.50      | r2_hidden(sK3,sK4)
% 7.36/1.50      | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_1321]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1726,plain,
% 7.36/1.50      ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 7.36/1.50      | r2_hidden(sK3,sK4) = iProver_top
% 7.36/1.50      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_1725]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_15,plain,
% 7.36/1.50      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 7.36/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1920,plain,
% 7.36/1.50      ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3)) ),
% 7.36/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1921,plain,
% 7.36/1.50      ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_1920]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1956,plain,
% 7.36/1.50      ( r2_hidden(sK3,sK4) = iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_1934,c_27,c_1726,c_1921]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_25,negated_conjecture,
% 7.36/1.50      ( r2_hidden(sK2,sK4) | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 7.36/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1064,plain,
% 7.36/1.50      ( r2_hidden(sK2,sK4) = iProver_top
% 7.36/1.50      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_1935,plain,
% 7.36/1.50      ( k2_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) = sK4
% 7.36/1.50      | r2_hidden(sK2,sK4) = iProver_top ),
% 7.36/1.51      inference(superposition,[status(thm)],[c_1064,c_1081]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_26,plain,
% 7.36/1.51      ( r2_hidden(sK2,sK4) = iProver_top
% 7.36/1.51      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1326,plain,
% 7.36/1.51      ( r2_hidden(X0,X1)
% 7.36/1.51      | ~ r2_hidden(X0,k1_enumset1(X2,X0,X3))
% 7.36/1.51      | ~ r1_tarski(k1_enumset1(X2,X0,X3),X1) ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1749,plain,
% 7.36/1.51      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3))
% 7.36/1.51      | r2_hidden(sK2,sK4)
% 7.36/1.51      | ~ r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_1326]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1750,plain,
% 7.36/1.51      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 7.36/1.51      | r2_hidden(sK2,sK4) = iProver_top
% 7.36/1.51      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_16,plain,
% 7.36/1.51      ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
% 7.36/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1923,plain,
% 7.36/1.51      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1924,plain,
% 7.36/1.51      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_1923]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_2090,plain,
% 7.36/1.51      ( r2_hidden(sK2,sK4) = iProver_top ),
% 7.36/1.51      inference(global_propositional_subsumption,
% 7.36/1.51                [status(thm)],
% 7.36/1.51                [c_1935,c_26,c_1750,c_1924]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_9513,plain,
% 7.36/1.51      ( k2_xboole_0(k1_tarski(sK0(k1_enumset1(sK2,sK2,sK3),sK4)),k1_enumset1(sK2,sK2,sK3)) = k1_enumset1(sK2,sK2,sK3) ),
% 7.36/1.51      inference(global_propositional_subsumption,
% 7.36/1.51                [status(thm)],
% 7.36/1.51                [c_9206,c_26,c_27,c_1726,c_1750,c_1921,c_1924]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_9,plain,
% 7.36/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.36/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1080,plain,
% 7.36/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_20,plain,
% 7.36/1.51      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 7.36/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1069,plain,
% 7.36/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.36/1.51      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_2304,plain,
% 7.36/1.51      ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) = iProver_top ),
% 7.36/1.51      inference(superposition,[status(thm)],[c_1080,c_1069]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_9529,plain,
% 7.36/1.51      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 7.36/1.51      inference(superposition,[status(thm)],[c_9513,c_2304]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_18,plain,
% 7.36/1.51      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 7.36/1.51      | X0 = X1
% 7.36/1.51      | X0 = X2
% 7.36/1.51      | X0 = X3 ),
% 7.36/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1071,plain,
% 7.36/1.51      ( X0 = X1
% 7.36/1.51      | X0 = X2
% 7.36/1.51      | X0 = X3
% 7.36/1.51      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_9589,plain,
% 7.36/1.51      ( sK0(k1_enumset1(sK2,sK2,sK3),sK4) = sK2
% 7.36/1.51      | sK0(k1_enumset1(sK2,sK2,sK3),sK4) = sK3 ),
% 7.36/1.51      inference(superposition,[status(thm)],[c_9529,c_1071]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1958,plain,
% 7.36/1.51      ( r2_hidden(sK3,sK4) ),
% 7.36/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_1956]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_2092,plain,
% 7.36/1.51      ( r2_hidden(sK2,sK4) ),
% 7.36/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_2090]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_0,plain,
% 7.36/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.36/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1700,plain,
% 7.36/1.51      ( ~ r2_hidden(sK0(k1_enumset1(X0,X1,X2),X3),X3)
% 7.36/1.51      | r1_tarski(k1_enumset1(X0,X1,X2),X3) ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_5988,plain,
% 7.36/1.51      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
% 7.36/1.51      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_539,plain,( X0 = X0 ),theory(equality) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_12698,plain,
% 7.36/1.51      ( sK4 = sK4 ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_539]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_542,plain,
% 7.36/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.36/1.51      theory(equality) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_2599,plain,
% 7.36/1.51      ( ~ r2_hidden(X0,X1)
% 7.36/1.51      | r2_hidden(sK0(k1_enumset1(X2,X3,X4),X5),X5)
% 7.36/1.51      | X5 != X1
% 7.36/1.51      | sK0(k1_enumset1(X2,X3,X4),X5) != X0 ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_542]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_12617,plain,
% 7.36/1.51      ( ~ r2_hidden(X0,X1)
% 7.36/1.51      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
% 7.36/1.51      | sK0(k1_enumset1(sK2,sK2,sK3),sK4) != X0
% 7.36/1.51      | sK4 != X1 ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_2599]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_26290,plain,
% 7.36/1.51      ( ~ r2_hidden(X0,sK4)
% 7.36/1.51      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
% 7.36/1.51      | sK0(k1_enumset1(sK2,sK2,sK3),sK4) != X0
% 7.36/1.51      | sK4 != sK4 ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_12617]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_26292,plain,
% 7.36/1.51      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),sK4),sK4)
% 7.36/1.51      | ~ r2_hidden(sK2,sK4)
% 7.36/1.51      | sK0(k1_enumset1(sK2,sK2,sK3),sK4) != sK2
% 7.36/1.51      | sK4 != sK4 ),
% 7.36/1.51      inference(instantiation,[status(thm)],[c_26290]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_30821,plain,
% 7.36/1.51      ( sK0(k1_enumset1(sK2,sK2,sK3),sK4) = sK3 ),
% 7.36/1.51      inference(global_propositional_subsumption,
% 7.36/1.51                [status(thm)],
% 7.36/1.51                [c_9589,c_23,c_1958,c_2092,c_5988,c_12698,c_26292]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_1088,plain,
% 7.36/1.51      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.36/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_31178,plain,
% 7.36/1.51      ( r2_hidden(sK3,sK4) != iProver_top
% 7.36/1.51      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) = iProver_top ),
% 7.36/1.51      inference(superposition,[status(thm)],[c_30821,c_1088]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(c_28,plain,
% 7.36/1.51      ( r2_hidden(sK2,sK4) != iProver_top
% 7.36/1.51      | r2_hidden(sK3,sK4) != iProver_top
% 7.36/1.51      | r1_tarski(k1_enumset1(sK2,sK2,sK3),sK4) != iProver_top ),
% 7.36/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.36/1.51  
% 7.36/1.51  cnf(contradiction,plain,
% 7.36/1.51      ( $false ),
% 7.36/1.51      inference(minisat,[status(thm)],[c_31178,c_2090,c_1956,c_28]) ).
% 7.36/1.51  
% 7.36/1.51  
% 7.36/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.36/1.51  
% 7.36/1.51  ------                               Statistics
% 7.36/1.51  
% 7.36/1.51  ------ General
% 7.36/1.51  
% 7.36/1.51  abstr_ref_over_cycles:                  0
% 7.36/1.51  abstr_ref_under_cycles:                 0
% 7.36/1.51  gc_basic_clause_elim:                   0
% 7.36/1.51  forced_gc_time:                         0
% 7.36/1.51  parsing_time:                           0.009
% 7.36/1.51  unif_index_cands_time:                  0.
% 7.36/1.51  unif_index_add_time:                    0.
% 7.36/1.51  orderings_time:                         0.
% 7.36/1.51  out_proof_time:                         0.015
% 7.36/1.51  total_time:                             0.848
% 7.36/1.51  num_of_symbols:                         41
% 7.36/1.51  num_of_terms:                           40094
% 7.36/1.51  
% 7.36/1.51  ------ Preprocessing
% 7.36/1.51  
% 7.36/1.51  num_of_splits:                          0
% 7.36/1.51  num_of_split_atoms:                     0
% 7.36/1.51  num_of_reused_defs:                     0
% 7.36/1.51  num_eq_ax_congr_red:                    27
% 7.36/1.51  num_of_sem_filtered_clauses:            1
% 7.36/1.51  num_of_subtypes:                        0
% 7.36/1.51  monotx_restored_types:                  0
% 7.36/1.51  sat_num_of_epr_types:                   0
% 7.36/1.51  sat_num_of_non_cyclic_types:            0
% 7.36/1.51  sat_guarded_non_collapsed_types:        0
% 7.36/1.51  num_pure_diseq_elim:                    0
% 7.36/1.51  simp_replaced_by:                       0
% 7.36/1.51  res_preprocessed:                       111
% 7.36/1.51  prep_upred:                             0
% 7.36/1.51  prep_unflattend:                        0
% 7.36/1.51  smt_new_axioms:                         0
% 7.36/1.51  pred_elim_cands:                        2
% 7.36/1.51  pred_elim:                              0
% 7.36/1.51  pred_elim_cl:                           0
% 7.36/1.51  pred_elim_cycles:                       2
% 7.36/1.51  merged_defs:                            8
% 7.36/1.51  merged_defs_ncl:                        0
% 7.36/1.51  bin_hyper_res:                          8
% 7.36/1.51  prep_cycles:                            4
% 7.36/1.51  pred_elim_time:                         0.
% 7.36/1.51  splitting_time:                         0.
% 7.36/1.51  sem_filter_time:                        0.
% 7.36/1.51  monotx_time:                            0.
% 7.36/1.51  subtype_inf_time:                       0.
% 7.36/1.51  
% 7.36/1.51  ------ Problem properties
% 7.36/1.51  
% 7.36/1.51  clauses:                                25
% 7.36/1.51  conjectures:                            3
% 7.36/1.51  epr:                                    3
% 7.36/1.51  horn:                                   19
% 7.36/1.51  ground:                                 3
% 7.36/1.51  unary:                                  6
% 7.36/1.51  binary:                                 9
% 7.36/1.51  lits:                                   57
% 7.36/1.51  lits_eq:                                17
% 7.36/1.51  fd_pure:                                0
% 7.36/1.51  fd_pseudo:                              0
% 7.36/1.51  fd_cond:                                0
% 7.36/1.51  fd_pseudo_cond:                         6
% 7.36/1.51  ac_symbols:                             0
% 7.36/1.51  
% 7.36/1.51  ------ Propositional Solver
% 7.36/1.51  
% 7.36/1.51  prop_solver_calls:                      29
% 7.36/1.51  prop_fast_solver_calls:                 831
% 7.36/1.51  smt_solver_calls:                       0
% 7.36/1.51  smt_fast_solver_calls:                  0
% 7.36/1.51  prop_num_of_clauses:                    11558
% 7.36/1.51  prop_preprocess_simplified:             24419
% 7.36/1.51  prop_fo_subsumed:                       5
% 7.36/1.51  prop_solver_time:                       0.
% 7.36/1.51  smt_solver_time:                        0.
% 7.36/1.51  smt_fast_solver_time:                   0.
% 7.36/1.51  prop_fast_solver_time:                  0.
% 7.36/1.51  prop_unsat_core_time:                   0.001
% 7.36/1.51  
% 7.36/1.51  ------ QBF
% 7.36/1.51  
% 7.36/1.51  qbf_q_res:                              0
% 7.36/1.51  qbf_num_tautologies:                    0
% 7.36/1.51  qbf_prep_cycles:                        0
% 7.36/1.51  
% 7.36/1.51  ------ BMC1
% 7.36/1.51  
% 7.36/1.51  bmc1_current_bound:                     -1
% 7.36/1.51  bmc1_last_solved_bound:                 -1
% 7.36/1.51  bmc1_unsat_core_size:                   -1
% 7.36/1.51  bmc1_unsat_core_parents_size:           -1
% 7.36/1.51  bmc1_merge_next_fun:                    0
% 7.36/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.36/1.51  
% 7.36/1.51  ------ Instantiation
% 7.36/1.51  
% 7.36/1.51  inst_num_of_clauses:                    2602
% 7.36/1.51  inst_num_in_passive:                    1510
% 7.36/1.51  inst_num_in_active:                     752
% 7.36/1.51  inst_num_in_unprocessed:                342
% 7.36/1.51  inst_num_of_loops:                      930
% 7.36/1.51  inst_num_of_learning_restarts:          0
% 7.36/1.51  inst_num_moves_active_passive:          177
% 7.36/1.51  inst_lit_activity:                      0
% 7.36/1.51  inst_lit_activity_moves:                0
% 7.36/1.51  inst_num_tautologies:                   0
% 7.36/1.51  inst_num_prop_implied:                  0
% 7.36/1.51  inst_num_existing_simplified:           0
% 7.36/1.51  inst_num_eq_res_simplified:             0
% 7.36/1.51  inst_num_child_elim:                    0
% 7.36/1.51  inst_num_of_dismatching_blockings:      2981
% 7.36/1.51  inst_num_of_non_proper_insts:           2107
% 7.36/1.51  inst_num_of_duplicates:                 0
% 7.36/1.51  inst_inst_num_from_inst_to_res:         0
% 7.36/1.51  inst_dismatching_checking_time:         0.
% 7.36/1.51  
% 7.36/1.51  ------ Resolution
% 7.36/1.51  
% 7.36/1.51  res_num_of_clauses:                     0
% 7.36/1.51  res_num_in_passive:                     0
% 7.36/1.51  res_num_in_active:                      0
% 7.36/1.51  res_num_of_loops:                       115
% 7.36/1.51  res_forward_subset_subsumed:            213
% 7.36/1.51  res_backward_subset_subsumed:           10
% 7.36/1.51  res_forward_subsumed:                   0
% 7.36/1.51  res_backward_subsumed:                  0
% 7.36/1.51  res_forward_subsumption_resolution:     0
% 7.36/1.51  res_backward_subsumption_resolution:    0
% 7.36/1.51  res_clause_to_clause_subsumption:       7802
% 7.36/1.51  res_orphan_elimination:                 0
% 7.36/1.51  res_tautology_del:                      50
% 7.36/1.51  res_num_eq_res_simplified:              0
% 7.36/1.51  res_num_sel_changes:                    0
% 7.36/1.51  res_moves_from_active_to_pass:          0
% 7.36/1.51  
% 7.36/1.51  ------ Superposition
% 7.36/1.51  
% 7.36/1.51  sup_time_total:                         0.
% 7.36/1.51  sup_time_generating:                    0.
% 7.36/1.51  sup_time_sim_full:                      0.
% 7.36/1.51  sup_time_sim_immed:                     0.
% 7.36/1.51  
% 7.36/1.51  sup_num_of_clauses:                     798
% 7.36/1.51  sup_num_in_active:                      126
% 7.36/1.51  sup_num_in_passive:                     672
% 7.36/1.51  sup_num_of_loops:                       185
% 7.36/1.51  sup_fw_superposition:                   1778
% 7.36/1.51  sup_bw_superposition:                   1122
% 7.36/1.51  sup_immediate_simplified:               808
% 7.36/1.51  sup_given_eliminated:                   0
% 7.36/1.51  comparisons_done:                       0
% 7.36/1.51  comparisons_avoided:                    9
% 7.36/1.51  
% 7.36/1.51  ------ Simplifications
% 7.36/1.51  
% 7.36/1.51  
% 7.36/1.51  sim_fw_subset_subsumed:                 77
% 7.36/1.51  sim_bw_subset_subsumed:                 2
% 7.36/1.51  sim_fw_subsumed:                        336
% 7.36/1.51  sim_bw_subsumed:                        1
% 7.36/1.51  sim_fw_subsumption_res:                 0
% 7.36/1.51  sim_bw_subsumption_res:                 0
% 7.36/1.51  sim_tautology_del:                      89
% 7.36/1.51  sim_eq_tautology_del:                   68
% 7.36/1.51  sim_eq_res_simp:                        0
% 7.36/1.51  sim_fw_demodulated:                     323
% 7.36/1.51  sim_bw_demodulated:                     58
% 7.36/1.51  sim_light_normalised:                   161
% 7.36/1.51  sim_joinable_taut:                      0
% 7.36/1.51  sim_joinable_simp:                      0
% 7.36/1.51  sim_ac_normalised:                      0
% 7.36/1.51  sim_smt_subsumption:                    0
% 7.36/1.51  
%------------------------------------------------------------------------------
