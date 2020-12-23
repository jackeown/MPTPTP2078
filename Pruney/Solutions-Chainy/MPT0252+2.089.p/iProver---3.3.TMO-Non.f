%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:35 EST 2020

% Result     : Timeout 59.91s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   81 ( 160 expanded)
%              Number of clauses        :   27 (  34 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  246 ( 524 expanded)
%              Number of equality atoms :  132 ( 341 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f66,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f23])).

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

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f83,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f84,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK2,sK4)
      & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r2_hidden(sK2,sK4)
    & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f35])).

fof(f61,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f79,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f80,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f79])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_159793,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_159873,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_159793])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_159791,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_159789,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,negated_conjecture,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_159786,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_159861,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_159789,c_159786])).

cnf(c_160016,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_159791,c_159861])).

cnf(c_11,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_159795,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_159933,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_159795])).

cnf(c_160088,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_160016,c_159933])).

cnf(c_160091,plain,
    ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_160088,c_159791])).

cnf(c_160573,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_159873,c_160091])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_159796,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_160735,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_159873,c_159796])).

cnf(c_273657,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_160573,c_160735])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_273657,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:40:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 59.91/7.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.91/7.99  
% 59.91/7.99  ------  iProver source info
% 59.91/7.99  
% 59.91/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.91/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.91/7.99  git: non_committed_changes: false
% 59.91/7.99  git: last_make_outside_of_git: false
% 59.91/7.99  
% 59.91/7.99  ------ 
% 59.91/7.99  ------ Parsing...
% 59.91/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  ------ Proving...
% 59.91/7.99  ------ Problem Properties 
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  clauses                                 19
% 59.91/7.99  conjectures                             2
% 59.91/7.99  EPR                                     3
% 59.91/7.99  Horn                                    16
% 59.91/7.99  unary                                   9
% 59.91/7.99  binary                                  3
% 59.91/7.99  lits                                    39
% 59.91/7.99  lits eq                                 18
% 59.91/7.99  fd_pure                                 0
% 59.91/7.99  fd_pseudo                               0
% 59.91/7.99  fd_cond                                 0
% 59.91/7.99  fd_pseudo_cond                          5
% 59.91/7.99  AC symbols                              0
% 59.91/7.99  
% 59.91/7.99  ------ Input Options Time Limit: Unbounded
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 59.91/7.99  Current options:
% 59.91/7.99  ------ 
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing...
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.91/7.99  
% 59.91/7.99  ------ Proving...
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  % SZS status Theorem for theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  fof(f9,axiom,(
% 59.91/7.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f54,plain,(
% 59.91/7.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f9])).
% 59.91/7.99  
% 59.91/7.99  fof(f10,axiom,(
% 59.91/7.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f55,plain,(
% 59.91/7.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f10])).
% 59.91/7.99  
% 59.91/7.99  fof(f11,axiom,(
% 59.91/7.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f56,plain,(
% 59.91/7.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f11])).
% 59.91/7.99  
% 59.91/7.99  fof(f12,axiom,(
% 59.91/7.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f57,plain,(
% 59.91/7.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f12])).
% 59.91/7.99  
% 59.91/7.99  fof(f63,plain,(
% 59.91/7.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 59.91/7.99    inference(definition_unfolding,[],[f56,f57])).
% 59.91/7.99  
% 59.91/7.99  fof(f64,plain,(
% 59.91/7.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 59.91/7.99    inference(definition_unfolding,[],[f55,f63])).
% 59.91/7.99  
% 59.91/7.99  fof(f66,plain,(
% 59.91/7.99    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 59.91/7.99    inference(definition_unfolding,[],[f54,f64])).
% 59.91/7.99  
% 59.91/7.99  fof(f4,axiom,(
% 59.91/7.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f23,plain,(
% 59.91/7.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 59.91/7.99    inference(ennf_transformation,[],[f4])).
% 59.91/7.99  
% 59.91/7.99  fof(f30,plain,(
% 59.91/7.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 59.91/7.99    inference(nnf_transformation,[],[f23])).
% 59.91/7.99  
% 59.91/7.99  fof(f31,plain,(
% 59.91/7.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 59.91/7.99    inference(flattening,[],[f30])).
% 59.91/7.99  
% 59.91/7.99  fof(f32,plain,(
% 59.91/7.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 59.91/7.99    inference(rectify,[],[f31])).
% 59.91/7.99  
% 59.91/7.99  fof(f33,plain,(
% 59.91/7.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 59.91/7.99    introduced(choice_axiom,[])).
% 59.91/7.99  
% 59.91/7.99  fof(f34,plain,(
% 59.91/7.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 59.91/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 59.91/7.99  
% 59.91/7.99  fof(f43,plain,(
% 59.91/7.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 59.91/7.99    inference(cnf_transformation,[],[f34])).
% 59.91/7.99  
% 59.91/7.99  fof(f74,plain,(
% 59.91/7.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 59.91/7.99    inference(definition_unfolding,[],[f43,f64])).
% 59.91/7.99  
% 59.91/7.99  fof(f83,plain,(
% 59.91/7.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3) )),
% 59.91/7.99    inference(equality_resolution,[],[f74])).
% 59.91/7.99  
% 59.91/7.99  fof(f84,plain,(
% 59.91/7.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2))) )),
% 59.91/7.99    inference(equality_resolution,[],[f83])).
% 59.91/7.99  
% 59.91/7.99  fof(f14,axiom,(
% 59.91/7.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f24,plain,(
% 59.91/7.99    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 59.91/7.99    inference(ennf_transformation,[],[f14])).
% 59.91/7.99  
% 59.91/7.99  fof(f59,plain,(
% 59.91/7.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f24])).
% 59.91/7.99  
% 59.91/7.99  fof(f16,conjecture,(
% 59.91/7.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f17,negated_conjecture,(
% 59.91/7.99    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 59.91/7.99    inference(negated_conjecture,[],[f16])).
% 59.91/7.99  
% 59.91/7.99  fof(f25,plain,(
% 59.91/7.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 59.91/7.99    inference(ennf_transformation,[],[f17])).
% 59.91/7.99  
% 59.91/7.99  fof(f35,plain,(
% 59.91/7.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4))),
% 59.91/7.99    introduced(choice_axiom,[])).
% 59.91/7.99  
% 59.91/7.99  fof(f36,plain,(
% 59.91/7.99    ~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 59.91/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f35])).
% 59.91/7.99  
% 59.91/7.99  fof(f61,plain,(
% 59.91/7.99    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 59.91/7.99    inference(cnf_transformation,[],[f36])).
% 59.91/7.99  
% 59.91/7.99  fof(f15,axiom,(
% 59.91/7.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f60,plain,(
% 59.91/7.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 59.91/7.99    inference(cnf_transformation,[],[f15])).
% 59.91/7.99  
% 59.91/7.99  fof(f78,plain,(
% 59.91/7.99    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4)),
% 59.91/7.99    inference(definition_unfolding,[],[f61,f60])).
% 59.91/7.99  
% 59.91/7.99  fof(f2,axiom,(
% 59.91/7.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f18,plain,(
% 59.91/7.99    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 59.91/7.99    inference(unused_predicate_definition_removal,[],[f2])).
% 59.91/7.99  
% 59.91/7.99  fof(f20,plain,(
% 59.91/7.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 59.91/7.99    inference(ennf_transformation,[],[f18])).
% 59.91/7.99  
% 59.91/7.99  fof(f21,plain,(
% 59.91/7.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 59.91/7.99    inference(flattening,[],[f20])).
% 59.91/7.99  
% 59.91/7.99  fof(f40,plain,(
% 59.91/7.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f21])).
% 59.91/7.99  
% 59.91/7.99  fof(f3,axiom,(
% 59.91/7.99    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f22,plain,(
% 59.91/7.99    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 59.91/7.99    inference(ennf_transformation,[],[f3])).
% 59.91/7.99  
% 59.91/7.99  fof(f41,plain,(
% 59.91/7.99    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f22])).
% 59.91/7.99  
% 59.91/7.99  fof(f45,plain,(
% 59.91/7.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 59.91/7.99    inference(cnf_transformation,[],[f34])).
% 59.91/7.99  
% 59.91/7.99  fof(f72,plain,(
% 59.91/7.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 59.91/7.99    inference(definition_unfolding,[],[f45,f64])).
% 59.91/7.99  
% 59.91/7.99  fof(f79,plain,(
% 59.91/7.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3) )),
% 59.91/7.99    inference(equality_resolution,[],[f72])).
% 59.91/7.99  
% 59.91/7.99  fof(f80,plain,(
% 59.91/7.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5))) )),
% 59.91/7.99    inference(equality_resolution,[],[f79])).
% 59.91/7.99  
% 59.91/7.99  fof(f1,axiom,(
% 59.91/7.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 59.91/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.91/7.99  
% 59.91/7.99  fof(f19,plain,(
% 59.91/7.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 59.91/7.99    inference(ennf_transformation,[],[f1])).
% 59.91/7.99  
% 59.91/7.99  fof(f26,plain,(
% 59.91/7.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 59.91/7.99    inference(nnf_transformation,[],[f19])).
% 59.91/7.99  
% 59.91/7.99  fof(f27,plain,(
% 59.91/7.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 59.91/7.99    inference(rectify,[],[f26])).
% 59.91/7.99  
% 59.91/7.99  fof(f28,plain,(
% 59.91/7.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 59.91/7.99    introduced(choice_axiom,[])).
% 59.91/7.99  
% 59.91/7.99  fof(f29,plain,(
% 59.91/7.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 59.91/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 59.91/7.99  
% 59.91/7.99  fof(f37,plain,(
% 59.91/7.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 59.91/7.99    inference(cnf_transformation,[],[f29])).
% 59.91/7.99  
% 59.91/7.99  fof(f62,plain,(
% 59.91/7.99    ~r2_hidden(sK2,sK4)),
% 59.91/7.99    inference(cnf_transformation,[],[f36])).
% 59.91/7.99  
% 59.91/7.99  cnf(c_0,plain,
% 59.91/7.99      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 59.91/7.99      inference(cnf_transformation,[],[f66]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_13,plain,
% 59.91/7.99      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
% 59.91/7.99      inference(cnf_transformation,[],[f84]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159793,plain,
% 59.91/7.99      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159873,plain,
% 59.91/7.99      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_0,c_159793]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_17,plain,
% 59.91/7.99      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 59.91/7.99      inference(cnf_transformation,[],[f59]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159791,plain,
% 59.91/7.99      ( r2_hidden(X0,X1) != iProver_top
% 59.91/7.99      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_19,negated_conjecture,
% 59.91/7.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
% 59.91/7.99      inference(cnf_transformation,[],[f78]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159789,plain,
% 59.91/7.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_5,plain,
% 59.91/7.99      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 59.91/7.99      inference(cnf_transformation,[],[f40]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_6,negated_conjecture,
% 59.91/7.99      ( ~ r2_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 59.91/7.99      inference(cnf_transformation,[],[f41]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_180,plain,
% 59.91/7.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 59.91/7.99      inference(resolution,[status(thm)],[c_5,c_6]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159786,plain,
% 59.91/7.99      ( X0 = X1
% 59.91/7.99      | r1_tarski(X0,X1) != iProver_top
% 59.91/7.99      | r1_tarski(X1,X0) != iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159861,plain,
% 59.91/7.99      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 59.91/7.99      | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_159789,c_159786]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_160016,plain,
% 59.91/7.99      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 59.91/7.99      | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_159791,c_159861]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_11,plain,
% 59.91/7.99      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
% 59.91/7.99      inference(cnf_transformation,[],[f80]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159795,plain,
% 59.91/7.99      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159933,plain,
% 59.91/7.99      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_0,c_159795]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_160088,plain,
% 59.91/7.99      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
% 59.91/7.99      inference(forward_subsumption_resolution,
% 59.91/7.99                [status(thm)],
% 59.91/7.99                [c_160016,c_159933]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_160091,plain,
% 59.91/7.99      ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
% 59.91/7.99      | r1_tarski(X0,sK4) = iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_160088,c_159791]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_160573,plain,
% 59.91/7.99      ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_159873,c_160091]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_4,plain,
% 59.91/7.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 59.91/7.99      inference(cnf_transformation,[],[f37]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_159796,plain,
% 59.91/7.99      ( r2_hidden(X0,X1) != iProver_top
% 59.91/7.99      | r2_hidden(X0,X2) = iProver_top
% 59.91/7.99      | r1_tarski(X1,X2) != iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_160735,plain,
% 59.91/7.99      ( r2_hidden(X0,X1) = iProver_top
% 59.91/7.99      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_159873,c_159796]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_273657,plain,
% 59.91/7.99      ( r2_hidden(sK2,sK4) = iProver_top ),
% 59.91/7.99      inference(superposition,[status(thm)],[c_160573,c_160735]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_18,negated_conjecture,
% 59.91/7.99      ( ~ r2_hidden(sK2,sK4) ),
% 59.91/7.99      inference(cnf_transformation,[],[f62]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(c_21,plain,
% 59.91/7.99      ( r2_hidden(sK2,sK4) != iProver_top ),
% 59.91/7.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.91/7.99  
% 59.91/7.99  cnf(contradiction,plain,
% 59.91/7.99      ( $false ),
% 59.91/7.99      inference(minisat,[status(thm)],[c_273657,c_21]) ).
% 59.91/7.99  
% 59.91/7.99  
% 59.91/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.91/7.99  
% 59.91/7.99  ------                               Statistics
% 59.91/7.99  
% 59.91/7.99  ------ Selected
% 59.91/7.99  
% 59.91/7.99  total_time:                             7.467
% 59.91/7.99  
%------------------------------------------------------------------------------
