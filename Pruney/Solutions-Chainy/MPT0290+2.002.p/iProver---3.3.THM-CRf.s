%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:46 EST 2020

% Result     : Theorem 20.06s
% Output     : CNFRefutation 20.06s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 161 expanded)
%              Number of clauses        :   38 (  43 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 ( 553 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f36,f36])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK3,sK4)),k3_xboole_0(k3_tarski(sK3),k3_tarski(sK4))) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK3,sK4)),k3_xboole_0(k3_tarski(sK3),k3_tarski(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f24])).

fof(f40,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK3,sK4)),k3_xboole_0(k3_tarski(sK3),k3_tarski(sK4))) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ~ r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
    inference(definition_unfolding,[],[f40,f36,f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23469,plain,
    ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_tarski(k3_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_57839,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
    | r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
    inference(instantiation,[status(thm)],[c_23469])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6008,plain,
    ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0)
    | ~ r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_14338,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
    | r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK3) ),
    inference(instantiation,[status(thm)],[c_6008])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_373,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_377,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1097,plain,
    ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = iProver_top
    | r1_tarski(k3_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_377])).

cnf(c_3890,plain,
    ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1097])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_372,plain,
    ( r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3973,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3890,c_372])).

cnf(c_4561,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3973])).

cnf(c_4564,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4561])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3395,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
    | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3397,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK3)
    | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_874,plain,
    ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
    | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2000,plain,
    ( r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
    | ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
    | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_2615,plain,
    ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
    | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(X0))
    | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2617,plain,
    ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
    | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3))
    | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_2615])).

cnf(c_823,plain,
    ( ~ r2_hidden(X0,sK4)
    | r1_tarski(X0,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2516,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4)
    | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_671,plain,
    ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
    | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4))
    | ~ r1_tarski(X0,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1703,plain,
    ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
    | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4))
    | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_504,plain,
    ( r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))
    | ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4))
    | ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_439,plain,
    ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))
    | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_440,plain,
    ( r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
    | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ r1_tarski(sK2(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_404,plain,
    ( ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))
    | r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57839,c_14338,c_4564,c_3397,c_2617,c_2516,c_1703,c_504,c_439,c_440,c_404,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 20.06/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.06/2.99  
% 20.06/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 20.06/2.99  
% 20.06/2.99  ------  iProver source info
% 20.06/2.99  
% 20.06/2.99  git: date: 2020-06-30 10:37:57 +0100
% 20.06/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 20.06/2.99  git: non_committed_changes: false
% 20.06/2.99  git: last_make_outside_of_git: false
% 20.06/2.99  
% 20.06/2.99  ------ 
% 20.06/2.99  
% 20.06/2.99  ------ Input Options
% 20.06/2.99  
% 20.06/2.99  --out_options                           all
% 20.06/2.99  --tptp_safe_out                         true
% 20.06/2.99  --problem_path                          ""
% 20.06/2.99  --include_path                          ""
% 20.06/2.99  --clausifier                            res/vclausify_rel
% 20.06/2.99  --clausifier_options                    ""
% 20.06/2.99  --stdin                                 false
% 20.06/2.99  --stats_out                             all
% 20.06/2.99  
% 20.06/2.99  ------ General Options
% 20.06/2.99  
% 20.06/2.99  --fof                                   false
% 20.06/2.99  --time_out_real                         305.
% 20.06/2.99  --time_out_virtual                      -1.
% 20.06/2.99  --symbol_type_check                     false
% 20.06/2.99  --clausify_out                          false
% 20.06/2.99  --sig_cnt_out                           false
% 20.06/2.99  --trig_cnt_out                          false
% 20.06/2.99  --trig_cnt_out_tolerance                1.
% 20.06/2.99  --trig_cnt_out_sk_spl                   false
% 20.06/2.99  --abstr_cl_out                          false
% 20.06/2.99  
% 20.06/2.99  ------ Global Options
% 20.06/2.99  
% 20.06/2.99  --schedule                              default
% 20.06/2.99  --add_important_lit                     false
% 20.06/2.99  --prop_solver_per_cl                    1000
% 20.06/2.99  --min_unsat_core                        false
% 20.06/2.99  --soft_assumptions                      false
% 20.06/2.99  --soft_lemma_size                       3
% 20.06/2.99  --prop_impl_unit_size                   0
% 20.06/2.99  --prop_impl_unit                        []
% 20.06/2.99  --share_sel_clauses                     true
% 20.06/2.99  --reset_solvers                         false
% 20.06/2.99  --bc_imp_inh                            [conj_cone]
% 20.06/2.99  --conj_cone_tolerance                   3.
% 20.06/2.99  --extra_neg_conj                        none
% 20.06/2.99  --large_theory_mode                     true
% 20.06/2.99  --prolific_symb_bound                   200
% 20.06/2.99  --lt_threshold                          2000
% 20.06/2.99  --clause_weak_htbl                      true
% 20.06/2.99  --gc_record_bc_elim                     false
% 20.06/2.99  
% 20.06/2.99  ------ Preprocessing Options
% 20.06/2.99  
% 20.06/2.99  --preprocessing_flag                    true
% 20.06/2.99  --time_out_prep_mult                    0.1
% 20.06/2.99  --splitting_mode                        input
% 20.06/2.99  --splitting_grd                         true
% 20.06/2.99  --splitting_cvd                         false
% 20.06/2.99  --splitting_cvd_svl                     false
% 20.06/2.99  --splitting_nvd                         32
% 20.06/2.99  --sub_typing                            true
% 20.06/2.99  --prep_gs_sim                           true
% 20.06/2.99  --prep_unflatten                        true
% 20.06/2.99  --prep_res_sim                          true
% 20.06/2.99  --prep_upred                            true
% 20.06/2.99  --prep_sem_filter                       exhaustive
% 20.06/2.99  --prep_sem_filter_out                   false
% 20.06/2.99  --pred_elim                             true
% 20.06/2.99  --res_sim_input                         true
% 20.06/2.99  --eq_ax_congr_red                       true
% 20.06/2.99  --pure_diseq_elim                       true
% 20.06/2.99  --brand_transform                       false
% 20.06/2.99  --non_eq_to_eq                          false
% 20.06/2.99  --prep_def_merge                        true
% 20.06/2.99  --prep_def_merge_prop_impl              false
% 20.06/2.99  --prep_def_merge_mbd                    true
% 20.06/2.99  --prep_def_merge_tr_red                 false
% 20.06/2.99  --prep_def_merge_tr_cl                  false
% 20.06/2.99  --smt_preprocessing                     true
% 20.06/2.99  --smt_ac_axioms                         fast
% 20.06/2.99  --preprocessed_out                      false
% 20.06/2.99  --preprocessed_stats                    false
% 20.06/2.99  
% 20.06/2.99  ------ Abstraction refinement Options
% 20.06/2.99  
% 20.06/2.99  --abstr_ref                             []
% 20.06/2.99  --abstr_ref_prep                        false
% 20.06/2.99  --abstr_ref_until_sat                   false
% 20.06/2.99  --abstr_ref_sig_restrict                funpre
% 20.06/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 20.06/2.99  --abstr_ref_under                       []
% 20.06/2.99  
% 20.06/2.99  ------ SAT Options
% 20.06/2.99  
% 20.06/2.99  --sat_mode                              false
% 20.06/2.99  --sat_fm_restart_options                ""
% 20.06/2.99  --sat_gr_def                            false
% 20.06/2.99  --sat_epr_types                         true
% 20.06/2.99  --sat_non_cyclic_types                  false
% 20.06/2.99  --sat_finite_models                     false
% 20.06/2.99  --sat_fm_lemmas                         false
% 20.06/2.99  --sat_fm_prep                           false
% 20.06/2.99  --sat_fm_uc_incr                        true
% 20.06/2.99  --sat_out_model                         small
% 20.06/2.99  --sat_out_clauses                       false
% 20.06/2.99  
% 20.06/2.99  ------ QBF Options
% 20.06/2.99  
% 20.06/2.99  --qbf_mode                              false
% 20.06/2.99  --qbf_elim_univ                         false
% 20.06/2.99  --qbf_dom_inst                          none
% 20.06/2.99  --qbf_dom_pre_inst                      false
% 20.06/2.99  --qbf_sk_in                             false
% 20.06/2.99  --qbf_pred_elim                         true
% 20.06/2.99  --qbf_split                             512
% 20.06/2.99  
% 20.06/2.99  ------ BMC1 Options
% 20.06/2.99  
% 20.06/2.99  --bmc1_incremental                      false
% 20.06/2.99  --bmc1_axioms                           reachable_all
% 20.06/2.99  --bmc1_min_bound                        0
% 20.06/2.99  --bmc1_max_bound                        -1
% 20.06/2.99  --bmc1_max_bound_default                -1
% 20.06/2.99  --bmc1_symbol_reachability              true
% 20.06/2.99  --bmc1_property_lemmas                  false
% 20.06/2.99  --bmc1_k_induction                      false
% 20.06/2.99  --bmc1_non_equiv_states                 false
% 20.06/2.99  --bmc1_deadlock                         false
% 20.06/2.99  --bmc1_ucm                              false
% 20.06/2.99  --bmc1_add_unsat_core                   none
% 20.06/2.99  --bmc1_unsat_core_children              false
% 20.06/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 20.06/2.99  --bmc1_out_stat                         full
% 20.06/2.99  --bmc1_ground_init                      false
% 20.06/2.99  --bmc1_pre_inst_next_state              false
% 20.06/2.99  --bmc1_pre_inst_state                   false
% 20.06/2.99  --bmc1_pre_inst_reach_state             false
% 20.06/2.99  --bmc1_out_unsat_core                   false
% 20.06/2.99  --bmc1_aig_witness_out                  false
% 20.06/2.99  --bmc1_verbose                          false
% 20.06/2.99  --bmc1_dump_clauses_tptp                false
% 20.06/2.99  --bmc1_dump_unsat_core_tptp             false
% 20.06/2.99  --bmc1_dump_file                        -
% 20.06/2.99  --bmc1_ucm_expand_uc_limit              128
% 20.06/2.99  --bmc1_ucm_n_expand_iterations          6
% 20.06/2.99  --bmc1_ucm_extend_mode                  1
% 20.06/2.99  --bmc1_ucm_init_mode                    2
% 20.06/2.99  --bmc1_ucm_cone_mode                    none
% 20.06/2.99  --bmc1_ucm_reduced_relation_type        0
% 20.06/2.99  --bmc1_ucm_relax_model                  4
% 20.06/2.99  --bmc1_ucm_full_tr_after_sat            true
% 20.06/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 20.06/2.99  --bmc1_ucm_layered_model                none
% 20.06/2.99  --bmc1_ucm_max_lemma_size               10
% 20.06/2.99  
% 20.06/2.99  ------ AIG Options
% 20.06/2.99  
% 20.06/2.99  --aig_mode                              false
% 20.06/2.99  
% 20.06/2.99  ------ Instantiation Options
% 20.06/2.99  
% 20.06/2.99  --instantiation_flag                    true
% 20.06/2.99  --inst_sos_flag                         true
% 20.06/2.99  --inst_sos_phase                        true
% 20.06/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.06/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.06/2.99  --inst_lit_sel_side                     num_symb
% 20.06/2.99  --inst_solver_per_active                1400
% 20.06/2.99  --inst_solver_calls_frac                1.
% 20.06/2.99  --inst_passive_queue_type               priority_queues
% 20.06/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.06/2.99  --inst_passive_queues_freq              [25;2]
% 20.06/2.99  --inst_dismatching                      true
% 20.06/2.99  --inst_eager_unprocessed_to_passive     true
% 20.06/2.99  --inst_prop_sim_given                   true
% 20.06/2.99  --inst_prop_sim_new                     false
% 20.06/2.99  --inst_subs_new                         false
% 20.06/2.99  --inst_eq_res_simp                      false
% 20.06/2.99  --inst_subs_given                       false
% 20.06/2.99  --inst_orphan_elimination               true
% 20.06/2.99  --inst_learning_loop_flag               true
% 20.06/2.99  --inst_learning_start                   3000
% 20.06/2.99  --inst_learning_factor                  2
% 20.06/2.99  --inst_start_prop_sim_after_learn       3
% 20.06/2.99  --inst_sel_renew                        solver
% 20.06/2.99  --inst_lit_activity_flag                true
% 20.06/2.99  --inst_restr_to_given                   false
% 20.06/2.99  --inst_activity_threshold               500
% 20.06/2.99  --inst_out_proof                        true
% 20.06/2.99  
% 20.06/2.99  ------ Resolution Options
% 20.06/2.99  
% 20.06/2.99  --resolution_flag                       true
% 20.06/2.99  --res_lit_sel                           adaptive
% 20.06/2.99  --res_lit_sel_side                      none
% 20.06/2.99  --res_ordering                          kbo
% 20.06/2.99  --res_to_prop_solver                    active
% 20.06/2.99  --res_prop_simpl_new                    false
% 20.06/2.99  --res_prop_simpl_given                  true
% 20.06/2.99  --res_passive_queue_type                priority_queues
% 20.06/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.06/3.00  --res_passive_queues_freq               [15;5]
% 20.06/3.00  --res_forward_subs                      full
% 20.06/3.00  --res_backward_subs                     full
% 20.06/3.00  --res_forward_subs_resolution           true
% 20.06/3.00  --res_backward_subs_resolution          true
% 20.06/3.00  --res_orphan_elimination                true
% 20.06/3.00  --res_time_limit                        2.
% 20.06/3.00  --res_out_proof                         true
% 20.06/3.00  
% 20.06/3.00  ------ Superposition Options
% 20.06/3.00  
% 20.06/3.00  --superposition_flag                    true
% 20.06/3.00  --sup_passive_queue_type                priority_queues
% 20.06/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.06/3.00  --sup_passive_queues_freq               [8;1;4]
% 20.06/3.00  --demod_completeness_check              fast
% 20.06/3.00  --demod_use_ground                      true
% 20.06/3.00  --sup_to_prop_solver                    passive
% 20.06/3.00  --sup_prop_simpl_new                    true
% 20.06/3.00  --sup_prop_simpl_given                  true
% 20.06/3.00  --sup_fun_splitting                     true
% 20.06/3.00  --sup_smt_interval                      50000
% 20.06/3.00  
% 20.06/3.00  ------ Superposition Simplification Setup
% 20.06/3.00  
% 20.06/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 20.06/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 20.06/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 20.06/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 20.06/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 20.06/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 20.06/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 20.06/3.00  --sup_immed_triv                        [TrivRules]
% 20.06/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.06/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.06/3.00  --sup_immed_bw_main                     []
% 20.06/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 20.06/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 20.06/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.06/3.00  --sup_input_bw                          []
% 20.06/3.00  
% 20.06/3.00  ------ Combination Options
% 20.06/3.00  
% 20.06/3.00  --comb_res_mult                         3
% 20.06/3.00  --comb_sup_mult                         2
% 20.06/3.00  --comb_inst_mult                        10
% 20.06/3.00  
% 20.06/3.00  ------ Debug Options
% 20.06/3.00  
% 20.06/3.00  --dbg_backtrace                         false
% 20.06/3.00  --dbg_dump_prop_clauses                 false
% 20.06/3.00  --dbg_dump_prop_clauses_file            -
% 20.06/3.00  --dbg_out_stat                          false
% 20.06/3.00  ------ Parsing...
% 20.06/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 20.06/3.00  
% 20.06/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 20.06/3.00  
% 20.06/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 20.06/3.00  
% 20.06/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 20.06/3.00  ------ Proving...
% 20.06/3.00  ------ Problem Properties 
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  clauses                                 14
% 20.06/3.00  conjectures                             1
% 20.06/3.00  EPR                                     1
% 20.06/3.00  Horn                                    10
% 20.06/3.00  unary                                   2
% 20.06/3.00  binary                                  7
% 20.06/3.00  lits                                    32
% 20.06/3.00  lits eq                                 4
% 20.06/3.00  fd_pure                                 0
% 20.06/3.00  fd_pseudo                               0
% 20.06/3.00  fd_cond                                 0
% 20.06/3.00  fd_pseudo_cond                          3
% 20.06/3.00  AC symbols                              0
% 20.06/3.00  
% 20.06/3.00  ------ Schedule dynamic 5 is on 
% 20.06/3.00  
% 20.06/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  ------ 
% 20.06/3.00  Current options:
% 20.06/3.00  ------ 
% 20.06/3.00  
% 20.06/3.00  ------ Input Options
% 20.06/3.00  
% 20.06/3.00  --out_options                           all
% 20.06/3.00  --tptp_safe_out                         true
% 20.06/3.00  --problem_path                          ""
% 20.06/3.00  --include_path                          ""
% 20.06/3.00  --clausifier                            res/vclausify_rel
% 20.06/3.00  --clausifier_options                    ""
% 20.06/3.00  --stdin                                 false
% 20.06/3.00  --stats_out                             all
% 20.06/3.00  
% 20.06/3.00  ------ General Options
% 20.06/3.00  
% 20.06/3.00  --fof                                   false
% 20.06/3.00  --time_out_real                         305.
% 20.06/3.00  --time_out_virtual                      -1.
% 20.06/3.00  --symbol_type_check                     false
% 20.06/3.00  --clausify_out                          false
% 20.06/3.00  --sig_cnt_out                           false
% 20.06/3.00  --trig_cnt_out                          false
% 20.06/3.00  --trig_cnt_out_tolerance                1.
% 20.06/3.00  --trig_cnt_out_sk_spl                   false
% 20.06/3.00  --abstr_cl_out                          false
% 20.06/3.00  
% 20.06/3.00  ------ Global Options
% 20.06/3.00  
% 20.06/3.00  --schedule                              default
% 20.06/3.00  --add_important_lit                     false
% 20.06/3.00  --prop_solver_per_cl                    1000
% 20.06/3.00  --min_unsat_core                        false
% 20.06/3.00  --soft_assumptions                      false
% 20.06/3.00  --soft_lemma_size                       3
% 20.06/3.00  --prop_impl_unit_size                   0
% 20.06/3.00  --prop_impl_unit                        []
% 20.06/3.00  --share_sel_clauses                     true
% 20.06/3.00  --reset_solvers                         false
% 20.06/3.00  --bc_imp_inh                            [conj_cone]
% 20.06/3.00  --conj_cone_tolerance                   3.
% 20.06/3.00  --extra_neg_conj                        none
% 20.06/3.00  --large_theory_mode                     true
% 20.06/3.00  --prolific_symb_bound                   200
% 20.06/3.00  --lt_threshold                          2000
% 20.06/3.00  --clause_weak_htbl                      true
% 20.06/3.00  --gc_record_bc_elim                     false
% 20.06/3.00  
% 20.06/3.00  ------ Preprocessing Options
% 20.06/3.00  
% 20.06/3.00  --preprocessing_flag                    true
% 20.06/3.00  --time_out_prep_mult                    0.1
% 20.06/3.00  --splitting_mode                        input
% 20.06/3.00  --splitting_grd                         true
% 20.06/3.00  --splitting_cvd                         false
% 20.06/3.00  --splitting_cvd_svl                     false
% 20.06/3.00  --splitting_nvd                         32
% 20.06/3.00  --sub_typing                            true
% 20.06/3.00  --prep_gs_sim                           true
% 20.06/3.00  --prep_unflatten                        true
% 20.06/3.00  --prep_res_sim                          true
% 20.06/3.00  --prep_upred                            true
% 20.06/3.00  --prep_sem_filter                       exhaustive
% 20.06/3.00  --prep_sem_filter_out                   false
% 20.06/3.00  --pred_elim                             true
% 20.06/3.00  --res_sim_input                         true
% 20.06/3.00  --eq_ax_congr_red                       true
% 20.06/3.00  --pure_diseq_elim                       true
% 20.06/3.00  --brand_transform                       false
% 20.06/3.00  --non_eq_to_eq                          false
% 20.06/3.00  --prep_def_merge                        true
% 20.06/3.00  --prep_def_merge_prop_impl              false
% 20.06/3.00  --prep_def_merge_mbd                    true
% 20.06/3.00  --prep_def_merge_tr_red                 false
% 20.06/3.00  --prep_def_merge_tr_cl                  false
% 20.06/3.00  --smt_preprocessing                     true
% 20.06/3.00  --smt_ac_axioms                         fast
% 20.06/3.00  --preprocessed_out                      false
% 20.06/3.00  --preprocessed_stats                    false
% 20.06/3.00  
% 20.06/3.00  ------ Abstraction refinement Options
% 20.06/3.00  
% 20.06/3.00  --abstr_ref                             []
% 20.06/3.00  --abstr_ref_prep                        false
% 20.06/3.00  --abstr_ref_until_sat                   false
% 20.06/3.00  --abstr_ref_sig_restrict                funpre
% 20.06/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 20.06/3.00  --abstr_ref_under                       []
% 20.06/3.00  
% 20.06/3.00  ------ SAT Options
% 20.06/3.00  
% 20.06/3.00  --sat_mode                              false
% 20.06/3.00  --sat_fm_restart_options                ""
% 20.06/3.00  --sat_gr_def                            false
% 20.06/3.00  --sat_epr_types                         true
% 20.06/3.00  --sat_non_cyclic_types                  false
% 20.06/3.00  --sat_finite_models                     false
% 20.06/3.00  --sat_fm_lemmas                         false
% 20.06/3.00  --sat_fm_prep                           false
% 20.06/3.00  --sat_fm_uc_incr                        true
% 20.06/3.00  --sat_out_model                         small
% 20.06/3.00  --sat_out_clauses                       false
% 20.06/3.00  
% 20.06/3.00  ------ QBF Options
% 20.06/3.00  
% 20.06/3.00  --qbf_mode                              false
% 20.06/3.00  --qbf_elim_univ                         false
% 20.06/3.00  --qbf_dom_inst                          none
% 20.06/3.00  --qbf_dom_pre_inst                      false
% 20.06/3.00  --qbf_sk_in                             false
% 20.06/3.00  --qbf_pred_elim                         true
% 20.06/3.00  --qbf_split                             512
% 20.06/3.00  
% 20.06/3.00  ------ BMC1 Options
% 20.06/3.00  
% 20.06/3.00  --bmc1_incremental                      false
% 20.06/3.00  --bmc1_axioms                           reachable_all
% 20.06/3.00  --bmc1_min_bound                        0
% 20.06/3.00  --bmc1_max_bound                        -1
% 20.06/3.00  --bmc1_max_bound_default                -1
% 20.06/3.00  --bmc1_symbol_reachability              true
% 20.06/3.00  --bmc1_property_lemmas                  false
% 20.06/3.00  --bmc1_k_induction                      false
% 20.06/3.00  --bmc1_non_equiv_states                 false
% 20.06/3.00  --bmc1_deadlock                         false
% 20.06/3.00  --bmc1_ucm                              false
% 20.06/3.00  --bmc1_add_unsat_core                   none
% 20.06/3.00  --bmc1_unsat_core_children              false
% 20.06/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 20.06/3.00  --bmc1_out_stat                         full
% 20.06/3.00  --bmc1_ground_init                      false
% 20.06/3.00  --bmc1_pre_inst_next_state              false
% 20.06/3.00  --bmc1_pre_inst_state                   false
% 20.06/3.00  --bmc1_pre_inst_reach_state             false
% 20.06/3.00  --bmc1_out_unsat_core                   false
% 20.06/3.00  --bmc1_aig_witness_out                  false
% 20.06/3.00  --bmc1_verbose                          false
% 20.06/3.00  --bmc1_dump_clauses_tptp                false
% 20.06/3.00  --bmc1_dump_unsat_core_tptp             false
% 20.06/3.00  --bmc1_dump_file                        -
% 20.06/3.00  --bmc1_ucm_expand_uc_limit              128
% 20.06/3.00  --bmc1_ucm_n_expand_iterations          6
% 20.06/3.00  --bmc1_ucm_extend_mode                  1
% 20.06/3.00  --bmc1_ucm_init_mode                    2
% 20.06/3.00  --bmc1_ucm_cone_mode                    none
% 20.06/3.00  --bmc1_ucm_reduced_relation_type        0
% 20.06/3.00  --bmc1_ucm_relax_model                  4
% 20.06/3.00  --bmc1_ucm_full_tr_after_sat            true
% 20.06/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 20.06/3.00  --bmc1_ucm_layered_model                none
% 20.06/3.00  --bmc1_ucm_max_lemma_size               10
% 20.06/3.00  
% 20.06/3.00  ------ AIG Options
% 20.06/3.00  
% 20.06/3.00  --aig_mode                              false
% 20.06/3.00  
% 20.06/3.00  ------ Instantiation Options
% 20.06/3.00  
% 20.06/3.00  --instantiation_flag                    true
% 20.06/3.00  --inst_sos_flag                         true
% 20.06/3.00  --inst_sos_phase                        true
% 20.06/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.06/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.06/3.00  --inst_lit_sel_side                     none
% 20.06/3.00  --inst_solver_per_active                1400
% 20.06/3.00  --inst_solver_calls_frac                1.
% 20.06/3.00  --inst_passive_queue_type               priority_queues
% 20.06/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.06/3.00  --inst_passive_queues_freq              [25;2]
% 20.06/3.00  --inst_dismatching                      true
% 20.06/3.00  --inst_eager_unprocessed_to_passive     true
% 20.06/3.00  --inst_prop_sim_given                   true
% 20.06/3.00  --inst_prop_sim_new                     false
% 20.06/3.00  --inst_subs_new                         false
% 20.06/3.00  --inst_eq_res_simp                      false
% 20.06/3.00  --inst_subs_given                       false
% 20.06/3.00  --inst_orphan_elimination               true
% 20.06/3.00  --inst_learning_loop_flag               true
% 20.06/3.00  --inst_learning_start                   3000
% 20.06/3.00  --inst_learning_factor                  2
% 20.06/3.00  --inst_start_prop_sim_after_learn       3
% 20.06/3.00  --inst_sel_renew                        solver
% 20.06/3.00  --inst_lit_activity_flag                true
% 20.06/3.00  --inst_restr_to_given                   false
% 20.06/3.00  --inst_activity_threshold               500
% 20.06/3.00  --inst_out_proof                        true
% 20.06/3.00  
% 20.06/3.00  ------ Resolution Options
% 20.06/3.00  
% 20.06/3.00  --resolution_flag                       false
% 20.06/3.00  --res_lit_sel                           adaptive
% 20.06/3.00  --res_lit_sel_side                      none
% 20.06/3.00  --res_ordering                          kbo
% 20.06/3.00  --res_to_prop_solver                    active
% 20.06/3.00  --res_prop_simpl_new                    false
% 20.06/3.00  --res_prop_simpl_given                  true
% 20.06/3.00  --res_passive_queue_type                priority_queues
% 20.06/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.06/3.00  --res_passive_queues_freq               [15;5]
% 20.06/3.00  --res_forward_subs                      full
% 20.06/3.00  --res_backward_subs                     full
% 20.06/3.00  --res_forward_subs_resolution           true
% 20.06/3.00  --res_backward_subs_resolution          true
% 20.06/3.00  --res_orphan_elimination                true
% 20.06/3.00  --res_time_limit                        2.
% 20.06/3.00  --res_out_proof                         true
% 20.06/3.00  
% 20.06/3.00  ------ Superposition Options
% 20.06/3.00  
% 20.06/3.00  --superposition_flag                    true
% 20.06/3.00  --sup_passive_queue_type                priority_queues
% 20.06/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.06/3.00  --sup_passive_queues_freq               [8;1;4]
% 20.06/3.00  --demod_completeness_check              fast
% 20.06/3.00  --demod_use_ground                      true
% 20.06/3.00  --sup_to_prop_solver                    passive
% 20.06/3.00  --sup_prop_simpl_new                    true
% 20.06/3.00  --sup_prop_simpl_given                  true
% 20.06/3.00  --sup_fun_splitting                     true
% 20.06/3.00  --sup_smt_interval                      50000
% 20.06/3.00  
% 20.06/3.00  ------ Superposition Simplification Setup
% 20.06/3.00  
% 20.06/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 20.06/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 20.06/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 20.06/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 20.06/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 20.06/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 20.06/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 20.06/3.00  --sup_immed_triv                        [TrivRules]
% 20.06/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.06/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.06/3.00  --sup_immed_bw_main                     []
% 20.06/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 20.06/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 20.06/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.06/3.00  --sup_input_bw                          []
% 20.06/3.00  
% 20.06/3.00  ------ Combination Options
% 20.06/3.00  
% 20.06/3.00  --comb_res_mult                         3
% 20.06/3.00  --comb_sup_mult                         2
% 20.06/3.00  --comb_inst_mult                        10
% 20.06/3.00  
% 20.06/3.00  ------ Debug Options
% 20.06/3.00  
% 20.06/3.00  --dbg_backtrace                         false
% 20.06/3.00  --dbg_dump_prop_clauses                 false
% 20.06/3.00  --dbg_dump_prop_clauses_file            -
% 20.06/3.00  --dbg_out_stat                          false
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  ------ Proving...
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  % SZS status Theorem for theBenchmark.p
% 20.06/3.00  
% 20.06/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 20.06/3.00  
% 20.06/3.00  fof(f6,axiom,(
% 20.06/3.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f11,plain,(
% 20.06/3.00    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 20.06/3.00    inference(ennf_transformation,[],[f6])).
% 20.06/3.00  
% 20.06/3.00  fof(f22,plain,(
% 20.06/3.00    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 20.06/3.00    introduced(choice_axiom,[])).
% 20.06/3.00  
% 20.06/3.00  fof(f23,plain,(
% 20.06/3.00    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 20.06/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f22])).
% 20.06/3.00  
% 20.06/3.00  fof(f38,plain,(
% 20.06/3.00    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f23])).
% 20.06/3.00  
% 20.06/3.00  fof(f3,axiom,(
% 20.06/3.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f17,plain,(
% 20.06/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 20.06/3.00    inference(nnf_transformation,[],[f3])).
% 20.06/3.00  
% 20.06/3.00  fof(f18,plain,(
% 20.06/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 20.06/3.00    inference(flattening,[],[f17])).
% 20.06/3.00  
% 20.06/3.00  fof(f19,plain,(
% 20.06/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 20.06/3.00    inference(rectify,[],[f18])).
% 20.06/3.00  
% 20.06/3.00  fof(f20,plain,(
% 20.06/3.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 20.06/3.00    introduced(choice_axiom,[])).
% 20.06/3.00  
% 20.06/3.00  fof(f21,plain,(
% 20.06/3.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 20.06/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 20.06/3.00  
% 20.06/3.00  fof(f30,plain,(
% 20.06/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 20.06/3.00    inference(cnf_transformation,[],[f21])).
% 20.06/3.00  
% 20.06/3.00  fof(f4,axiom,(
% 20.06/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f36,plain,(
% 20.06/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 20.06/3.00    inference(cnf_transformation,[],[f4])).
% 20.06/3.00  
% 20.06/3.00  fof(f47,plain,(
% 20.06/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 20.06/3.00    inference(definition_unfolding,[],[f30,f36])).
% 20.06/3.00  
% 20.06/3.00  fof(f51,plain,(
% 20.06/3.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 20.06/3.00    inference(equality_resolution,[],[f47])).
% 20.06/3.00  
% 20.06/3.00  fof(f1,axiom,(
% 20.06/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f26,plain,(
% 20.06/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f1])).
% 20.06/3.00  
% 20.06/3.00  fof(f41,plain,(
% 20.06/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 20.06/3.00    inference(definition_unfolding,[],[f26,f36,f36])).
% 20.06/3.00  
% 20.06/3.00  fof(f31,plain,(
% 20.06/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 20.06/3.00    inference(cnf_transformation,[],[f21])).
% 20.06/3.00  
% 20.06/3.00  fof(f46,plain,(
% 20.06/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 20.06/3.00    inference(definition_unfolding,[],[f31,f36])).
% 20.06/3.00  
% 20.06/3.00  fof(f50,plain,(
% 20.06/3.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 20.06/3.00    inference(equality_resolution,[],[f46])).
% 20.06/3.00  
% 20.06/3.00  fof(f7,conjecture,(
% 20.06/3.00    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f8,negated_conjecture,(
% 20.06/3.00    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 20.06/3.00    inference(negated_conjecture,[],[f7])).
% 20.06/3.00  
% 20.06/3.00  fof(f12,plain,(
% 20.06/3.00    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 20.06/3.00    inference(ennf_transformation,[],[f8])).
% 20.06/3.00  
% 20.06/3.00  fof(f24,plain,(
% 20.06/3.00    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) => ~r1_tarski(k3_tarski(k3_xboole_0(sK3,sK4)),k3_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),
% 20.06/3.00    introduced(choice_axiom,[])).
% 20.06/3.00  
% 20.06/3.00  fof(f25,plain,(
% 20.06/3.00    ~r1_tarski(k3_tarski(k3_xboole_0(sK3,sK4)),k3_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),
% 20.06/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f24])).
% 20.06/3.00  
% 20.06/3.00  fof(f40,plain,(
% 20.06/3.00    ~r1_tarski(k3_tarski(k3_xboole_0(sK3,sK4)),k3_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),
% 20.06/3.00    inference(cnf_transformation,[],[f25])).
% 20.06/3.00  
% 20.06/3.00  fof(f48,plain,(
% 20.06/3.00    ~r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))),
% 20.06/3.00    inference(definition_unfolding,[],[f40,f36,f36])).
% 20.06/3.00  
% 20.06/3.00  fof(f5,axiom,(
% 20.06/3.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f10,plain,(
% 20.06/3.00    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 20.06/3.00    inference(ennf_transformation,[],[f5])).
% 20.06/3.00  
% 20.06/3.00  fof(f37,plain,(
% 20.06/3.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f10])).
% 20.06/3.00  
% 20.06/3.00  fof(f2,axiom,(
% 20.06/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 20.06/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.06/3.00  
% 20.06/3.00  fof(f9,plain,(
% 20.06/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 20.06/3.00    inference(ennf_transformation,[],[f2])).
% 20.06/3.00  
% 20.06/3.00  fof(f13,plain,(
% 20.06/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 20.06/3.00    inference(nnf_transformation,[],[f9])).
% 20.06/3.00  
% 20.06/3.00  fof(f14,plain,(
% 20.06/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 20.06/3.00    inference(rectify,[],[f13])).
% 20.06/3.00  
% 20.06/3.00  fof(f15,plain,(
% 20.06/3.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 20.06/3.00    introduced(choice_axiom,[])).
% 20.06/3.00  
% 20.06/3.00  fof(f16,plain,(
% 20.06/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 20.06/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 20.06/3.00  
% 20.06/3.00  fof(f27,plain,(
% 20.06/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f16])).
% 20.06/3.00  
% 20.06/3.00  fof(f32,plain,(
% 20.06/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 20.06/3.00    inference(cnf_transformation,[],[f21])).
% 20.06/3.00  
% 20.06/3.00  fof(f45,plain,(
% 20.06/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 20.06/3.00    inference(definition_unfolding,[],[f32,f36])).
% 20.06/3.00  
% 20.06/3.00  fof(f49,plain,(
% 20.06/3.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 20.06/3.00    inference(equality_resolution,[],[f45])).
% 20.06/3.00  
% 20.06/3.00  fof(f29,plain,(
% 20.06/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f16])).
% 20.06/3.00  
% 20.06/3.00  fof(f28,plain,(
% 20.06/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f16])).
% 20.06/3.00  
% 20.06/3.00  fof(f39,plain,(
% 20.06/3.00    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 20.06/3.00    inference(cnf_transformation,[],[f23])).
% 20.06/3.00  
% 20.06/3.00  cnf(c_12,plain,
% 20.06/3.00      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 20.06/3.00      inference(cnf_transformation,[],[f38]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_23469,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 20.06/3.00      | r1_tarski(k3_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_12]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_57839,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
% 20.06/3.00      | r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_23469]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_9,plain,
% 20.06/3.00      ( r2_hidden(X0,X1)
% 20.06/3.00      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 20.06/3.00      inference(cnf_transformation,[],[f51]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_6008,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0)
% 20.06/3.00      | ~ r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_9]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_14338,plain,
% 20.06/3.00      ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
% 20.06/3.00      | r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK3) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_6008]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_0,plain,
% 20.06/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 20.06/3.00      inference(cnf_transformation,[],[f41]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_373,plain,
% 20.06/3.00      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 20.06/3.00      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 20.06/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_8,plain,
% 20.06/3.00      ( r2_hidden(X0,X1)
% 20.06/3.00      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 20.06/3.00      inference(cnf_transformation,[],[f50]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_377,plain,
% 20.06/3.00      ( r2_hidden(X0,X1) = iProver_top
% 20.06/3.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 20.06/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_1097,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = iProver_top
% 20.06/3.00      | r1_tarski(k3_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) = iProver_top ),
% 20.06/3.00      inference(superposition,[status(thm)],[c_373,c_377]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_3890,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0) = iProver_top
% 20.06/3.00      | r1_tarski(k3_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) = iProver_top ),
% 20.06/3.00      inference(superposition,[status(thm)],[c_0,c_1097]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_13,negated_conjecture,
% 20.06/3.00      ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
% 20.06/3.00      inference(cnf_transformation,[],[f48]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_372,plain,
% 20.06/3.00      ( r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) != iProver_top ),
% 20.06/3.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_3973,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4) = iProver_top ),
% 20.06/3.00      inference(superposition,[status(thm)],[c_3890,c_372]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_4561,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4) = iProver_top ),
% 20.06/3.00      inference(superposition,[status(thm)],[c_0,c_3973]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_4564,plain,
% 20.06/3.00      ( r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4) ),
% 20.06/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_4561]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_10,plain,
% 20.06/3.00      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 20.06/3.00      inference(cnf_transformation,[],[f37]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_3395,plain,
% 20.06/3.00      ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
% 20.06/3.00      | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(X0)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_10]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_3397,plain,
% 20.06/3.00      ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK3)
% 20.06/3.00      | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_3395]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_3,plain,
% 20.06/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 20.06/3.00      inference(cnf_transformation,[],[f27]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_874,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
% 20.06/3.00      | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X1)
% 20.06/3.00      | ~ r1_tarski(X0,X1) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_2000,plain,
% 20.06/3.00      ( r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
% 20.06/3.00      | ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
% 20.06/3.00      | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_874]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_2615,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
% 20.06/3.00      | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(X0))
% 20.06/3.00      | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(X0)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_2000]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_2617,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
% 20.06/3.00      | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3))
% 20.06/3.00      | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_2615]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_823,plain,
% 20.06/3.00      ( ~ r2_hidden(X0,sK4) | r1_tarski(X0,k3_tarski(sK4)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_10]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_2516,plain,
% 20.06/3.00      ( ~ r2_hidden(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK4)
% 20.06/3.00      | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_823]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_671,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),X0)
% 20.06/3.00      | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4))
% 20.06/3.00      | ~ r1_tarski(X0,k3_tarski(sK4)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_1703,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
% 20.06/3.00      | r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4))
% 20.06/3.00      | ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_671]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_7,plain,
% 20.06/3.00      ( ~ r2_hidden(X0,X1)
% 20.06/3.00      | ~ r2_hidden(X0,X2)
% 20.06/3.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 20.06/3.00      inference(cnf_transformation,[],[f49]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_504,plain,
% 20.06/3.00      ( r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))
% 20.06/3.00      | ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK4))
% 20.06/3.00      | ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k3_tarski(sK3)) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_7]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_1,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 20.06/3.00      inference(cnf_transformation,[],[f29]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_439,plain,
% 20.06/3.00      ( ~ r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))
% 20.06/3.00      | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_2,plain,
% 20.06/3.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 20.06/3.00      inference(cnf_transformation,[],[f28]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_440,plain,
% 20.06/3.00      ( r2_hidden(sK0(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))))
% 20.06/3.00      | r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_2]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_11,plain,
% 20.06/3.00      ( ~ r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 20.06/3.00      inference(cnf_transformation,[],[f39]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(c_404,plain,
% 20.06/3.00      ( ~ r1_tarski(sK2(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4))))
% 20.06/3.00      | r1_tarski(k3_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))),k4_xboole_0(k3_tarski(sK3),k4_xboole_0(k3_tarski(sK3),k3_tarski(sK4)))) ),
% 20.06/3.00      inference(instantiation,[status(thm)],[c_11]) ).
% 20.06/3.00  
% 20.06/3.00  cnf(contradiction,plain,
% 20.06/3.00      ( $false ),
% 20.06/3.00      inference(minisat,
% 20.06/3.00                [status(thm)],
% 20.06/3.00                [c_57839,c_14338,c_4564,c_3397,c_2617,c_2516,c_1703,
% 20.06/3.00                 c_504,c_439,c_440,c_404,c_13]) ).
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 20.06/3.00  
% 20.06/3.00  ------                               Statistics
% 20.06/3.00  
% 20.06/3.00  ------ General
% 20.06/3.00  
% 20.06/3.00  abstr_ref_over_cycles:                  0
% 20.06/3.00  abstr_ref_under_cycles:                 0
% 20.06/3.00  gc_basic_clause_elim:                   0
% 20.06/3.00  forced_gc_time:                         0
% 20.06/3.00  parsing_time:                           0.007
% 20.06/3.00  unif_index_cands_time:                  0.
% 20.06/3.00  unif_index_add_time:                    0.
% 20.06/3.00  orderings_time:                         0.
% 20.06/3.00  out_proof_time:                         0.01
% 20.06/3.00  total_time:                             2.381
% 20.06/3.00  num_of_symbols:                         40
% 20.06/3.00  num_of_terms:                           68136
% 20.06/3.00  
% 20.06/3.00  ------ Preprocessing
% 20.06/3.00  
% 20.06/3.00  num_of_splits:                          0
% 20.06/3.00  num_of_split_atoms:                     0
% 20.06/3.00  num_of_reused_defs:                     0
% 20.06/3.00  num_eq_ax_congr_red:                    14
% 20.06/3.00  num_of_sem_filtered_clauses:            1
% 20.06/3.00  num_of_subtypes:                        0
% 20.06/3.00  monotx_restored_types:                  0
% 20.06/3.00  sat_num_of_epr_types:                   0
% 20.06/3.00  sat_num_of_non_cyclic_types:            0
% 20.06/3.00  sat_guarded_non_collapsed_types:        0
% 20.06/3.00  num_pure_diseq_elim:                    0
% 20.06/3.00  simp_replaced_by:                       0
% 20.06/3.00  res_preprocessed:                       55
% 20.06/3.00  prep_upred:                             0
% 20.06/3.00  prep_unflattend:                        0
% 20.06/3.00  smt_new_axioms:                         0
% 20.06/3.00  pred_elim_cands:                        2
% 20.06/3.00  pred_elim:                              0
% 20.06/3.00  pred_elim_cl:                           0
% 20.06/3.00  pred_elim_cycles:                       1
% 20.06/3.00  merged_defs:                            0
% 20.06/3.00  merged_defs_ncl:                        0
% 20.06/3.00  bin_hyper_res:                          0
% 20.06/3.00  prep_cycles:                            3
% 20.06/3.00  pred_elim_time:                         0.
% 20.06/3.00  splitting_time:                         0.
% 20.06/3.00  sem_filter_time:                        0.
% 20.06/3.00  monotx_time:                            0.
% 20.06/3.00  subtype_inf_time:                       0.
% 20.06/3.00  
% 20.06/3.00  ------ Problem properties
% 20.06/3.00  
% 20.06/3.00  clauses:                                14
% 20.06/3.00  conjectures:                            1
% 20.06/3.00  epr:                                    1
% 20.06/3.00  horn:                                   10
% 20.06/3.00  ground:                                 1
% 20.06/3.00  unary:                                  2
% 20.06/3.00  binary:                                 7
% 20.06/3.00  lits:                                   32
% 20.06/3.00  lits_eq:                                4
% 20.06/3.00  fd_pure:                                0
% 20.06/3.00  fd_pseudo:                              0
% 20.06/3.00  fd_cond:                                0
% 20.06/3.00  fd_pseudo_cond:                         3
% 20.06/3.00  ac_symbols:                             0
% 20.06/3.00  
% 20.06/3.00  ------ Propositional Solver
% 20.06/3.00  
% 20.06/3.00  prop_solver_calls:                      29
% 20.06/3.00  prop_fast_solver_calls:                 1253
% 20.06/3.00  smt_solver_calls:                       0
% 20.06/3.00  smt_fast_solver_calls:                  0
% 20.06/3.00  prop_num_of_clauses:                    28769
% 20.06/3.00  prop_preprocess_simplified:             37338
% 20.06/3.00  prop_fo_subsumed:                       27
% 20.06/3.00  prop_solver_time:                       0.
% 20.06/3.00  smt_solver_time:                        0.
% 20.06/3.00  smt_fast_solver_time:                   0.
% 20.06/3.00  prop_fast_solver_time:                  0.
% 20.06/3.00  prop_unsat_core_time:                   0.001
% 20.06/3.00  
% 20.06/3.00  ------ QBF
% 20.06/3.00  
% 20.06/3.00  qbf_q_res:                              0
% 20.06/3.00  qbf_num_tautologies:                    0
% 20.06/3.00  qbf_prep_cycles:                        0
% 20.06/3.00  
% 20.06/3.00  ------ BMC1
% 20.06/3.00  
% 20.06/3.00  bmc1_current_bound:                     -1
% 20.06/3.00  bmc1_last_solved_bound:                 -1
% 20.06/3.00  bmc1_unsat_core_size:                   -1
% 20.06/3.00  bmc1_unsat_core_parents_size:           -1
% 20.06/3.00  bmc1_merge_next_fun:                    0
% 20.06/3.00  bmc1_unsat_core_clauses_time:           0.
% 20.06/3.00  
% 20.06/3.00  ------ Instantiation
% 20.06/3.00  
% 20.06/3.00  inst_num_of_clauses:                    4390
% 20.06/3.00  inst_num_in_passive:                    2830
% 20.06/3.00  inst_num_in_active:                     1334
% 20.06/3.00  inst_num_in_unprocessed:                232
% 20.06/3.00  inst_num_of_loops:                      1835
% 20.06/3.00  inst_num_of_learning_restarts:          0
% 20.06/3.00  inst_num_moves_active_passive:          498
% 20.06/3.00  inst_lit_activity:                      0
% 20.06/3.00  inst_lit_activity_moves:                1
% 20.06/3.00  inst_num_tautologies:                   0
% 20.06/3.00  inst_num_prop_implied:                  0
% 20.06/3.00  inst_num_existing_simplified:           0
% 20.06/3.00  inst_num_eq_res_simplified:             0
% 20.06/3.00  inst_num_child_elim:                    0
% 20.06/3.00  inst_num_of_dismatching_blockings:      7929
% 20.06/3.00  inst_num_of_non_proper_insts:           5231
% 20.06/3.00  inst_num_of_duplicates:                 0
% 20.06/3.00  inst_inst_num_from_inst_to_res:         0
% 20.06/3.00  inst_dismatching_checking_time:         0.
% 20.06/3.00  
% 20.06/3.00  ------ Resolution
% 20.06/3.00  
% 20.06/3.00  res_num_of_clauses:                     0
% 20.06/3.00  res_num_in_passive:                     0
% 20.06/3.00  res_num_in_active:                      0
% 20.06/3.00  res_num_of_loops:                       58
% 20.06/3.00  res_forward_subset_subsumed:            632
% 20.06/3.00  res_backward_subset_subsumed:           20
% 20.06/3.00  res_forward_subsumed:                   0
% 20.06/3.00  res_backward_subsumed:                  0
% 20.06/3.00  res_forward_subsumption_resolution:     0
% 20.06/3.00  res_backward_subsumption_resolution:    0
% 20.06/3.00  res_clause_to_clause_subsumption:       112928
% 20.06/3.00  res_orphan_elimination:                 0
% 20.06/3.00  res_tautology_del:                      504
% 20.06/3.00  res_num_eq_res_simplified:              0
% 20.06/3.00  res_num_sel_changes:                    0
% 20.06/3.00  res_moves_from_active_to_pass:          0
% 20.06/3.00  
% 20.06/3.00  ------ Superposition
% 20.06/3.00  
% 20.06/3.00  sup_time_total:                         0.
% 20.06/3.00  sup_time_generating:                    0.
% 20.06/3.00  sup_time_sim_full:                      0.
% 20.06/3.00  sup_time_sim_immed:                     0.
% 20.06/3.00  
% 20.06/3.00  sup_num_of_clauses:                     4415
% 20.06/3.00  sup_num_in_active:                      364
% 20.06/3.00  sup_num_in_passive:                     4051
% 20.06/3.00  sup_num_of_loops:                       366
% 20.06/3.00  sup_fw_superposition:                   3670
% 20.06/3.00  sup_bw_superposition:                   2957
% 20.06/3.00  sup_immediate_simplified:               547
% 20.06/3.00  sup_given_eliminated:                   0
% 20.06/3.00  comparisons_done:                       0
% 20.06/3.00  comparisons_avoided:                    0
% 20.06/3.00  
% 20.06/3.00  ------ Simplifications
% 20.06/3.00  
% 20.06/3.00  
% 20.06/3.00  sim_fw_subset_subsumed:                 163
% 20.06/3.00  sim_bw_subset_subsumed:                 78
% 20.06/3.00  sim_fw_subsumed:                        286
% 20.06/3.00  sim_bw_subsumed:                        71
% 20.06/3.00  sim_fw_subsumption_res:                 0
% 20.06/3.00  sim_bw_subsumption_res:                 0
% 20.06/3.00  sim_tautology_del:                      44
% 20.06/3.00  sim_eq_tautology_del:                   0
% 20.06/3.00  sim_eq_res_simp:                        15
% 20.06/3.00  sim_fw_demodulated:                     0
% 20.06/3.00  sim_bw_demodulated:                     0
% 20.06/3.00  sim_light_normalised:                   0
% 20.06/3.00  sim_joinable_taut:                      0
% 20.06/3.00  sim_joinable_simp:                      0
% 20.06/3.00  sim_ac_normalised:                      0
% 20.06/3.00  sim_smt_subsumption:                    0
% 20.06/3.00  
%------------------------------------------------------------------------------
