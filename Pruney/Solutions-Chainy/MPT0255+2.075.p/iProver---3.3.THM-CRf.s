%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:27 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 499 expanded)
%              Number of clauses        :   42 (  97 expanded)
%              Number of leaves         :   13 ( 135 expanded)
%              Depth                    :   21
%              Number of atoms          :  253 (1644 expanded)
%              Number of equality atoms :  107 ( 590 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f26,f44,f44])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f24])).

fof(f43,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f43,f44,f38])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_162,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_7682,plain,
    ( ~ r2_hidden(sK2,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
    | r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_177,plain,
    ( r2_hidden(X0,X1)
    | X1 != X2
    | k1_enumset1(X0,X0,X3) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_178,plain,
    ( r2_hidden(X0,X1)
    | k1_enumset1(X0,X0,X2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_2715,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2))
    | k1_enumset1(X0,X0,X3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_6592,plain,
    ( r2_hidden(sK2,k3_xboole_0(X0,X1))
    | k1_enumset1(sK2,sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2715])).

cnf(c_7681,plain,
    ( r2_hidden(sK2,k3_xboole_0(X0,k1_xboole_0))
    | k1_enumset1(sK2,sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6592])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_471,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_584,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_469,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_825,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_469])).

cnf(c_3939,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_825])).

cnf(c_4043,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3939,c_9])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_473,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4320,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_473])).

cnf(c_4387,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4320,c_4043])).

cnf(c_4388,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4387,c_9])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_824,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_469])).

cnf(c_4481,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_824])).

cnf(c_4315,plain,
    ( k1_enumset1(sK2,sK2,sK3) = X0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_824])).

cnf(c_4452,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4315])).

cnf(c_4638,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4481,c_4452])).

cnf(c_4644,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
    | k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4638,c_473])).

cnf(c_4734,plain,
    ( k1_enumset1(sK2,sK2,sK3) = X0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4315,c_825])).

cnf(c_4754,plain,
    ( k1_enumset1(sK2,sK2,sK3) = X0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4734])).

cnf(c_4756,plain,
    ( k1_enumset1(sK2,sK2,sK3) = X0
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4754])).

cnf(c_4802,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
    | k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4644,c_4756])).

cnf(c_4803,plain,
    ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4802,c_9])).

cnf(c_7686,plain,
    ( ~ r2_hidden(sK2,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(grounding,[status(thm)],[c_7682:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_7687,plain,
    ( r2_hidden(sK2,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_enumset1(sK2,sK2,sK3) != k1_xboole_0 ),
    inference(grounding,[status(thm)],[c_7681:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7686,c_7687,c_4803])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n019.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 14:26:52 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 3.81/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.98  
% 3.81/0.98  ------  iProver source info
% 3.81/0.98  
% 3.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.98  git: non_committed_changes: false
% 3.81/0.98  git: last_make_outside_of_git: false
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  ------ Parsing...
% 3.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  ------ Proving...
% 3.81/0.98  ------ Problem Properties 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  clauses                                 13
% 3.81/0.98  conjectures                             1
% 3.81/0.98  EPR                                     0
% 3.81/0.98  Horn                                    11
% 3.81/0.98  unary                                   4
% 3.81/0.98  binary                                  5
% 3.81/0.98  lits                                    27
% 3.81/0.98  lits eq                                 8
% 3.81/0.98  fd_pure                                 0
% 3.81/0.98  fd_pseudo                               0
% 3.81/0.98  fd_cond                                 0
% 3.81/0.98  fd_pseudo_cond                          3
% 3.81/0.98  AC symbols                              0
% 3.81/0.98  
% 3.81/0.98  ------ Input Options Time Limit: Unbounded
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  Current options:
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS status Theorem for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  fof(f3,axiom,(
% 3.81/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f12,plain,(
% 3.81/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.81/0.98    inference(rectify,[],[f3])).
% 3.81/0.98  
% 3.81/0.98  fof(f13,plain,(
% 3.81/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.81/0.98    inference(ennf_transformation,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f20,plain,(
% 3.81/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f21,plain,(
% 3.81/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 3.81/0.98  
% 3.81/0.98  fof(f34,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f21])).
% 3.81/0.98  
% 3.81/0.98  fof(f6,axiom,(
% 3.81/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f37,plain,(
% 3.81/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f6])).
% 3.81/0.98  
% 3.81/0.98  fof(f5,axiom,(
% 3.81/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f36,plain,(
% 3.81/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f5])).
% 3.81/0.98  
% 3.81/0.98  fof(f9,axiom,(
% 3.81/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f22,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.81/0.98    inference(nnf_transformation,[],[f9])).
% 3.81/0.98  
% 3.81/0.98  fof(f23,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.81/0.98    inference(flattening,[],[f22])).
% 3.81/0.98  
% 3.81/0.98  fof(f40,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f23])).
% 3.81/0.98  
% 3.81/0.98  fof(f7,axiom,(
% 3.81/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f38,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f7])).
% 3.81/0.98  
% 3.81/0.98  fof(f55,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k1_enumset1(X0,X0,X1),X2)) )),
% 3.81/0.98    inference(definition_unfolding,[],[f40,f38])).
% 3.81/0.98  
% 3.81/0.98  fof(f2,axiom,(
% 3.81/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f15,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.81/0.98    inference(nnf_transformation,[],[f2])).
% 3.81/0.98  
% 3.81/0.98  fof(f16,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.81/0.98    inference(flattening,[],[f15])).
% 3.81/0.98  
% 3.81/0.98  fof(f17,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.81/0.98    inference(rectify,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f18,plain,(
% 3.81/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f19,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.81/0.98  
% 3.81/0.98  fof(f30,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f8,axiom,(
% 3.81/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f39,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f8])).
% 3.81/0.98  
% 3.81/0.98  fof(f44,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.81/0.98    inference(definition_unfolding,[],[f39,f38])).
% 3.81/0.98  
% 3.81/0.98  fof(f48,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.81/0.98    inference(definition_unfolding,[],[f30,f44])).
% 3.81/0.98  
% 3.81/0.98  fof(f1,axiom,(
% 3.81/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f26,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f1])).
% 3.81/0.98  
% 3.81/0.98  fof(f45,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0))) )),
% 3.81/0.98    inference(definition_unfolding,[],[f26,f44,f44])).
% 3.81/0.98  
% 3.81/0.98  fof(f4,axiom,(
% 3.81/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f35,plain,(
% 3.81/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.81/0.98    inference(cnf_transformation,[],[f4])).
% 3.81/0.98  
% 3.81/0.98  fof(f52,plain,(
% 3.81/0.98    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 3.81/0.98    inference(definition_unfolding,[],[f35,f44])).
% 3.81/0.98  
% 3.81/0.98  fof(f28,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.81/0.98    inference(cnf_transformation,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f50,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 3.81/0.98    inference(definition_unfolding,[],[f28,f44])).
% 3.81/0.98  
% 3.81/0.98  fof(f58,plain,(
% 3.81/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.81/0.98    inference(equality_resolution,[],[f50])).
% 3.81/0.98  
% 3.81/0.98  fof(f32,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f46,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.81/0.98    inference(definition_unfolding,[],[f32,f44])).
% 3.81/0.98  
% 3.81/0.98  fof(f10,conjecture,(
% 3.81/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f11,negated_conjecture,(
% 3.81/0.98    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.81/0.98    inference(negated_conjecture,[],[f10])).
% 3.81/0.98  
% 3.81/0.98  fof(f14,plain,(
% 3.81/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0),
% 3.81/0.98    inference(ennf_transformation,[],[f11])).
% 3.81/0.98  
% 3.81/0.98  fof(f24,plain,(
% 3.81/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 => k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f25,plain,(
% 3.81/0.98    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f43,plain,(
% 3.81/0.98    k2_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 3.81/0.98    inference(cnf_transformation,[],[f25])).
% 3.81/0.98  
% 3.81/0.98  fof(f56,plain,(
% 3.81/0.98    k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),
% 3.81/0.98    inference(definition_unfolding,[],[f43,f44,f38])).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7,plain,
% 3.81/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11,plain,
% 3.81/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_161,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.81/0.98      | X3 != X1
% 3.81/0.98      | k1_xboole_0 != X2 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_162,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_161]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7682,plain,
% 3.81/0.98      ( ~ r2_hidden(sK2,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_162]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_10,plain,
% 3.81/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_14,plain,
% 3.81/0.98      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_177,plain,
% 3.81/0.98      ( r2_hidden(X0,X1)
% 3.81/0.98      | X1 != X2
% 3.81/0.98      | k1_enumset1(X0,X0,X3) != k1_xboole_0 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_178,plain,
% 3.81/0.98      ( r2_hidden(X0,X1) | k1_enumset1(X0,X0,X2) != k1_xboole_0 ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_177]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2715,plain,
% 3.81/0.98      ( r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.81/0.98      | k1_enumset1(X0,X0,X3) != k1_xboole_0 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_178]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6592,plain,
% 3.81/0.98      ( r2_hidden(sK2,k3_xboole_0(X0,X1))
% 3.81/0.98      | k1_enumset1(sK2,sK2,sK3) != k1_xboole_0 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_2715]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7681,plain,
% 3.81/0.98      ( r2_hidden(sK2,k3_xboole_0(X0,k1_xboole_0))
% 3.81/0.98      | k1_enumset1(sK2,sK2,sK3) != k1_xboole_0 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_6592]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3,plain,
% 3.81/0.98      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.81/0.98      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 3.81/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_471,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_0,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_9,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_584,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5,plain,
% 3.81/0.98      ( ~ r2_hidden(X0,X1)
% 3.81/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 3.81/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_469,plain,
% 3.81/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.81/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_825,plain,
% 3.81/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.81/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_584,c_469]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3939,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X1
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_471,c_825]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4043,plain,
% 3.81/0.98      ( X0 = X1
% 3.81/0.98      | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
% 3.81/0.98      inference(demodulation,[status(thm)],[c_3939,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1,plain,
% 3.81/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.81/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.81/0.98      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 3.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_473,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4320,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0
% 3.81/0.98      | k1_xboole_0 = X0
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4043,c_473]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4387,plain,
% 3.81/0.98      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0
% 3.81/0.98      | k1_xboole_0 = X0
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
% 3.81/0.98      inference(forward_subsumption_resolution,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_4320,c_4043]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4388,plain,
% 3.81/0.98      ( k1_xboole_0 = X0
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
% 3.81/0.98      inference(demodulation,[status(thm)],[c_4387,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_15,negated_conjecture,
% 3.81/0.98      ( k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_824,plain,
% 3.81/0.98      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 3.81/0.98      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_15,c_469]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4481,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4388,c_824]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4315,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = X0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X1) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4043,c_824]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4452,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_4315]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4638,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_4481,c_4452]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4644,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
% 3.81/0.98      | k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) = k1_xboole_0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4638,c_473]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4734,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = X0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X1) = iProver_top ),
% 3.81/0.98      inference(forward_subsumption_resolution,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_4315,c_825]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4754,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = X0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top
% 3.81/0.98      | iProver_top != iProver_top ),
% 3.81/0.98      inference(equality_factoring,[status(thm)],[c_4734]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4756,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = X0
% 3.81/0.98      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0,X0),X0) = iProver_top ),
% 3.81/0.98      inference(equality_resolution_simp,[status(thm)],[c_4754]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4802,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0
% 3.81/0.98      | k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) = k1_xboole_0 ),
% 3.81/0.98      inference(forward_subsumption_resolution,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_4644,c_4756]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4803,plain,
% 3.81/0.98      ( k1_enumset1(sK2,sK2,sK3) = k1_xboole_0 ),
% 3.81/0.98      inference(demodulation,[status(thm)],[c_4802,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7686,plain,
% 3.81/0.98      ( ~ r2_hidden(sK2,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 3.81/0.98      inference(grounding,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_7682:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7687,plain,
% 3.81/0.98      ( r2_hidden(sK2,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 3.81/0.98      | k1_enumset1(sK2,sK2,sK3) != k1_xboole_0 ),
% 3.81/0.98      inference(grounding,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_7681:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(contradiction,plain,
% 3.81/0.98      ( $false ),
% 3.81/0.98      inference(minisat,[status(thm)],[c_7686,c_7687,c_4803]) ).
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  ------                               Statistics
% 3.81/0.98  
% 3.81/0.98  ------ Selected
% 3.81/0.98  
% 3.81/0.98  total_time:                             0.329
% 3.81/0.98  
%------------------------------------------------------------------------------
