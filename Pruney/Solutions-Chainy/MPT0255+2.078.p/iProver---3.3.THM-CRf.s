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
% DateTime   : Thu Dec  3 11:34:28 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 460 expanded)
%              Number of clauses        :   34 (  94 expanded)
%              Number of leaves         :   13 ( 126 expanded)
%              Depth                    :   20
%              Number of atoms          :  198 (1415 expanded)
%              Number of equality atoms :  103 ( 530 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f44,f38])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f23])).

fof(f43,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(sK3,k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))) ),
    inference(definition_unfolding,[],[f43,f34,f44])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f25,f34,f34])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f42,f34])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_356,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(sK3,k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_729,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(sK3,k2_enumset1(sK1,sK1,sK1,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_15])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_354,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1119,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_354])).

cnf(c_2749,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK2))) = X1
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X0) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X1) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_356,c_1119])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_139,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k4_xboole_0(X1,X2)) = X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_140,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(unflattening,[status(thm)],[c_139])).

cnf(c_1116,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_140,c_354])).

cnf(c_6129,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK2))) = X1
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X0) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2749,c_1116])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_558,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_15])).

cnf(c_728,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_558])).

cnf(c_1118,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_354])).

cnf(c_6150,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(sK3,k2_enumset1(sK1,sK1,sK1,sK2))) = X0
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6129,c_1118])).

cnf(c_6222,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),X0) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6150,c_729])).

cnf(c_6351,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6222,c_1116])).

cnf(c_1115,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) = iProver_top
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_354])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6356,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(sK3,k2_enumset1(sK1,sK1,sK1,sK2))) = X0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k2_enumset1(sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6351,c_357])).

cnf(c_6395,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k2_enumset1(sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6356,c_729])).

cnf(c_6589,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k1_tarski(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1115,c_6395])).

cnf(c_7732,plain,
    ( k1_tarski(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6351,c_6589])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_447,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_448,plain,
    ( k1_tarski(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7732,c_448])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.28/1.09  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.09  
% 3.28/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/1.09  
% 3.28/1.09  ------  iProver source info
% 3.28/1.09  
% 3.28/1.09  git: date: 2020-06-30 10:37:57 +0100
% 3.28/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/1.09  git: non_committed_changes: false
% 3.28/1.09  git: last_make_outside_of_git: false
% 3.28/1.09  
% 3.28/1.09  ------ 
% 3.28/1.09  
% 3.28/1.09  ------ Input Options
% 3.28/1.09  
% 3.28/1.09  --out_options                           all
% 3.28/1.09  --tptp_safe_out                         true
% 3.28/1.09  --problem_path                          ""
% 3.28/1.09  --include_path                          ""
% 3.28/1.09  --clausifier                            res/vclausify_rel
% 3.28/1.09  --clausifier_options                    --mode clausify
% 3.28/1.09  --stdin                                 false
% 3.28/1.09  --stats_out                             all
% 3.28/1.09  
% 3.28/1.09  ------ General Options
% 3.28/1.09  
% 3.28/1.09  --fof                                   false
% 3.28/1.09  --time_out_real                         305.
% 3.28/1.09  --time_out_virtual                      -1.
% 3.28/1.09  --symbol_type_check                     false
% 3.28/1.09  --clausify_out                          false
% 3.28/1.09  --sig_cnt_out                           false
% 3.28/1.09  --trig_cnt_out                          false
% 3.28/1.09  --trig_cnt_out_tolerance                1.
% 3.28/1.09  --trig_cnt_out_sk_spl                   false
% 3.28/1.09  --abstr_cl_out                          false
% 3.28/1.09  
% 3.28/1.09  ------ Global Options
% 3.28/1.09  
% 3.28/1.09  --schedule                              default
% 3.28/1.09  --add_important_lit                     false
% 3.28/1.09  --prop_solver_per_cl                    1000
% 3.28/1.09  --min_unsat_core                        false
% 3.28/1.09  --soft_assumptions                      false
% 3.28/1.09  --soft_lemma_size                       3
% 3.28/1.09  --prop_impl_unit_size                   0
% 3.28/1.09  --prop_impl_unit                        []
% 3.28/1.09  --share_sel_clauses                     true
% 3.28/1.09  --reset_solvers                         false
% 3.28/1.09  --bc_imp_inh                            [conj_cone]
% 3.28/1.09  --conj_cone_tolerance                   3.
% 3.28/1.09  --extra_neg_conj                        none
% 3.28/1.09  --large_theory_mode                     true
% 3.28/1.09  --prolific_symb_bound                   200
% 3.28/1.09  --lt_threshold                          2000
% 3.28/1.09  --clause_weak_htbl                      true
% 3.28/1.09  --gc_record_bc_elim                     false
% 3.28/1.09  
% 3.28/1.09  ------ Preprocessing Options
% 3.28/1.09  
% 3.28/1.09  --preprocessing_flag                    true
% 3.28/1.09  --time_out_prep_mult                    0.1
% 3.28/1.09  --splitting_mode                        input
% 3.28/1.09  --splitting_grd                         true
% 3.28/1.09  --splitting_cvd                         false
% 3.28/1.09  --splitting_cvd_svl                     false
% 3.28/1.09  --splitting_nvd                         32
% 3.28/1.09  --sub_typing                            true
% 3.28/1.09  --prep_gs_sim                           true
% 3.28/1.09  --prep_unflatten                        true
% 3.28/1.09  --prep_res_sim                          true
% 3.28/1.09  --prep_upred                            true
% 3.28/1.09  --prep_sem_filter                       exhaustive
% 3.28/1.09  --prep_sem_filter_out                   false
% 3.28/1.09  --pred_elim                             true
% 3.28/1.09  --res_sim_input                         true
% 3.28/1.09  --eq_ax_congr_red                       true
% 3.28/1.09  --pure_diseq_elim                       true
% 3.28/1.09  --brand_transform                       false
% 3.28/1.09  --non_eq_to_eq                          false
% 3.28/1.09  --prep_def_merge                        true
% 3.28/1.09  --prep_def_merge_prop_impl              false
% 3.28/1.09  --prep_def_merge_mbd                    true
% 3.28/1.09  --prep_def_merge_tr_red                 false
% 3.28/1.09  --prep_def_merge_tr_cl                  false
% 3.28/1.09  --smt_preprocessing                     true
% 3.28/1.09  --smt_ac_axioms                         fast
% 3.28/1.09  --preprocessed_out                      false
% 3.28/1.09  --preprocessed_stats                    false
% 3.28/1.09  
% 3.28/1.09  ------ Abstraction refinement Options
% 3.28/1.09  
% 3.28/1.09  --abstr_ref                             []
% 3.28/1.09  --abstr_ref_prep                        false
% 3.28/1.09  --abstr_ref_until_sat                   false
% 3.28/1.09  --abstr_ref_sig_restrict                funpre
% 3.28/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.09  --abstr_ref_under                       []
% 3.28/1.09  
% 3.28/1.09  ------ SAT Options
% 3.28/1.09  
% 3.28/1.09  --sat_mode                              false
% 3.28/1.09  --sat_fm_restart_options                ""
% 3.28/1.09  --sat_gr_def                            false
% 3.28/1.09  --sat_epr_types                         true
% 3.28/1.09  --sat_non_cyclic_types                  false
% 3.28/1.09  --sat_finite_models                     false
% 3.28/1.09  --sat_fm_lemmas                         false
% 3.28/1.09  --sat_fm_prep                           false
% 3.28/1.09  --sat_fm_uc_incr                        true
% 3.28/1.09  --sat_out_model                         small
% 3.28/1.09  --sat_out_clauses                       false
% 3.28/1.09  
% 3.28/1.09  ------ QBF Options
% 3.28/1.09  
% 3.28/1.09  --qbf_mode                              false
% 3.28/1.09  --qbf_elim_univ                         false
% 3.28/1.09  --qbf_dom_inst                          none
% 3.28/1.09  --qbf_dom_pre_inst                      false
% 3.28/1.09  --qbf_sk_in                             false
% 3.28/1.09  --qbf_pred_elim                         true
% 3.28/1.09  --qbf_split                             512
% 3.28/1.09  
% 3.28/1.09  ------ BMC1 Options
% 3.28/1.09  
% 3.28/1.09  --bmc1_incremental                      false
% 3.28/1.09  --bmc1_axioms                           reachable_all
% 3.28/1.09  --bmc1_min_bound                        0
% 3.28/1.09  --bmc1_max_bound                        -1
% 3.28/1.09  --bmc1_max_bound_default                -1
% 3.28/1.09  --bmc1_symbol_reachability              true
% 3.28/1.09  --bmc1_property_lemmas                  false
% 3.28/1.09  --bmc1_k_induction                      false
% 3.28/1.09  --bmc1_non_equiv_states                 false
% 3.28/1.09  --bmc1_deadlock                         false
% 3.28/1.09  --bmc1_ucm                              false
% 3.28/1.09  --bmc1_add_unsat_core                   none
% 3.28/1.09  --bmc1_unsat_core_children              false
% 3.28/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.09  --bmc1_out_stat                         full
% 3.28/1.09  --bmc1_ground_init                      false
% 3.28/1.09  --bmc1_pre_inst_next_state              false
% 3.28/1.09  --bmc1_pre_inst_state                   false
% 3.28/1.09  --bmc1_pre_inst_reach_state             false
% 3.28/1.09  --bmc1_out_unsat_core                   false
% 3.28/1.09  --bmc1_aig_witness_out                  false
% 3.28/1.09  --bmc1_verbose                          false
% 3.28/1.09  --bmc1_dump_clauses_tptp                false
% 3.28/1.09  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.09  --bmc1_dump_file                        -
% 3.28/1.09  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.09  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.09  --bmc1_ucm_extend_mode                  1
% 3.28/1.09  --bmc1_ucm_init_mode                    2
% 3.28/1.09  --bmc1_ucm_cone_mode                    none
% 3.28/1.09  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.09  --bmc1_ucm_relax_model                  4
% 3.28/1.09  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.09  --bmc1_ucm_layered_model                none
% 3.28/1.09  --bmc1_ucm_max_lemma_size               10
% 3.28/1.09  
% 3.28/1.09  ------ AIG Options
% 3.28/1.09  
% 3.28/1.09  --aig_mode                              false
% 3.28/1.09  
% 3.28/1.09  ------ Instantiation Options
% 3.28/1.09  
% 3.28/1.09  --instantiation_flag                    true
% 3.28/1.09  --inst_sos_flag                         false
% 3.28/1.09  --inst_sos_phase                        true
% 3.28/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.09  --inst_lit_sel_side                     num_symb
% 3.28/1.09  --inst_solver_per_active                1400
% 3.28/1.09  --inst_solver_calls_frac                1.
% 3.28/1.09  --inst_passive_queue_type               priority_queues
% 3.28/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.09  --inst_passive_queues_freq              [25;2]
% 3.28/1.09  --inst_dismatching                      true
% 3.28/1.09  --inst_eager_unprocessed_to_passive     true
% 3.28/1.09  --inst_prop_sim_given                   true
% 3.28/1.09  --inst_prop_sim_new                     false
% 3.28/1.09  --inst_subs_new                         false
% 3.28/1.09  --inst_eq_res_simp                      false
% 3.28/1.09  --inst_subs_given                       false
% 3.28/1.09  --inst_orphan_elimination               true
% 3.28/1.09  --inst_learning_loop_flag               true
% 3.28/1.09  --inst_learning_start                   3000
% 3.28/1.09  --inst_learning_factor                  2
% 3.28/1.09  --inst_start_prop_sim_after_learn       3
% 3.28/1.09  --inst_sel_renew                        solver
% 3.28/1.09  --inst_lit_activity_flag                true
% 3.28/1.09  --inst_restr_to_given                   false
% 3.28/1.09  --inst_activity_threshold               500
% 3.28/1.09  --inst_out_proof                        true
% 3.28/1.09  
% 3.28/1.09  ------ Resolution Options
% 3.28/1.09  
% 3.28/1.09  --resolution_flag                       true
% 3.28/1.09  --res_lit_sel                           adaptive
% 3.28/1.09  --res_lit_sel_side                      none
% 3.28/1.09  --res_ordering                          kbo
% 3.28/1.09  --res_to_prop_solver                    active
% 3.28/1.09  --res_prop_simpl_new                    false
% 3.28/1.09  --res_prop_simpl_given                  true
% 3.28/1.09  --res_passive_queue_type                priority_queues
% 3.28/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.09  --res_passive_queues_freq               [15;5]
% 3.28/1.09  --res_forward_subs                      full
% 3.28/1.09  --res_backward_subs                     full
% 3.28/1.09  --res_forward_subs_resolution           true
% 3.28/1.09  --res_backward_subs_resolution          true
% 3.28/1.09  --res_orphan_elimination                true
% 3.28/1.09  --res_time_limit                        2.
% 3.28/1.09  --res_out_proof                         true
% 3.28/1.09  
% 3.28/1.09  ------ Superposition Options
% 3.28/1.09  
% 3.28/1.09  --superposition_flag                    true
% 3.28/1.09  --sup_passive_queue_type                priority_queues
% 3.28/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.09  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.09  --demod_completeness_check              fast
% 3.28/1.09  --demod_use_ground                      true
% 3.28/1.09  --sup_to_prop_solver                    passive
% 3.28/1.09  --sup_prop_simpl_new                    true
% 3.28/1.09  --sup_prop_simpl_given                  true
% 3.28/1.09  --sup_fun_splitting                     false
% 3.28/1.09  --sup_smt_interval                      50000
% 3.28/1.09  
% 3.28/1.09  ------ Superposition Simplification Setup
% 3.28/1.09  
% 3.28/1.09  --sup_indices_passive                   []
% 3.28/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.09  --sup_full_bw                           [BwDemod]
% 3.28/1.09  --sup_immed_triv                        [TrivRules]
% 3.28/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.09  --sup_immed_bw_main                     []
% 3.28/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.09  
% 3.28/1.09  ------ Combination Options
% 3.28/1.09  
% 3.28/1.09  --comb_res_mult                         3
% 3.28/1.09  --comb_sup_mult                         2
% 3.28/1.09  --comb_inst_mult                        10
% 3.28/1.09  
% 3.28/1.09  ------ Debug Options
% 3.28/1.09  
% 3.28/1.09  --dbg_backtrace                         false
% 3.28/1.09  --dbg_dump_prop_clauses                 false
% 3.28/1.09  --dbg_dump_prop_clauses_file            -
% 3.28/1.09  --dbg_out_stat                          false
% 3.28/1.09  ------ Parsing...
% 3.28/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/1.09  
% 3.28/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.28/1.09  
% 3.28/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/1.09  
% 3.28/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/1.09  ------ Proving...
% 3.28/1.09  ------ Problem Properties 
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  clauses                                 13
% 3.28/1.09  conjectures                             1
% 3.28/1.09  EPR                                     0
% 3.28/1.09  Horn                                    11
% 3.28/1.09  unary                                   6
% 3.28/1.09  binary                                  2
% 3.28/1.09  lits                                    26
% 3.28/1.09  lits eq                                 10
% 3.28/1.09  fd_pure                                 0
% 3.28/1.09  fd_pseudo                               0
% 3.28/1.09  fd_cond                                 0
% 3.28/1.09  fd_pseudo_cond                          3
% 3.28/1.09  AC symbols                              0
% 3.28/1.09  
% 3.28/1.09  ------ Schedule dynamic 5 is on 
% 3.28/1.09  
% 3.28/1.09  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  ------ 
% 3.28/1.09  Current options:
% 3.28/1.09  ------ 
% 3.28/1.09  
% 3.28/1.09  ------ Input Options
% 3.28/1.09  
% 3.28/1.09  --out_options                           all
% 3.28/1.09  --tptp_safe_out                         true
% 3.28/1.09  --problem_path                          ""
% 3.28/1.09  --include_path                          ""
% 3.28/1.09  --clausifier                            res/vclausify_rel
% 3.28/1.09  --clausifier_options                    --mode clausify
% 3.28/1.09  --stdin                                 false
% 3.28/1.09  --stats_out                             all
% 3.28/1.09  
% 3.28/1.09  ------ General Options
% 3.28/1.09  
% 3.28/1.09  --fof                                   false
% 3.28/1.09  --time_out_real                         305.
% 3.28/1.09  --time_out_virtual                      -1.
% 3.28/1.09  --symbol_type_check                     false
% 3.28/1.09  --clausify_out                          false
% 3.28/1.09  --sig_cnt_out                           false
% 3.28/1.09  --trig_cnt_out                          false
% 3.28/1.09  --trig_cnt_out_tolerance                1.
% 3.28/1.09  --trig_cnt_out_sk_spl                   false
% 3.28/1.09  --abstr_cl_out                          false
% 3.28/1.09  
% 3.28/1.09  ------ Global Options
% 3.28/1.09  
% 3.28/1.09  --schedule                              default
% 3.28/1.09  --add_important_lit                     false
% 3.28/1.09  --prop_solver_per_cl                    1000
% 3.28/1.09  --min_unsat_core                        false
% 3.28/1.09  --soft_assumptions                      false
% 3.28/1.09  --soft_lemma_size                       3
% 3.28/1.09  --prop_impl_unit_size                   0
% 3.28/1.09  --prop_impl_unit                        []
% 3.28/1.09  --share_sel_clauses                     true
% 3.28/1.09  --reset_solvers                         false
% 3.28/1.09  --bc_imp_inh                            [conj_cone]
% 3.28/1.09  --conj_cone_tolerance                   3.
% 3.28/1.09  --extra_neg_conj                        none
% 3.28/1.09  --large_theory_mode                     true
% 3.28/1.09  --prolific_symb_bound                   200
% 3.28/1.09  --lt_threshold                          2000
% 3.28/1.09  --clause_weak_htbl                      true
% 3.28/1.09  --gc_record_bc_elim                     false
% 3.28/1.09  
% 3.28/1.09  ------ Preprocessing Options
% 3.28/1.09  
% 3.28/1.09  --preprocessing_flag                    true
% 3.28/1.09  --time_out_prep_mult                    0.1
% 3.28/1.09  --splitting_mode                        input
% 3.28/1.09  --splitting_grd                         true
% 3.28/1.09  --splitting_cvd                         false
% 3.28/1.09  --splitting_cvd_svl                     false
% 3.28/1.09  --splitting_nvd                         32
% 3.28/1.09  --sub_typing                            true
% 3.28/1.09  --prep_gs_sim                           true
% 3.28/1.09  --prep_unflatten                        true
% 3.28/1.09  --prep_res_sim                          true
% 3.28/1.09  --prep_upred                            true
% 3.28/1.09  --prep_sem_filter                       exhaustive
% 3.28/1.09  --prep_sem_filter_out                   false
% 3.28/1.09  --pred_elim                             true
% 3.28/1.09  --res_sim_input                         true
% 3.28/1.09  --eq_ax_congr_red                       true
% 3.28/1.09  --pure_diseq_elim                       true
% 3.28/1.09  --brand_transform                       false
% 3.28/1.09  --non_eq_to_eq                          false
% 3.28/1.09  --prep_def_merge                        true
% 3.28/1.09  --prep_def_merge_prop_impl              false
% 3.28/1.09  --prep_def_merge_mbd                    true
% 3.28/1.09  --prep_def_merge_tr_red                 false
% 3.28/1.09  --prep_def_merge_tr_cl                  false
% 3.28/1.09  --smt_preprocessing                     true
% 3.28/1.09  --smt_ac_axioms                         fast
% 3.28/1.09  --preprocessed_out                      false
% 3.28/1.09  --preprocessed_stats                    false
% 3.28/1.09  
% 3.28/1.09  ------ Abstraction refinement Options
% 3.28/1.09  
% 3.28/1.09  --abstr_ref                             []
% 3.28/1.09  --abstr_ref_prep                        false
% 3.28/1.09  --abstr_ref_until_sat                   false
% 3.28/1.09  --abstr_ref_sig_restrict                funpre
% 3.28/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.09  --abstr_ref_under                       []
% 3.28/1.09  
% 3.28/1.09  ------ SAT Options
% 3.28/1.09  
% 3.28/1.09  --sat_mode                              false
% 3.28/1.09  --sat_fm_restart_options                ""
% 3.28/1.09  --sat_gr_def                            false
% 3.28/1.09  --sat_epr_types                         true
% 3.28/1.09  --sat_non_cyclic_types                  false
% 3.28/1.09  --sat_finite_models                     false
% 3.28/1.09  --sat_fm_lemmas                         false
% 3.28/1.09  --sat_fm_prep                           false
% 3.28/1.09  --sat_fm_uc_incr                        true
% 3.28/1.09  --sat_out_model                         small
% 3.28/1.09  --sat_out_clauses                       false
% 3.28/1.09  
% 3.28/1.09  ------ QBF Options
% 3.28/1.09  
% 3.28/1.09  --qbf_mode                              false
% 3.28/1.09  --qbf_elim_univ                         false
% 3.28/1.09  --qbf_dom_inst                          none
% 3.28/1.09  --qbf_dom_pre_inst                      false
% 3.28/1.09  --qbf_sk_in                             false
% 3.28/1.09  --qbf_pred_elim                         true
% 3.28/1.09  --qbf_split                             512
% 3.28/1.09  
% 3.28/1.09  ------ BMC1 Options
% 3.28/1.09  
% 3.28/1.09  --bmc1_incremental                      false
% 3.28/1.09  --bmc1_axioms                           reachable_all
% 3.28/1.09  --bmc1_min_bound                        0
% 3.28/1.09  --bmc1_max_bound                        -1
% 3.28/1.09  --bmc1_max_bound_default                -1
% 3.28/1.09  --bmc1_symbol_reachability              true
% 3.28/1.09  --bmc1_property_lemmas                  false
% 3.28/1.09  --bmc1_k_induction                      false
% 3.28/1.09  --bmc1_non_equiv_states                 false
% 3.28/1.09  --bmc1_deadlock                         false
% 3.28/1.09  --bmc1_ucm                              false
% 3.28/1.09  --bmc1_add_unsat_core                   none
% 3.28/1.09  --bmc1_unsat_core_children              false
% 3.28/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.09  --bmc1_out_stat                         full
% 3.28/1.09  --bmc1_ground_init                      false
% 3.28/1.09  --bmc1_pre_inst_next_state              false
% 3.28/1.09  --bmc1_pre_inst_state                   false
% 3.28/1.09  --bmc1_pre_inst_reach_state             false
% 3.28/1.09  --bmc1_out_unsat_core                   false
% 3.28/1.09  --bmc1_aig_witness_out                  false
% 3.28/1.09  --bmc1_verbose                          false
% 3.28/1.09  --bmc1_dump_clauses_tptp                false
% 3.28/1.09  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.09  --bmc1_dump_file                        -
% 3.28/1.09  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.09  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.09  --bmc1_ucm_extend_mode                  1
% 3.28/1.09  --bmc1_ucm_init_mode                    2
% 3.28/1.09  --bmc1_ucm_cone_mode                    none
% 3.28/1.09  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.09  --bmc1_ucm_relax_model                  4
% 3.28/1.09  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.09  --bmc1_ucm_layered_model                none
% 3.28/1.09  --bmc1_ucm_max_lemma_size               10
% 3.28/1.09  
% 3.28/1.09  ------ AIG Options
% 3.28/1.09  
% 3.28/1.09  --aig_mode                              false
% 3.28/1.09  
% 3.28/1.09  ------ Instantiation Options
% 3.28/1.09  
% 3.28/1.09  --instantiation_flag                    true
% 3.28/1.09  --inst_sos_flag                         false
% 3.28/1.09  --inst_sos_phase                        true
% 3.28/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.09  --inst_lit_sel_side                     none
% 3.28/1.09  --inst_solver_per_active                1400
% 3.28/1.09  --inst_solver_calls_frac                1.
% 3.28/1.09  --inst_passive_queue_type               priority_queues
% 3.28/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.09  --inst_passive_queues_freq              [25;2]
% 3.28/1.09  --inst_dismatching                      true
% 3.28/1.09  --inst_eager_unprocessed_to_passive     true
% 3.28/1.09  --inst_prop_sim_given                   true
% 3.28/1.09  --inst_prop_sim_new                     false
% 3.28/1.09  --inst_subs_new                         false
% 3.28/1.09  --inst_eq_res_simp                      false
% 3.28/1.09  --inst_subs_given                       false
% 3.28/1.09  --inst_orphan_elimination               true
% 3.28/1.09  --inst_learning_loop_flag               true
% 3.28/1.09  --inst_learning_start                   3000
% 3.28/1.09  --inst_learning_factor                  2
% 3.28/1.09  --inst_start_prop_sim_after_learn       3
% 3.28/1.09  --inst_sel_renew                        solver
% 3.28/1.09  --inst_lit_activity_flag                true
% 3.28/1.09  --inst_restr_to_given                   false
% 3.28/1.09  --inst_activity_threshold               500
% 3.28/1.09  --inst_out_proof                        true
% 3.28/1.09  
% 3.28/1.09  ------ Resolution Options
% 3.28/1.09  
% 3.28/1.09  --resolution_flag                       false
% 3.28/1.09  --res_lit_sel                           adaptive
% 3.28/1.09  --res_lit_sel_side                      none
% 3.28/1.09  --res_ordering                          kbo
% 3.28/1.09  --res_to_prop_solver                    active
% 3.28/1.09  --res_prop_simpl_new                    false
% 3.28/1.09  --res_prop_simpl_given                  true
% 3.28/1.09  --res_passive_queue_type                priority_queues
% 3.28/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.09  --res_passive_queues_freq               [15;5]
% 3.28/1.09  --res_forward_subs                      full
% 3.28/1.09  --res_backward_subs                     full
% 3.28/1.09  --res_forward_subs_resolution           true
% 3.28/1.09  --res_backward_subs_resolution          true
% 3.28/1.09  --res_orphan_elimination                true
% 3.28/1.09  --res_time_limit                        2.
% 3.28/1.09  --res_out_proof                         true
% 3.28/1.09  
% 3.28/1.09  ------ Superposition Options
% 3.28/1.09  
% 3.28/1.09  --superposition_flag                    true
% 3.28/1.09  --sup_passive_queue_type                priority_queues
% 3.28/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.09  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.09  --demod_completeness_check              fast
% 3.28/1.09  --demod_use_ground                      true
% 3.28/1.09  --sup_to_prop_solver                    passive
% 3.28/1.09  --sup_prop_simpl_new                    true
% 3.28/1.09  --sup_prop_simpl_given                  true
% 3.28/1.09  --sup_fun_splitting                     false
% 3.28/1.09  --sup_smt_interval                      50000
% 3.28/1.09  
% 3.28/1.09  ------ Superposition Simplification Setup
% 3.28/1.09  
% 3.28/1.09  --sup_indices_passive                   []
% 3.28/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.09  --sup_full_bw                           [BwDemod]
% 3.28/1.09  --sup_immed_triv                        [TrivRules]
% 3.28/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.09  --sup_immed_bw_main                     []
% 3.28/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.09  
% 3.28/1.09  ------ Combination Options
% 3.28/1.09  
% 3.28/1.09  --comb_res_mult                         3
% 3.28/1.09  --comb_sup_mult                         2
% 3.28/1.09  --comb_inst_mult                        10
% 3.28/1.09  
% 3.28/1.09  ------ Debug Options
% 3.28/1.09  
% 3.28/1.09  --dbg_backtrace                         false
% 3.28/1.09  --dbg_dump_prop_clauses                 false
% 3.28/1.09  --dbg_dump_prop_clauses_file            -
% 3.28/1.09  --dbg_out_stat                          false
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  ------ Proving...
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  % SZS status Theorem for theBenchmark.p
% 3.28/1.09  
% 3.28/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/1.09  
% 3.28/1.09  fof(f2,axiom,(
% 3.28/1.09    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f16,plain,(
% 3.28/1.09    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.28/1.09    inference(nnf_transformation,[],[f2])).
% 3.28/1.09  
% 3.28/1.09  fof(f17,plain,(
% 3.28/1.09    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.28/1.09    inference(flattening,[],[f16])).
% 3.28/1.09  
% 3.28/1.09  fof(f18,plain,(
% 3.28/1.09    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.28/1.09    inference(rectify,[],[f17])).
% 3.28/1.09  
% 3.28/1.09  fof(f19,plain,(
% 3.28/1.09    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.28/1.09    introduced(choice_axiom,[])).
% 3.28/1.09  
% 3.28/1.09  fof(f20,plain,(
% 3.28/1.09    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.28/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.28/1.09  
% 3.28/1.09  fof(f29,plain,(
% 3.28/1.09    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f20])).
% 3.28/1.09  
% 3.28/1.09  fof(f5,axiom,(
% 3.28/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f34,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.28/1.09    inference(cnf_transformation,[],[f5])).
% 3.28/1.09  
% 3.28/1.09  fof(f49,plain,(
% 3.28/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.09    inference(definition_unfolding,[],[f29,f34])).
% 3.28/1.09  
% 3.28/1.09  fof(f8,axiom,(
% 3.28/1.09    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f37,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f8])).
% 3.28/1.09  
% 3.28/1.09  fof(f6,axiom,(
% 3.28/1.09    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f35,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f6])).
% 3.28/1.09  
% 3.28/1.09  fof(f44,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 3.28/1.09    inference(definition_unfolding,[],[f35,f34])).
% 3.28/1.09  
% 3.28/1.09  fof(f9,axiom,(
% 3.28/1.09    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f38,plain,(
% 3.28/1.09    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f9])).
% 3.28/1.09  
% 3.28/1.09  fof(f54,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.28/1.09    inference(definition_unfolding,[],[f37,f44,f38])).
% 3.28/1.09  
% 3.28/1.09  fof(f12,conjecture,(
% 3.28/1.09    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f13,negated_conjecture,(
% 3.28/1.09    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.28/1.09    inference(negated_conjecture,[],[f12])).
% 3.28/1.09  
% 3.28/1.09  fof(f15,plain,(
% 3.28/1.09    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0),
% 3.28/1.09    inference(ennf_transformation,[],[f13])).
% 3.28/1.09  
% 3.28/1.09  fof(f23,plain,(
% 3.28/1.09    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 3.28/1.09    introduced(choice_axiom,[])).
% 3.28/1.09  
% 3.28/1.09  fof(f24,plain,(
% 3.28/1.09    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 3.28/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f23])).
% 3.28/1.09  
% 3.28/1.09  fof(f43,plain,(
% 3.28/1.09    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 3.28/1.09    inference(cnf_transformation,[],[f24])).
% 3.28/1.09  
% 3.28/1.09  fof(f59,plain,(
% 3.28/1.09    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(sK3,k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),
% 3.28/1.09    inference(definition_unfolding,[],[f43,f34,f44])).
% 3.28/1.09  
% 3.28/1.09  fof(f27,plain,(
% 3.28/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.28/1.09    inference(cnf_transformation,[],[f20])).
% 3.28/1.09  
% 3.28/1.09  fof(f51,plain,(
% 3.28/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 3.28/1.09    inference(definition_unfolding,[],[f27,f34])).
% 3.28/1.09  
% 3.28/1.09  fof(f61,plain,(
% 3.28/1.09    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X0)) )),
% 3.28/1.09    inference(equality_resolution,[],[f51])).
% 3.28/1.09  
% 3.28/1.09  fof(f3,axiom,(
% 3.28/1.09    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f14,plain,(
% 3.28/1.09    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.28/1.09    inference(ennf_transformation,[],[f3])).
% 3.28/1.09  
% 3.28/1.09  fof(f32,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f14])).
% 3.28/1.09  
% 3.28/1.09  fof(f53,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.28/1.09    inference(definition_unfolding,[],[f32,f34])).
% 3.28/1.09  
% 3.28/1.09  fof(f4,axiom,(
% 3.28/1.09    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f33,plain,(
% 3.28/1.09    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f4])).
% 3.28/1.09  
% 3.28/1.09  fof(f1,axiom,(
% 3.28/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f25,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f1])).
% 3.28/1.09  
% 3.28/1.09  fof(f46,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 3.28/1.09    inference(definition_unfolding,[],[f25,f34,f34])).
% 3.28/1.09  
% 3.28/1.09  fof(f30,plain,(
% 3.28/1.09    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f20])).
% 3.28/1.09  
% 3.28/1.09  fof(f48,plain,(
% 3.28/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.09    inference(definition_unfolding,[],[f30,f34])).
% 3.28/1.09  
% 3.28/1.09  fof(f7,axiom,(
% 3.28/1.09    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f36,plain,(
% 3.28/1.09    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.28/1.09    inference(cnf_transformation,[],[f7])).
% 3.28/1.09  
% 3.28/1.09  fof(f45,plain,(
% 3.28/1.09    ( ! [X0] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0)) )),
% 3.28/1.09    inference(definition_unfolding,[],[f36,f44])).
% 3.28/1.09  
% 3.28/1.09  fof(f11,axiom,(
% 3.28/1.09    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.28/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.09  
% 3.28/1.09  fof(f42,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 3.28/1.09    inference(cnf_transformation,[],[f11])).
% 3.28/1.09  
% 3.28/1.09  fof(f58,plain,(
% 3.28/1.09    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 3.28/1.09    inference(definition_unfolding,[],[f42,f34])).
% 3.28/1.09  
% 3.28/1.09  cnf(c_4,plain,
% 3.28/1.09      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.28/1.09      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
% 3.28/1.09      inference(cnf_transformation,[],[f49]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_356,plain,
% 3.28/1.09      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 3.28/1.09      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_10,plain,
% 3.28/1.09      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_enumset1(X0,X0,X0,X1) ),
% 3.28/1.09      inference(cnf_transformation,[],[f54]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_15,negated_conjecture,
% 3.28/1.09      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(sK3,k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))) ),
% 3.28/1.09      inference(cnf_transformation,[],[f59]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_729,plain,
% 3.28/1.09      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(sK3,k2_enumset1(sK1,sK1,sK1,sK2))) = k1_xboole_0 ),
% 3.28/1.09      inference(demodulation,[status(thm)],[c_10,c_15]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6,plain,
% 3.28/1.09      ( ~ r2_hidden(X0,X1)
% 3.28/1.09      | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 3.28/1.09      inference(cnf_transformation,[],[f61]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_354,plain,
% 3.28/1.09      ( r2_hidden(X0,X1) != iProver_top
% 3.28/1.09      | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = iProver_top ),
% 3.28/1.09      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_1119,plain,
% 3.28/1.09      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2)) != iProver_top
% 3.28/1.09      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_729,c_354]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_2749,plain,
% 3.28/1.09      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK2))) = X1
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X0) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X1) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),k1_xboole_0) = iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_356,c_1119]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_8,plain,
% 3.28/1.09      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 3.28/1.09      inference(cnf_transformation,[],[f53]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_9,plain,
% 3.28/1.09      ( r1_tarski(k1_xboole_0,X0) ),
% 3.28/1.09      inference(cnf_transformation,[],[f33]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_139,plain,
% 3.28/1.09      ( X0 != X1
% 3.28/1.09      | k5_xboole_0(X2,k4_xboole_0(X1,X2)) = X1
% 3.28/1.09      | k1_xboole_0 != X2 ),
% 3.28/1.09      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_140,plain,
% 3.28/1.09      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.28/1.09      inference(unflattening,[status(thm)],[c_139]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_1116,plain,
% 3.28/1.09      ( r2_hidden(X0,X1) = iProver_top
% 3.28/1.09      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_140,c_354]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6129,plain,
% 3.28/1.09      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(X0,k2_enumset1(sK1,sK1,sK1,sK2))) = X1
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X0) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),X0,X1),X1) = iProver_top ),
% 3.28/1.09      inference(forward_subsumption_resolution,
% 3.28/1.09                [status(thm)],
% 3.28/1.09                [c_2749,c_1116]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_1,plain,
% 3.28/1.09      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 3.28/1.09      inference(cnf_transformation,[],[f46]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_558,plain,
% 3.28/1.09      ( k5_xboole_0(sK3,k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),sK3)) = k1_xboole_0 ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_1,c_15]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_728,plain,
% 3.28/1.09      ( k5_xboole_0(sK3,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) = k1_xboole_0 ),
% 3.28/1.09      inference(demodulation,[status(thm)],[c_10,c_558]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_1118,plain,
% 3.28/1.09      ( r2_hidden(X0,sK3) != iProver_top
% 3.28/1.09      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_728,c_354]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6150,plain,
% 3.28/1.09      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(sK3,k2_enumset1(sK1,sK1,sK1,sK2))) = X0
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),X0) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k1_xboole_0) = iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_6129,c_1118]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6222,plain,
% 3.28/1.09      ( k1_xboole_0 = X0
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),X0) = iProver_top
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k1_xboole_0) = iProver_top ),
% 3.28/1.09      inference(demodulation,[status(thm)],[c_6150,c_729]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6351,plain,
% 3.28/1.09      ( k1_xboole_0 = X0
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),X0) = iProver_top ),
% 3.28/1.09      inference(forward_subsumption_resolution,
% 3.28/1.09                [status(thm)],
% 3.28/1.09                [c_6222,c_1116]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_1115,plain,
% 3.28/1.09      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) = iProver_top
% 3.28/1.09      | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_10,c_354]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_3,plain,
% 3.28/1.09      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.28/1.09      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.28/1.09      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
% 3.28/1.09      inference(cnf_transformation,[],[f48]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_357,plain,
% 3.28/1.09      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.28/1.09      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
% 3.28/1.09      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6356,plain,
% 3.28/1.09      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k4_xboole_0(sK3,k2_enumset1(sK1,sK1,sK1,sK2))) = X0
% 3.28/1.09      | k1_xboole_0 = X0
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k2_enumset1(sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_6351,c_357]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6395,plain,
% 3.28/1.09      ( k1_xboole_0 = X0
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k2_enumset1(sK1,sK1,sK1,sK2)) != iProver_top ),
% 3.28/1.09      inference(demodulation,[status(thm)],[c_6356,c_729]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_6589,plain,
% 3.28/1.09      ( k1_xboole_0 = X0
% 3.28/1.09      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK2),sK3,X0),k1_tarski(sK1)) != iProver_top ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_1115,c_6395]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_7732,plain,
% 3.28/1.09      ( k1_tarski(sK1) = k1_xboole_0 ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_6351,c_6589]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_0,plain,
% 3.28/1.09      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) = k1_tarski(X0) ),
% 3.28/1.09      inference(cnf_transformation,[],[f45]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_14,plain,
% 3.28/1.09      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) != k1_xboole_0 ),
% 3.28/1.09      inference(cnf_transformation,[],[f58]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_447,plain,
% 3.28/1.09      ( k1_tarski(X0) != k1_xboole_0 ),
% 3.28/1.09      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(c_448,plain,
% 3.28/1.09      ( k1_tarski(sK1) != k1_xboole_0 ),
% 3.28/1.09      inference(instantiation,[status(thm)],[c_447]) ).
% 3.28/1.09  
% 3.28/1.09  cnf(contradiction,plain,
% 3.28/1.09      ( $false ),
% 3.28/1.09      inference(minisat,[status(thm)],[c_7732,c_448]) ).
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/1.09  
% 3.28/1.09  ------                               Statistics
% 3.28/1.09  
% 3.28/1.09  ------ General
% 3.28/1.09  
% 3.28/1.09  abstr_ref_over_cycles:                  0
% 3.28/1.09  abstr_ref_under_cycles:                 0
% 3.28/1.09  gc_basic_clause_elim:                   0
% 3.28/1.09  forced_gc_time:                         0
% 3.28/1.09  parsing_time:                           0.007
% 3.28/1.09  unif_index_cands_time:                  0.
% 3.28/1.09  unif_index_add_time:                    0.
% 3.28/1.09  orderings_time:                         0.
% 3.28/1.09  out_proof_time:                         0.006
% 3.28/1.09  total_time:                             0.294
% 3.28/1.09  num_of_symbols:                         42
% 3.28/1.09  num_of_terms:                           10602
% 3.28/1.09  
% 3.28/1.09  ------ Preprocessing
% 3.28/1.09  
% 3.28/1.09  num_of_splits:                          0
% 3.28/1.09  num_of_split_atoms:                     0
% 3.28/1.09  num_of_reused_defs:                     0
% 3.28/1.09  num_eq_ax_congr_red:                    22
% 3.28/1.09  num_of_sem_filtered_clauses:            1
% 3.28/1.09  num_of_subtypes:                        0
% 3.28/1.09  monotx_restored_types:                  0
% 3.28/1.09  sat_num_of_epr_types:                   0
% 3.28/1.09  sat_num_of_non_cyclic_types:            0
% 3.28/1.09  sat_guarded_non_collapsed_types:        0
% 3.28/1.09  num_pure_diseq_elim:                    0
% 3.28/1.09  simp_replaced_by:                       0
% 3.28/1.09  res_preprocessed:                       68
% 3.28/1.09  prep_upred:                             0
% 3.28/1.09  prep_unflattend:                        6
% 3.28/1.09  smt_new_axioms:                         0
% 3.28/1.09  pred_elim_cands:                        1
% 3.28/1.09  pred_elim:                              1
% 3.28/1.09  pred_elim_cl:                           3
% 3.28/1.09  pred_elim_cycles:                       3
% 3.28/1.09  merged_defs:                            0
% 3.28/1.09  merged_defs_ncl:                        0
% 3.28/1.09  bin_hyper_res:                          0
% 3.28/1.09  prep_cycles:                            4
% 3.28/1.09  pred_elim_time:                         0.001
% 3.28/1.09  splitting_time:                         0.
% 3.28/1.09  sem_filter_time:                        0.
% 3.28/1.09  monotx_time:                            0.
% 3.28/1.09  subtype_inf_time:                       0.
% 3.28/1.09  
% 3.28/1.09  ------ Problem properties
% 3.28/1.09  
% 3.28/1.09  clauses:                                13
% 3.28/1.09  conjectures:                            1
% 3.28/1.09  epr:                                    0
% 3.28/1.09  horn:                                   11
% 3.28/1.09  ground:                                 1
% 3.28/1.09  unary:                                  6
% 3.28/1.09  binary:                                 2
% 3.28/1.09  lits:                                   26
% 3.28/1.09  lits_eq:                                10
% 3.28/1.09  fd_pure:                                0
% 3.28/1.09  fd_pseudo:                              0
% 3.28/1.09  fd_cond:                                0
% 3.28/1.09  fd_pseudo_cond:                         3
% 3.28/1.09  ac_symbols:                             0
% 3.28/1.09  
% 3.28/1.09  ------ Propositional Solver
% 3.28/1.09  
% 3.28/1.09  prop_solver_calls:                      28
% 3.28/1.09  prop_fast_solver_calls:                 474
% 3.28/1.09  smt_solver_calls:                       0
% 3.28/1.09  smt_fast_solver_calls:                  0
% 3.28/1.09  prop_num_of_clauses:                    2609
% 3.28/1.09  prop_preprocess_simplified:             4479
% 3.28/1.09  prop_fo_subsumed:                       1
% 3.28/1.09  prop_solver_time:                       0.
% 3.28/1.09  smt_solver_time:                        0.
% 3.28/1.09  smt_fast_solver_time:                   0.
% 3.28/1.09  prop_fast_solver_time:                  0.
% 3.28/1.09  prop_unsat_core_time:                   0.
% 3.28/1.09  
% 3.28/1.09  ------ QBF
% 3.28/1.09  
% 3.28/1.09  qbf_q_res:                              0
% 3.28/1.09  qbf_num_tautologies:                    0
% 3.28/1.09  qbf_prep_cycles:                        0
% 3.28/1.09  
% 3.28/1.09  ------ BMC1
% 3.28/1.09  
% 3.28/1.09  bmc1_current_bound:                     -1
% 3.28/1.09  bmc1_last_solved_bound:                 -1
% 3.28/1.09  bmc1_unsat_core_size:                   -1
% 3.28/1.09  bmc1_unsat_core_parents_size:           -1
% 3.28/1.09  bmc1_merge_next_fun:                    0
% 3.28/1.09  bmc1_unsat_core_clauses_time:           0.
% 3.28/1.09  
% 3.28/1.09  ------ Instantiation
% 3.28/1.09  
% 3.28/1.09  inst_num_of_clauses:                    620
% 3.28/1.09  inst_num_in_passive:                    123
% 3.28/1.09  inst_num_in_active:                     252
% 3.28/1.09  inst_num_in_unprocessed:                245
% 3.28/1.09  inst_num_of_loops:                      330
% 3.28/1.09  inst_num_of_learning_restarts:          0
% 3.28/1.09  inst_num_moves_active_passive:          73
% 3.28/1.09  inst_lit_activity:                      0
% 3.28/1.09  inst_lit_activity_moves:                0
% 3.28/1.09  inst_num_tautologies:                   0
% 3.28/1.09  inst_num_prop_implied:                  0
% 3.28/1.09  inst_num_existing_simplified:           0
% 3.28/1.09  inst_num_eq_res_simplified:             0
% 3.28/1.09  inst_num_child_elim:                    0
% 3.28/1.09  inst_num_of_dismatching_blockings:      462
% 3.28/1.09  inst_num_of_non_proper_insts:           517
% 3.28/1.09  inst_num_of_duplicates:                 0
% 3.28/1.09  inst_inst_num_from_inst_to_res:         0
% 3.28/1.09  inst_dismatching_checking_time:         0.
% 3.28/1.09  
% 3.28/1.09  ------ Resolution
% 3.28/1.09  
% 3.28/1.09  res_num_of_clauses:                     0
% 3.28/1.09  res_num_in_passive:                     0
% 3.28/1.09  res_num_in_active:                      0
% 3.28/1.09  res_num_of_loops:                       72
% 3.28/1.09  res_forward_subset_subsumed:            125
% 3.28/1.09  res_backward_subset_subsumed:           2
% 3.28/1.09  res_forward_subsumed:                   2
% 3.28/1.09  res_backward_subsumed:                  0
% 3.28/1.09  res_forward_subsumption_resolution:     0
% 3.28/1.09  res_backward_subsumption_resolution:    0
% 3.28/1.09  res_clause_to_clause_subsumption:       2272
% 3.28/1.09  res_orphan_elimination:                 0
% 3.28/1.09  res_tautology_del:                      52
% 3.28/1.09  res_num_eq_res_simplified:              0
% 3.28/1.09  res_num_sel_changes:                    0
% 3.28/1.09  res_moves_from_active_to_pass:          0
% 3.28/1.09  
% 3.28/1.09  ------ Superposition
% 3.28/1.09  
% 3.28/1.09  sup_time_total:                         0.
% 3.28/1.09  sup_time_generating:                    0.
% 3.28/1.09  sup_time_sim_full:                      0.
% 3.28/1.09  sup_time_sim_immed:                     0.
% 3.28/1.09  
% 3.28/1.09  sup_num_of_clauses:                     284
% 3.28/1.09  sup_num_in_active:                      60
% 3.28/1.09  sup_num_in_passive:                     224
% 3.28/1.09  sup_num_of_loops:                       65
% 3.28/1.09  sup_fw_superposition:                   356
% 3.28/1.09  sup_bw_superposition:                   197
% 3.28/1.09  sup_immediate_simplified:               131
% 3.28/1.09  sup_given_eliminated:                   5
% 3.28/1.09  comparisons_done:                       0
% 3.28/1.09  comparisons_avoided:                    0
% 3.28/1.09  
% 3.28/1.09  ------ Simplifications
% 3.28/1.09  
% 3.28/1.09  
% 3.28/1.09  sim_fw_subset_subsumed:                 21
% 3.28/1.09  sim_bw_subset_subsumed:                 11
% 3.28/1.09  sim_fw_subsumed:                        45
% 3.28/1.09  sim_bw_subsumed:                        1
% 3.28/1.09  sim_fw_subsumption_res:                 16
% 3.28/1.09  sim_bw_subsumption_res:                 2
% 3.28/1.09  sim_tautology_del:                      29
% 3.28/1.09  sim_eq_tautology_del:                   3
% 3.28/1.09  sim_eq_res_simp:                        9
% 3.28/1.09  sim_fw_demodulated:                     28
% 3.28/1.09  sim_bw_demodulated:                     6
% 3.28/1.09  sim_light_normalised:                   42
% 3.28/1.09  sim_joinable_taut:                      0
% 3.28/1.09  sim_joinable_simp:                      0
% 3.28/1.09  sim_ac_normalised:                      0
% 3.28/1.09  sim_smt_subsumption:                    0
% 3.28/1.09  
%------------------------------------------------------------------------------
