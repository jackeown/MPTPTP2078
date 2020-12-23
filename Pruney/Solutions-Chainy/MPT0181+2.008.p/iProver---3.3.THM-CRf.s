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
% DateTime   : Thu Dec  3 11:27:39 EST 2020

% Result     : Theorem 27.52s
% Output     : CNFRefutation 27.52s
% Verified   : 
% Statistics : Number of formulae       :  125 (107938 expanded)
%              Number of clauses        :   90 (17706 expanded)
%              Number of leaves         :   11 (31833 expanded)
%              Depth                    :   44
%              Number of atoms          :  288 (252855 expanded)
%              Number of equality atoms :  202 (123476 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) ),
    inference(definition_unfolding,[],[f25,f31,f32])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f16])).

fof(f30,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_192,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_191,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_505,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
    | r2_hidden(X0,k2_xboole_0(k1_enumset1(X4,X1,X2),k1_enumset1(X3,X3,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_191])).

cnf(c_0,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_504,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_652,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_504,c_7])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_190,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_650,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_190])).

cnf(c_975,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top
    | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_650])).

cnf(c_1882,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top
    | r2_hidden(X0,k1_enumset1(X2,X1,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_975])).

cnf(c_3168,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X2
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X1) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X2) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),k1_enumset1(X3,X0,X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_192,c_1882])).

cnf(c_35906,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3168])).

cnf(c_35915,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35906])).

cnf(c_8,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_35919,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = X3
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_35915,c_8])).

cnf(c_677,plain,
    ( k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_652,c_504])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_194,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2481,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X3
    | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X3) != iProver_top
    | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_190,c_194])).

cnf(c_5193,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3))) = X4
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
    | r2_hidden(sK0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_2481])).

cnf(c_5247,plain,
    ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5193,c_677])).

cnf(c_9721,plain,
    ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k1_enumset1(X1,X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_190,c_5247])).

cnf(c_37877,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35919,c_9721])).

cnf(c_37921,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37877,c_35919])).

cnf(c_37922,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37921,c_8])).

cnf(c_49309,plain,
    ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37922,c_9721])).

cnf(c_49323,plain,
    ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_49309,c_37922])).

cnf(c_503,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k3_enumset1(X0,X0,X1,X1,X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_524,plain,
    ( k3_enumset1(X0,X0,X1,X1,X1) = k1_enumset1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_503,c_0])).

cnf(c_501,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
    | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_190])).

cnf(c_528,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X2,X3,X4)) = iProver_top
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_501,c_8])).

cnf(c_2482,plain,
    ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X3,X4)) = X5
    | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),X5) != iProver_top
    | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_194])).

cnf(c_12768,plain,
    ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X2,X2)) = X3
    | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X2,X2),X3),X3) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_524,c_2482])).

cnf(c_12785,plain,
    ( k2_xboole_0(X0,k1_enumset1(X1,X1,X2)) = X3
    | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),X3) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12768,c_524])).

cnf(c_37882,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35919,c_12785])).

cnf(c_37894,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37882,c_35919])).

cnf(c_333,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_37895,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37894,c_0,c_333])).

cnf(c_38718,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37895,c_194])).

cnf(c_38733,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37895,c_650])).

cnf(c_38784,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38718,c_38733])).

cnf(c_38785,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_38784,c_0])).

cnf(c_39020,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) ),
    inference(superposition,[status(thm)],[c_38785,c_7])).

cnf(c_39034,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_38785,c_504])).

cnf(c_39358,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_39020,c_39034])).

cnf(c_676,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_652,c_8])).

cnf(c_38924,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_38785,c_676])).

cnf(c_39021,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_38785,c_8])).

cnf(c_39360,plain,
    ( k3_enumset1(X0,X0,X1,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_39358,c_39021])).

cnf(c_39667,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_38924,c_39360])).

cnf(c_39669,plain,
    ( k3_enumset1(X0,X0,X1,X2,X2) = k1_enumset1(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_39667,c_8,c_504])).

cnf(c_49324,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(demodulation,[status(thm)],[c_49323,c_39358,c_39669])).

cnf(c_38821,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[status(thm)],[c_38785,c_0])).

cnf(c_40962,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[status(thm)],[c_38821,c_8])).

cnf(c_49917,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_49324,c_40962])).

cnf(c_49282,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37922,c_194])).

cnf(c_49391,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49282,c_8])).

cnf(c_508,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_49773,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k3_enumset1(X1,X1,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_49324,c_508])).

cnf(c_50774,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_49773,c_39034])).

cnf(c_74352,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X1,X2)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49391,c_50774])).

cnf(c_74390,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_49917,c_74352])).

cnf(c_74415,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_74390,c_333])).

cnf(c_122958,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_74415])).

cnf(c_123058,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_122958,c_74415])).

cnf(c_123059,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
    | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X1,X0,X0)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_123058,c_0])).

cnf(c_124951,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
    | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_123059,c_194])).

cnf(c_49774,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k2_xboole_0(k1_enumset1(X1,X0,X0),k1_enumset1(X2,X2,X2)) ),
    inference(superposition,[status(thm)],[c_49324,c_7])).

cnf(c_50771,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X2) ),
    inference(demodulation,[status(thm)],[c_49774,c_8,c_39034])).

cnf(c_56420,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X0)) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[status(thm)],[c_49324,c_50771])).

cnf(c_69668,plain,
    ( k3_enumset1(X0,X0,X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[status(thm)],[c_56420,c_8])).

cnf(c_70188,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
    | r2_hidden(X0,k1_enumset1(X2,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_69668,c_528])).

cnf(c_124965,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
    | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_123059,c_70188])).

cnf(c_125080,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
    | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X1,X0,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_124951,c_124965])).

cnf(c_125081,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
    | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(demodulation,[status(thm)],[c_125080,c_0])).

cnf(c_49919,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_49324,c_38785])).

cnf(c_125876,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[status(thm)],[c_125081,c_49919])).

cnf(c_126435,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_125876,c_38785])).

cnf(c_131546,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1)) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_126435,c_8])).

cnf(c_49929,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1)) = k1_enumset1(X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_49324,c_39358])).

cnf(c_131966,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_131546,c_39360,c_49929])).

cnf(c_9,negated_conjecture,
    ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_135384,plain,
    ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_131966,c_9])).

cnf(c_78,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_569,plain,
    ( k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135384,c_569])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.52/4.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.52/4.04  
% 27.52/4.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.52/4.04  
% 27.52/4.04  ------  iProver source info
% 27.52/4.04  
% 27.52/4.04  git: date: 2020-06-30 10:37:57 +0100
% 27.52/4.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.52/4.04  git: non_committed_changes: false
% 27.52/4.04  git: last_make_outside_of_git: false
% 27.52/4.04  
% 27.52/4.04  ------ 
% 27.52/4.04  
% 27.52/4.04  ------ Input Options
% 27.52/4.04  
% 27.52/4.04  --out_options                           all
% 27.52/4.04  --tptp_safe_out                         true
% 27.52/4.04  --problem_path                          ""
% 27.52/4.04  --include_path                          ""
% 27.52/4.04  --clausifier                            res/vclausify_rel
% 27.52/4.04  --clausifier_options                    --mode clausify
% 27.52/4.04  --stdin                                 false
% 27.52/4.04  --stats_out                             all
% 27.52/4.04  
% 27.52/4.04  ------ General Options
% 27.52/4.04  
% 27.52/4.04  --fof                                   false
% 27.52/4.04  --time_out_real                         305.
% 27.52/4.04  --time_out_virtual                      -1.
% 27.52/4.04  --symbol_type_check                     false
% 27.52/4.04  --clausify_out                          false
% 27.52/4.04  --sig_cnt_out                           false
% 27.52/4.04  --trig_cnt_out                          false
% 27.52/4.04  --trig_cnt_out_tolerance                1.
% 27.52/4.04  --trig_cnt_out_sk_spl                   false
% 27.52/4.04  --abstr_cl_out                          false
% 27.52/4.04  
% 27.52/4.04  ------ Global Options
% 27.52/4.04  
% 27.52/4.04  --schedule                              default
% 27.52/4.04  --add_important_lit                     false
% 27.52/4.04  --prop_solver_per_cl                    1000
% 27.52/4.04  --min_unsat_core                        false
% 27.52/4.04  --soft_assumptions                      false
% 27.52/4.04  --soft_lemma_size                       3
% 27.52/4.04  --prop_impl_unit_size                   0
% 27.52/4.04  --prop_impl_unit                        []
% 27.52/4.04  --share_sel_clauses                     true
% 27.52/4.04  --reset_solvers                         false
% 27.52/4.04  --bc_imp_inh                            [conj_cone]
% 27.52/4.04  --conj_cone_tolerance                   3.
% 27.52/4.04  --extra_neg_conj                        none
% 27.52/4.04  --large_theory_mode                     true
% 27.52/4.04  --prolific_symb_bound                   200
% 27.52/4.04  --lt_threshold                          2000
% 27.52/4.04  --clause_weak_htbl                      true
% 27.52/4.04  --gc_record_bc_elim                     false
% 27.52/4.04  
% 27.52/4.04  ------ Preprocessing Options
% 27.52/4.04  
% 27.52/4.04  --preprocessing_flag                    true
% 27.52/4.04  --time_out_prep_mult                    0.1
% 27.52/4.04  --splitting_mode                        input
% 27.52/4.04  --splitting_grd                         true
% 27.52/4.04  --splitting_cvd                         false
% 27.52/4.04  --splitting_cvd_svl                     false
% 27.52/4.04  --splitting_nvd                         32
% 27.52/4.04  --sub_typing                            true
% 27.52/4.04  --prep_gs_sim                           true
% 27.52/4.04  --prep_unflatten                        true
% 27.52/4.04  --prep_res_sim                          true
% 27.52/4.04  --prep_upred                            true
% 27.52/4.04  --prep_sem_filter                       exhaustive
% 27.52/4.04  --prep_sem_filter_out                   false
% 27.52/4.04  --pred_elim                             true
% 27.52/4.04  --res_sim_input                         true
% 27.52/4.04  --eq_ax_congr_red                       true
% 27.52/4.04  --pure_diseq_elim                       true
% 27.52/4.04  --brand_transform                       false
% 27.52/4.04  --non_eq_to_eq                          false
% 27.52/4.04  --prep_def_merge                        true
% 27.52/4.04  --prep_def_merge_prop_impl              false
% 27.52/4.04  --prep_def_merge_mbd                    true
% 27.52/4.04  --prep_def_merge_tr_red                 false
% 27.52/4.04  --prep_def_merge_tr_cl                  false
% 27.52/4.04  --smt_preprocessing                     true
% 27.52/4.04  --smt_ac_axioms                         fast
% 27.52/4.04  --preprocessed_out                      false
% 27.52/4.04  --preprocessed_stats                    false
% 27.52/4.04  
% 27.52/4.04  ------ Abstraction refinement Options
% 27.52/4.04  
% 27.52/4.04  --abstr_ref                             []
% 27.52/4.04  --abstr_ref_prep                        false
% 27.52/4.04  --abstr_ref_until_sat                   false
% 27.52/4.04  --abstr_ref_sig_restrict                funpre
% 27.52/4.04  --abstr_ref_af_restrict_to_split_sk     false
% 27.52/4.04  --abstr_ref_under                       []
% 27.52/4.04  
% 27.52/4.04  ------ SAT Options
% 27.52/4.04  
% 27.52/4.04  --sat_mode                              false
% 27.52/4.04  --sat_fm_restart_options                ""
% 27.52/4.04  --sat_gr_def                            false
% 27.52/4.04  --sat_epr_types                         true
% 27.52/4.04  --sat_non_cyclic_types                  false
% 27.52/4.04  --sat_finite_models                     false
% 27.52/4.04  --sat_fm_lemmas                         false
% 27.52/4.04  --sat_fm_prep                           false
% 27.52/4.04  --sat_fm_uc_incr                        true
% 27.52/4.04  --sat_out_model                         small
% 27.52/4.04  --sat_out_clauses                       false
% 27.52/4.04  
% 27.52/4.04  ------ QBF Options
% 27.52/4.04  
% 27.52/4.04  --qbf_mode                              false
% 27.52/4.04  --qbf_elim_univ                         false
% 27.52/4.04  --qbf_dom_inst                          none
% 27.52/4.04  --qbf_dom_pre_inst                      false
% 27.52/4.04  --qbf_sk_in                             false
% 27.52/4.04  --qbf_pred_elim                         true
% 27.52/4.04  --qbf_split                             512
% 27.52/4.04  
% 27.52/4.04  ------ BMC1 Options
% 27.52/4.04  
% 27.52/4.04  --bmc1_incremental                      false
% 27.52/4.04  --bmc1_axioms                           reachable_all
% 27.52/4.04  --bmc1_min_bound                        0
% 27.52/4.04  --bmc1_max_bound                        -1
% 27.52/4.04  --bmc1_max_bound_default                -1
% 27.52/4.04  --bmc1_symbol_reachability              true
% 27.52/4.04  --bmc1_property_lemmas                  false
% 27.52/4.04  --bmc1_k_induction                      false
% 27.52/4.04  --bmc1_non_equiv_states                 false
% 27.52/4.04  --bmc1_deadlock                         false
% 27.52/4.04  --bmc1_ucm                              false
% 27.52/4.04  --bmc1_add_unsat_core                   none
% 27.52/4.04  --bmc1_unsat_core_children              false
% 27.52/4.04  --bmc1_unsat_core_extrapolate_axioms    false
% 27.52/4.04  --bmc1_out_stat                         full
% 27.52/4.04  --bmc1_ground_init                      false
% 27.52/4.04  --bmc1_pre_inst_next_state              false
% 27.52/4.04  --bmc1_pre_inst_state                   false
% 27.52/4.04  --bmc1_pre_inst_reach_state             false
% 27.52/4.04  --bmc1_out_unsat_core                   false
% 27.52/4.04  --bmc1_aig_witness_out                  false
% 27.52/4.04  --bmc1_verbose                          false
% 27.52/4.04  --bmc1_dump_clauses_tptp                false
% 27.52/4.04  --bmc1_dump_unsat_core_tptp             false
% 27.52/4.04  --bmc1_dump_file                        -
% 27.52/4.04  --bmc1_ucm_expand_uc_limit              128
% 27.52/4.04  --bmc1_ucm_n_expand_iterations          6
% 27.52/4.04  --bmc1_ucm_extend_mode                  1
% 27.52/4.04  --bmc1_ucm_init_mode                    2
% 27.52/4.04  --bmc1_ucm_cone_mode                    none
% 27.52/4.04  --bmc1_ucm_reduced_relation_type        0
% 27.52/4.04  --bmc1_ucm_relax_model                  4
% 27.52/4.04  --bmc1_ucm_full_tr_after_sat            true
% 27.52/4.04  --bmc1_ucm_expand_neg_assumptions       false
% 27.52/4.04  --bmc1_ucm_layered_model                none
% 27.52/4.04  --bmc1_ucm_max_lemma_size               10
% 27.52/4.04  
% 27.52/4.04  ------ AIG Options
% 27.52/4.04  
% 27.52/4.04  --aig_mode                              false
% 27.52/4.04  
% 27.52/4.04  ------ Instantiation Options
% 27.52/4.04  
% 27.52/4.04  --instantiation_flag                    true
% 27.52/4.04  --inst_sos_flag                         false
% 27.52/4.04  --inst_sos_phase                        true
% 27.52/4.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.52/4.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.52/4.04  --inst_lit_sel_side                     num_symb
% 27.52/4.04  --inst_solver_per_active                1400
% 27.52/4.04  --inst_solver_calls_frac                1.
% 27.52/4.04  --inst_passive_queue_type               priority_queues
% 27.52/4.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.52/4.04  --inst_passive_queues_freq              [25;2]
% 27.52/4.04  --inst_dismatching                      true
% 27.52/4.04  --inst_eager_unprocessed_to_passive     true
% 27.52/4.04  --inst_prop_sim_given                   true
% 27.52/4.04  --inst_prop_sim_new                     false
% 27.52/4.04  --inst_subs_new                         false
% 27.52/4.04  --inst_eq_res_simp                      false
% 27.52/4.04  --inst_subs_given                       false
% 27.52/4.04  --inst_orphan_elimination               true
% 27.52/4.04  --inst_learning_loop_flag               true
% 27.52/4.04  --inst_learning_start                   3000
% 27.52/4.04  --inst_learning_factor                  2
% 27.52/4.04  --inst_start_prop_sim_after_learn       3
% 27.52/4.04  --inst_sel_renew                        solver
% 27.52/4.04  --inst_lit_activity_flag                true
% 27.52/4.04  --inst_restr_to_given                   false
% 27.52/4.04  --inst_activity_threshold               500
% 27.52/4.04  --inst_out_proof                        true
% 27.52/4.04  
% 27.52/4.04  ------ Resolution Options
% 27.52/4.04  
% 27.52/4.04  --resolution_flag                       true
% 27.52/4.04  --res_lit_sel                           adaptive
% 27.52/4.04  --res_lit_sel_side                      none
% 27.52/4.04  --res_ordering                          kbo
% 27.52/4.04  --res_to_prop_solver                    active
% 27.52/4.04  --res_prop_simpl_new                    false
% 27.52/4.04  --res_prop_simpl_given                  true
% 27.52/4.04  --res_passive_queue_type                priority_queues
% 27.52/4.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.52/4.04  --res_passive_queues_freq               [15;5]
% 27.52/4.04  --res_forward_subs                      full
% 27.52/4.04  --res_backward_subs                     full
% 27.52/4.04  --res_forward_subs_resolution           true
% 27.52/4.04  --res_backward_subs_resolution          true
% 27.52/4.04  --res_orphan_elimination                true
% 27.52/4.04  --res_time_limit                        2.
% 27.52/4.04  --res_out_proof                         true
% 27.52/4.04  
% 27.52/4.04  ------ Superposition Options
% 27.52/4.04  
% 27.52/4.04  --superposition_flag                    true
% 27.52/4.04  --sup_passive_queue_type                priority_queues
% 27.52/4.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.52/4.04  --sup_passive_queues_freq               [8;1;4]
% 27.52/4.04  --demod_completeness_check              fast
% 27.52/4.04  --demod_use_ground                      true
% 27.52/4.04  --sup_to_prop_solver                    passive
% 27.52/4.04  --sup_prop_simpl_new                    true
% 27.52/4.04  --sup_prop_simpl_given                  true
% 27.52/4.04  --sup_fun_splitting                     false
% 27.52/4.04  --sup_smt_interval                      50000
% 27.52/4.04  
% 27.52/4.04  ------ Superposition Simplification Setup
% 27.52/4.04  
% 27.52/4.04  --sup_indices_passive                   []
% 27.52/4.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.04  --sup_full_triv                         [TrivRules;PropSubs]
% 27.52/4.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.04  --sup_full_bw                           [BwDemod]
% 27.52/4.04  --sup_immed_triv                        [TrivRules]
% 27.52/4.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.04  --sup_immed_bw_main                     []
% 27.52/4.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.04  --sup_input_triv                        [Unflattening;TrivRules]
% 27.52/4.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.04  
% 27.52/4.04  ------ Combination Options
% 27.52/4.04  
% 27.52/4.04  --comb_res_mult                         3
% 27.52/4.04  --comb_sup_mult                         2
% 27.52/4.04  --comb_inst_mult                        10
% 27.52/4.04  
% 27.52/4.04  ------ Debug Options
% 27.52/4.04  
% 27.52/4.04  --dbg_backtrace                         false
% 27.52/4.04  --dbg_dump_prop_clauses                 false
% 27.52/4.04  --dbg_dump_prop_clauses_file            -
% 27.52/4.04  --dbg_out_stat                          false
% 27.52/4.04  ------ Parsing...
% 27.52/4.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.52/4.04  
% 27.52/4.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.52/4.04  
% 27.52/4.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.52/4.04  
% 27.52/4.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.52/4.04  ------ Proving...
% 27.52/4.04  ------ Problem Properties 
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  clauses                                 10
% 27.52/4.04  conjectures                             1
% 27.52/4.04  EPR                                     0
% 27.52/4.04  Horn                                    8
% 27.52/4.04  unary                                   4
% 27.52/4.04  binary                                  2
% 27.52/4.04  lits                                    21
% 27.52/4.04  lits eq                                 7
% 27.52/4.04  fd_pure                                 0
% 27.52/4.04  fd_pseudo                               0
% 27.52/4.04  fd_cond                                 0
% 27.52/4.04  fd_pseudo_cond                          3
% 27.52/4.04  AC symbols                              0
% 27.52/4.04  
% 27.52/4.04  ------ Schedule dynamic 5 is on 
% 27.52/4.04  
% 27.52/4.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  ------ 
% 27.52/4.04  Current options:
% 27.52/4.04  ------ 
% 27.52/4.04  
% 27.52/4.04  ------ Input Options
% 27.52/4.04  
% 27.52/4.04  --out_options                           all
% 27.52/4.04  --tptp_safe_out                         true
% 27.52/4.04  --problem_path                          ""
% 27.52/4.04  --include_path                          ""
% 27.52/4.04  --clausifier                            res/vclausify_rel
% 27.52/4.04  --clausifier_options                    --mode clausify
% 27.52/4.04  --stdin                                 false
% 27.52/4.04  --stats_out                             all
% 27.52/4.04  
% 27.52/4.04  ------ General Options
% 27.52/4.04  
% 27.52/4.04  --fof                                   false
% 27.52/4.04  --time_out_real                         305.
% 27.52/4.04  --time_out_virtual                      -1.
% 27.52/4.04  --symbol_type_check                     false
% 27.52/4.04  --clausify_out                          false
% 27.52/4.04  --sig_cnt_out                           false
% 27.52/4.04  --trig_cnt_out                          false
% 27.52/4.04  --trig_cnt_out_tolerance                1.
% 27.52/4.04  --trig_cnt_out_sk_spl                   false
% 27.52/4.04  --abstr_cl_out                          false
% 27.52/4.04  
% 27.52/4.04  ------ Global Options
% 27.52/4.04  
% 27.52/4.04  --schedule                              default
% 27.52/4.04  --add_important_lit                     false
% 27.52/4.04  --prop_solver_per_cl                    1000
% 27.52/4.04  --min_unsat_core                        false
% 27.52/4.04  --soft_assumptions                      false
% 27.52/4.04  --soft_lemma_size                       3
% 27.52/4.04  --prop_impl_unit_size                   0
% 27.52/4.04  --prop_impl_unit                        []
% 27.52/4.04  --share_sel_clauses                     true
% 27.52/4.04  --reset_solvers                         false
% 27.52/4.04  --bc_imp_inh                            [conj_cone]
% 27.52/4.04  --conj_cone_tolerance                   3.
% 27.52/4.04  --extra_neg_conj                        none
% 27.52/4.04  --large_theory_mode                     true
% 27.52/4.04  --prolific_symb_bound                   200
% 27.52/4.04  --lt_threshold                          2000
% 27.52/4.04  --clause_weak_htbl                      true
% 27.52/4.04  --gc_record_bc_elim                     false
% 27.52/4.04  
% 27.52/4.04  ------ Preprocessing Options
% 27.52/4.04  
% 27.52/4.04  --preprocessing_flag                    true
% 27.52/4.04  --time_out_prep_mult                    0.1
% 27.52/4.04  --splitting_mode                        input
% 27.52/4.04  --splitting_grd                         true
% 27.52/4.04  --splitting_cvd                         false
% 27.52/4.04  --splitting_cvd_svl                     false
% 27.52/4.04  --splitting_nvd                         32
% 27.52/4.04  --sub_typing                            true
% 27.52/4.04  --prep_gs_sim                           true
% 27.52/4.04  --prep_unflatten                        true
% 27.52/4.04  --prep_res_sim                          true
% 27.52/4.04  --prep_upred                            true
% 27.52/4.04  --prep_sem_filter                       exhaustive
% 27.52/4.04  --prep_sem_filter_out                   false
% 27.52/4.04  --pred_elim                             true
% 27.52/4.04  --res_sim_input                         true
% 27.52/4.04  --eq_ax_congr_red                       true
% 27.52/4.04  --pure_diseq_elim                       true
% 27.52/4.04  --brand_transform                       false
% 27.52/4.04  --non_eq_to_eq                          false
% 27.52/4.04  --prep_def_merge                        true
% 27.52/4.04  --prep_def_merge_prop_impl              false
% 27.52/4.04  --prep_def_merge_mbd                    true
% 27.52/4.04  --prep_def_merge_tr_red                 false
% 27.52/4.04  --prep_def_merge_tr_cl                  false
% 27.52/4.04  --smt_preprocessing                     true
% 27.52/4.04  --smt_ac_axioms                         fast
% 27.52/4.04  --preprocessed_out                      false
% 27.52/4.04  --preprocessed_stats                    false
% 27.52/4.04  
% 27.52/4.04  ------ Abstraction refinement Options
% 27.52/4.04  
% 27.52/4.04  --abstr_ref                             []
% 27.52/4.04  --abstr_ref_prep                        false
% 27.52/4.04  --abstr_ref_until_sat                   false
% 27.52/4.04  --abstr_ref_sig_restrict                funpre
% 27.52/4.04  --abstr_ref_af_restrict_to_split_sk     false
% 27.52/4.04  --abstr_ref_under                       []
% 27.52/4.04  
% 27.52/4.04  ------ SAT Options
% 27.52/4.04  
% 27.52/4.04  --sat_mode                              false
% 27.52/4.04  --sat_fm_restart_options                ""
% 27.52/4.04  --sat_gr_def                            false
% 27.52/4.04  --sat_epr_types                         true
% 27.52/4.04  --sat_non_cyclic_types                  false
% 27.52/4.04  --sat_finite_models                     false
% 27.52/4.04  --sat_fm_lemmas                         false
% 27.52/4.04  --sat_fm_prep                           false
% 27.52/4.04  --sat_fm_uc_incr                        true
% 27.52/4.04  --sat_out_model                         small
% 27.52/4.04  --sat_out_clauses                       false
% 27.52/4.04  
% 27.52/4.04  ------ QBF Options
% 27.52/4.04  
% 27.52/4.04  --qbf_mode                              false
% 27.52/4.04  --qbf_elim_univ                         false
% 27.52/4.04  --qbf_dom_inst                          none
% 27.52/4.04  --qbf_dom_pre_inst                      false
% 27.52/4.04  --qbf_sk_in                             false
% 27.52/4.04  --qbf_pred_elim                         true
% 27.52/4.04  --qbf_split                             512
% 27.52/4.04  
% 27.52/4.04  ------ BMC1 Options
% 27.52/4.04  
% 27.52/4.04  --bmc1_incremental                      false
% 27.52/4.04  --bmc1_axioms                           reachable_all
% 27.52/4.04  --bmc1_min_bound                        0
% 27.52/4.04  --bmc1_max_bound                        -1
% 27.52/4.04  --bmc1_max_bound_default                -1
% 27.52/4.04  --bmc1_symbol_reachability              true
% 27.52/4.04  --bmc1_property_lemmas                  false
% 27.52/4.04  --bmc1_k_induction                      false
% 27.52/4.04  --bmc1_non_equiv_states                 false
% 27.52/4.04  --bmc1_deadlock                         false
% 27.52/4.04  --bmc1_ucm                              false
% 27.52/4.04  --bmc1_add_unsat_core                   none
% 27.52/4.04  --bmc1_unsat_core_children              false
% 27.52/4.04  --bmc1_unsat_core_extrapolate_axioms    false
% 27.52/4.04  --bmc1_out_stat                         full
% 27.52/4.04  --bmc1_ground_init                      false
% 27.52/4.04  --bmc1_pre_inst_next_state              false
% 27.52/4.04  --bmc1_pre_inst_state                   false
% 27.52/4.04  --bmc1_pre_inst_reach_state             false
% 27.52/4.04  --bmc1_out_unsat_core                   false
% 27.52/4.04  --bmc1_aig_witness_out                  false
% 27.52/4.04  --bmc1_verbose                          false
% 27.52/4.04  --bmc1_dump_clauses_tptp                false
% 27.52/4.04  --bmc1_dump_unsat_core_tptp             false
% 27.52/4.04  --bmc1_dump_file                        -
% 27.52/4.04  --bmc1_ucm_expand_uc_limit              128
% 27.52/4.04  --bmc1_ucm_n_expand_iterations          6
% 27.52/4.04  --bmc1_ucm_extend_mode                  1
% 27.52/4.04  --bmc1_ucm_init_mode                    2
% 27.52/4.04  --bmc1_ucm_cone_mode                    none
% 27.52/4.04  --bmc1_ucm_reduced_relation_type        0
% 27.52/4.04  --bmc1_ucm_relax_model                  4
% 27.52/4.04  --bmc1_ucm_full_tr_after_sat            true
% 27.52/4.04  --bmc1_ucm_expand_neg_assumptions       false
% 27.52/4.04  --bmc1_ucm_layered_model                none
% 27.52/4.04  --bmc1_ucm_max_lemma_size               10
% 27.52/4.04  
% 27.52/4.04  ------ AIG Options
% 27.52/4.04  
% 27.52/4.04  --aig_mode                              false
% 27.52/4.04  
% 27.52/4.04  ------ Instantiation Options
% 27.52/4.04  
% 27.52/4.04  --instantiation_flag                    true
% 27.52/4.04  --inst_sos_flag                         false
% 27.52/4.04  --inst_sos_phase                        true
% 27.52/4.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.52/4.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.52/4.04  --inst_lit_sel_side                     none
% 27.52/4.04  --inst_solver_per_active                1400
% 27.52/4.04  --inst_solver_calls_frac                1.
% 27.52/4.04  --inst_passive_queue_type               priority_queues
% 27.52/4.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.52/4.04  --inst_passive_queues_freq              [25;2]
% 27.52/4.04  --inst_dismatching                      true
% 27.52/4.04  --inst_eager_unprocessed_to_passive     true
% 27.52/4.04  --inst_prop_sim_given                   true
% 27.52/4.04  --inst_prop_sim_new                     false
% 27.52/4.04  --inst_subs_new                         false
% 27.52/4.04  --inst_eq_res_simp                      false
% 27.52/4.04  --inst_subs_given                       false
% 27.52/4.04  --inst_orphan_elimination               true
% 27.52/4.04  --inst_learning_loop_flag               true
% 27.52/4.04  --inst_learning_start                   3000
% 27.52/4.04  --inst_learning_factor                  2
% 27.52/4.04  --inst_start_prop_sim_after_learn       3
% 27.52/4.04  --inst_sel_renew                        solver
% 27.52/4.04  --inst_lit_activity_flag                true
% 27.52/4.04  --inst_restr_to_given                   false
% 27.52/4.04  --inst_activity_threshold               500
% 27.52/4.04  --inst_out_proof                        true
% 27.52/4.04  
% 27.52/4.04  ------ Resolution Options
% 27.52/4.04  
% 27.52/4.04  --resolution_flag                       false
% 27.52/4.04  --res_lit_sel                           adaptive
% 27.52/4.04  --res_lit_sel_side                      none
% 27.52/4.04  --res_ordering                          kbo
% 27.52/4.04  --res_to_prop_solver                    active
% 27.52/4.04  --res_prop_simpl_new                    false
% 27.52/4.04  --res_prop_simpl_given                  true
% 27.52/4.04  --res_passive_queue_type                priority_queues
% 27.52/4.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.52/4.04  --res_passive_queues_freq               [15;5]
% 27.52/4.04  --res_forward_subs                      full
% 27.52/4.04  --res_backward_subs                     full
% 27.52/4.04  --res_forward_subs_resolution           true
% 27.52/4.04  --res_backward_subs_resolution          true
% 27.52/4.04  --res_orphan_elimination                true
% 27.52/4.04  --res_time_limit                        2.
% 27.52/4.04  --res_out_proof                         true
% 27.52/4.04  
% 27.52/4.04  ------ Superposition Options
% 27.52/4.04  
% 27.52/4.04  --superposition_flag                    true
% 27.52/4.04  --sup_passive_queue_type                priority_queues
% 27.52/4.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.52/4.04  --sup_passive_queues_freq               [8;1;4]
% 27.52/4.04  --demod_completeness_check              fast
% 27.52/4.04  --demod_use_ground                      true
% 27.52/4.04  --sup_to_prop_solver                    passive
% 27.52/4.04  --sup_prop_simpl_new                    true
% 27.52/4.04  --sup_prop_simpl_given                  true
% 27.52/4.04  --sup_fun_splitting                     false
% 27.52/4.04  --sup_smt_interval                      50000
% 27.52/4.04  
% 27.52/4.04  ------ Superposition Simplification Setup
% 27.52/4.04  
% 27.52/4.04  --sup_indices_passive                   []
% 27.52/4.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.04  --sup_full_triv                         [TrivRules;PropSubs]
% 27.52/4.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.04  --sup_full_bw                           [BwDemod]
% 27.52/4.04  --sup_immed_triv                        [TrivRules]
% 27.52/4.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.04  --sup_immed_bw_main                     []
% 27.52/4.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.04  --sup_input_triv                        [Unflattening;TrivRules]
% 27.52/4.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.04  
% 27.52/4.04  ------ Combination Options
% 27.52/4.04  
% 27.52/4.04  --comb_res_mult                         3
% 27.52/4.04  --comb_sup_mult                         2
% 27.52/4.04  --comb_inst_mult                        10
% 27.52/4.04  
% 27.52/4.04  ------ Debug Options
% 27.52/4.04  
% 27.52/4.04  --dbg_backtrace                         false
% 27.52/4.04  --dbg_dump_prop_clauses                 false
% 27.52/4.04  --dbg_dump_prop_clauses_file            -
% 27.52/4.04  --dbg_out_stat                          false
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  ------ Proving...
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  % SZS status Theorem for theBenchmark.p
% 27.52/4.04  
% 27.52/4.04  % SZS output start CNFRefutation for theBenchmark.p
% 27.52/4.04  
% 27.52/4.04  fof(f1,axiom,(
% 27.52/4.04    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f11,plain,(
% 27.52/4.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.04    inference(nnf_transformation,[],[f1])).
% 27.52/4.04  
% 27.52/4.04  fof(f12,plain,(
% 27.52/4.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.04    inference(flattening,[],[f11])).
% 27.52/4.04  
% 27.52/4.04  fof(f13,plain,(
% 27.52/4.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.04    inference(rectify,[],[f12])).
% 27.52/4.04  
% 27.52/4.04  fof(f14,plain,(
% 27.52/4.04    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.52/4.04    introduced(choice_axiom,[])).
% 27.52/4.04  
% 27.52/4.04  fof(f15,plain,(
% 27.52/4.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 27.52/4.04  
% 27.52/4.04  fof(f21,plain,(
% 27.52/4.04    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f15])).
% 27.52/4.04  
% 27.52/4.04  fof(f3,axiom,(
% 27.52/4.04    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f25,plain,(
% 27.52/4.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f3])).
% 27.52/4.04  
% 27.52/4.04  fof(f2,axiom,(
% 27.52/4.04    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f24,plain,(
% 27.52/4.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f2])).
% 27.52/4.04  
% 27.52/4.04  fof(f4,axiom,(
% 27.52/4.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f26,plain,(
% 27.52/4.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f4])).
% 27.52/4.04  
% 27.52/4.04  fof(f5,axiom,(
% 27.52/4.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f27,plain,(
% 27.52/4.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f5])).
% 27.52/4.04  
% 27.52/4.04  fof(f31,plain,(
% 27.52/4.04    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 27.52/4.04    inference(definition_unfolding,[],[f26,f27])).
% 27.52/4.04  
% 27.52/4.04  fof(f32,plain,(
% 27.52/4.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.52/4.04    inference(definition_unfolding,[],[f24,f31])).
% 27.52/4.04  
% 27.52/4.04  fof(f34,plain,(
% 27.52/4.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) )),
% 27.52/4.04    inference(definition_unfolding,[],[f25,f31,f32])).
% 27.52/4.04  
% 27.52/4.04  fof(f20,plain,(
% 27.52/4.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 27.52/4.04    inference(cnf_transformation,[],[f15])).
% 27.52/4.04  
% 27.52/4.04  fof(f36,plain,(
% 27.52/4.04    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 27.52/4.04    inference(equality_resolution,[],[f20])).
% 27.52/4.04  
% 27.52/4.04  fof(f6,axiom,(
% 27.52/4.04    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f28,plain,(
% 27.52/4.04    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f6])).
% 27.52/4.04  
% 27.52/4.04  fof(f33,plain,(
% 27.52/4.04    ( ! [X2,X0,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 27.52/4.04    inference(definition_unfolding,[],[f28,f32])).
% 27.52/4.04  
% 27.52/4.04  fof(f19,plain,(
% 27.52/4.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 27.52/4.04    inference(cnf_transformation,[],[f15])).
% 27.52/4.04  
% 27.52/4.04  fof(f37,plain,(
% 27.52/4.04    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 27.52/4.04    inference(equality_resolution,[],[f19])).
% 27.52/4.04  
% 27.52/4.04  fof(f7,axiom,(
% 27.52/4.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f29,plain,(
% 27.52/4.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f7])).
% 27.52/4.04  
% 27.52/4.04  fof(f35,plain,(
% 27.52/4.04    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.52/4.04    inference(definition_unfolding,[],[f29,f32])).
% 27.52/4.04  
% 27.52/4.04  fof(f23,plain,(
% 27.52/4.04    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.52/4.04    inference(cnf_transformation,[],[f15])).
% 27.52/4.04  
% 27.52/4.04  fof(f8,conjecture,(
% 27.52/4.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 27.52/4.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.04  
% 27.52/4.04  fof(f9,negated_conjecture,(
% 27.52/4.04    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 27.52/4.04    inference(negated_conjecture,[],[f8])).
% 27.52/4.04  
% 27.52/4.04  fof(f10,plain,(
% 27.52/4.04    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)),
% 27.52/4.04    inference(ennf_transformation,[],[f9])).
% 27.52/4.04  
% 27.52/4.04  fof(f16,plain,(
% 27.52/4.04    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2)),
% 27.52/4.04    introduced(choice_axiom,[])).
% 27.52/4.04  
% 27.52/4.04  fof(f17,plain,(
% 27.52/4.04    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2)),
% 27.52/4.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f16])).
% 27.52/4.04  
% 27.52/4.04  fof(f30,plain,(
% 27.52/4.04    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2)),
% 27.52/4.04    inference(cnf_transformation,[],[f17])).
% 27.52/4.04  
% 27.52/4.04  cnf(c_3,plain,
% 27.52/4.04      ( r2_hidden(sK0(X0,X1,X2),X1)
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X0)
% 27.52/4.04      | k2_xboole_0(X0,X1) = X2 ),
% 27.52/4.04      inference(cnf_transformation,[],[f21]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_192,plain,
% 27.52/4.04      ( k2_xboole_0(X0,X1) = X2
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 27.52/4.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_7,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
% 27.52/4.04      inference(cnf_transformation,[],[f34]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_4,plain,
% 27.52/4.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 27.52/4.04      inference(cnf_transformation,[],[f36]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_191,plain,
% 27.52/4.04      ( r2_hidden(X0,X1) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 27.52/4.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_505,plain,
% 27.52/4.04      ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k2_xboole_0(k1_enumset1(X4,X1,X2),k1_enumset1(X3,X3,X3))) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_7,c_191]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_0,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(cnf_transformation,[],[f33]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_504,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_652,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_504,c_7]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_5,plain,
% 27.52/4.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 27.52/4.04      inference(cnf_transformation,[],[f37]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_190,plain,
% 27.52/4.04      ( r2_hidden(X0,X1) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 27.52/4.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_650,plain,
% 27.52/4.04      ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_504,c_190]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_975,plain,
% 27.52/4.04      ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top
% 27.52/4.04      | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_652,c_650]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_1882,plain,
% 27.52/4.04      ( r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k1_enumset1(X2,X1,X3)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_505,c_975]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_3168,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X2
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X1) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X2) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),k1_enumset1(X3,X0,X4)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_192,c_1882]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_35906,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top
% 27.52/4.04      | iProver_top != iProver_top ),
% 27.52/4.04      inference(equality_factoring,[status(thm)],[c_3168]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_35915,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.04      inference(equality_resolution_simp,[status(thm)],[c_35906]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_8,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
% 27.52/4.04      inference(cnf_transformation,[],[f35]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_35919,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = X3
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_35915,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_677,plain,
% 27.52/4.04      ( k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_652,c_504]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_1,plain,
% 27.52/4.04      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 27.52/4.04      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 27.52/4.04      | k2_xboole_0(X0,X1) = X2 ),
% 27.52/4.04      inference(cnf_transformation,[],[f23]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_194,plain,
% 27.52/4.04      ( k2_xboole_0(X0,X1) = X2
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 27.52/4.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_2481,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X3
% 27.52/4.04      | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X3) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X1) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_190,c_194]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_5193,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3))) = X4
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_677,c_2481]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_5247,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_5193,c_677]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_9721,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k1_enumset1(X1,X2,X2)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_190,c_5247]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_37877,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_35919,c_9721]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_37921,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.04      inference(forward_subsumption_resolution,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_37877,c_35919]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_37922,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_37921,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49309,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_37922,c_9721]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49323,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.04      inference(forward_subsumption_resolution,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_49309,c_37922]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_503,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k3_enumset1(X0,X0,X1,X1,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_524,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X1,X1) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_503,c_0]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_501,plain,
% 27.52/4.04      ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_7,c_190]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_528,plain,
% 27.52/4.04      ( r2_hidden(X0,k3_enumset1(X1,X1,X2,X3,X4)) = iProver_top
% 27.52/4.04      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_501,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_2482,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X3,X4)) = X5
% 27.52/4.04      | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),X5) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),k1_enumset1(X1,X2,X3)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_528,c_194]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_12768,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X2,X2)) = X3
% 27.52/4.04      | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X2,X2),X3),X3) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_524,c_2482]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_12785,plain,
% 27.52/4.04      ( k2_xboole_0(X0,k1_enumset1(X1,X1,X2)) = X3
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),X3) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_12768,c_524]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_37882,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_35919,c_12785]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_37894,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.04      inference(forward_subsumption_resolution,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_37882,c_35919]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_333,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_37895,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_37894,c_0,c_333]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_38718,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_37895,c_194]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_38733,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X2)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_37895,c_650]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_38784,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.04      inference(forward_subsumption_resolution,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_38718,c_38733]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_38785,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_38784,c_0]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39020,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_38785,c_7]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39034,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_38785,c_504]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39358,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(light_normalisation,[status(thm)],[c_39020,c_39034]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_676,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_652,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_38924,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_38785,c_676]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39021,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_38785,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39360,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_39358,c_39021]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39667,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(light_normalisation,[status(thm)],[c_38924,c_39360]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_39669,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X2,X2) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_39667,c_8,c_504]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49324,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_49323,c_39358,c_39669]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_38821,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_38785,c_0]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_40962,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_38821,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49917,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X1,X0,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49324,c_40962]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49282,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_37922,c_194]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49391,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_49282,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_508,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49773,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k3_enumset1(X1,X1,X0,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49324,c_508]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_50774,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X2) ),
% 27.52/4.04      inference(light_normalisation,[status(thm)],[c_49773,c_39034]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_74352,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X1,X2)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_49391,c_50774]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_74390,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49917,c_74352]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_74415,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_74390,c_333]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_122958,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_3168,c_74415]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_123058,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top ),
% 27.52/4.04      inference(forward_subsumption_resolution,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_122958,c_74415]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_123059,plain,
% 27.52/4.04      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X1,X0,X0)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_123058,c_0]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_124951,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
% 27.52/4.04      | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_123059,c_194]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49774,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k2_xboole_0(k1_enumset1(X1,X0,X0),k1_enumset1(X2,X2,X2)) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49324,c_7]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_50771,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X2) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_49774,c_8,c_39034]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_56420,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X0)) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49324,c_50771]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_69668,plain,
% 27.52/4.04      ( k3_enumset1(X0,X0,X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_56420,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_70188,plain,
% 27.52/4.04      ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
% 27.52/4.04      | r2_hidden(X0,k1_enumset1(X2,X1,X1)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_69668,c_528]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_124965,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
% 27.52/4.04      | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.04      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_123059,c_70188]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_125080,plain,
% 27.52/4.04      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.04      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.04      inference(forward_subsumption_resolution,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_124951,c_124965]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_125081,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
% 27.52/4.04      | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_125080,c_0]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49919,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X1,X0) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49324,c_38785]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_125876,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_125081,c_49919]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_126435,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_125876,c_38785]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_131546,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1)) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_126435,c_8]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_49929,plain,
% 27.52/4.04      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1)) = k1_enumset1(X0,X2,X1) ),
% 27.52/4.04      inference(superposition,[status(thm)],[c_49324,c_39358]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_131966,plain,
% 27.52/4.04      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
% 27.52/4.04      inference(light_normalisation,
% 27.52/4.04                [status(thm)],
% 27.52/4.04                [c_131546,c_39360,c_49929]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_9,negated_conjecture,
% 27.52/4.04      ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
% 27.52/4.04      inference(cnf_transformation,[],[f30]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_135384,plain,
% 27.52/4.04      ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK2,sK3) ),
% 27.52/4.04      inference(demodulation,[status(thm)],[c_131966,c_9]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_78,plain,( X0 = X0 ),theory(equality) ).
% 27.52/4.04  
% 27.52/4.04  cnf(c_569,plain,
% 27.52/4.04      ( k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK1,sK2,sK3) ),
% 27.52/4.04      inference(instantiation,[status(thm)],[c_78]) ).
% 27.52/4.04  
% 27.52/4.04  cnf(contradiction,plain,
% 27.52/4.04      ( $false ),
% 27.52/4.04      inference(minisat,[status(thm)],[c_135384,c_569]) ).
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  % SZS output end CNFRefutation for theBenchmark.p
% 27.52/4.04  
% 27.52/4.04  ------                               Statistics
% 27.52/4.04  
% 27.52/4.04  ------ General
% 27.52/4.04  
% 27.52/4.04  abstr_ref_over_cycles:                  0
% 27.52/4.04  abstr_ref_under_cycles:                 0
% 27.52/4.04  gc_basic_clause_elim:                   0
% 27.52/4.04  forced_gc_time:                         0
% 27.52/4.04  parsing_time:                           0.016
% 27.52/4.04  unif_index_cands_time:                  0.
% 27.52/4.04  unif_index_add_time:                    0.
% 27.52/4.04  orderings_time:                         0.
% 27.52/4.04  out_proof_time:                         0.01
% 27.52/4.04  total_time:                             3.174
% 27.52/4.04  num_of_symbols:                         39
% 27.52/4.04  num_of_terms:                           84459
% 27.52/4.04  
% 27.52/4.04  ------ Preprocessing
% 27.52/4.04  
% 27.52/4.04  num_of_splits:                          0
% 27.52/4.04  num_of_split_atoms:                     0
% 27.52/4.04  num_of_reused_defs:                     0
% 27.52/4.04  num_eq_ax_congr_red:                    16
% 27.52/4.04  num_of_sem_filtered_clauses:            1
% 27.52/4.04  num_of_subtypes:                        0
% 27.52/4.04  monotx_restored_types:                  0
% 27.52/4.04  sat_num_of_epr_types:                   0
% 27.52/4.04  sat_num_of_non_cyclic_types:            0
% 27.52/4.04  sat_guarded_non_collapsed_types:        0
% 27.52/4.04  num_pure_diseq_elim:                    0
% 27.52/4.04  simp_replaced_by:                       0
% 27.52/4.04  res_preprocessed:                       41
% 27.52/4.04  prep_upred:                             0
% 27.52/4.04  prep_unflattend:                        0
% 27.52/4.04  smt_new_axioms:                         0
% 27.52/4.04  pred_elim_cands:                        1
% 27.52/4.04  pred_elim:                              0
% 27.52/4.04  pred_elim_cl:                           0
% 27.52/4.04  pred_elim_cycles:                       1
% 27.52/4.04  merged_defs:                            0
% 27.52/4.04  merged_defs_ncl:                        0
% 27.52/4.04  bin_hyper_res:                          0
% 27.52/4.04  prep_cycles:                            3
% 27.52/4.04  pred_elim_time:                         0.
% 27.52/4.04  splitting_time:                         0.
% 27.52/4.04  sem_filter_time:                        0.
% 27.52/4.04  monotx_time:                            0.001
% 27.52/4.04  subtype_inf_time:                       0.
% 27.52/4.04  
% 27.52/4.04  ------ Problem properties
% 27.52/4.04  
% 27.52/4.04  clauses:                                10
% 27.52/4.04  conjectures:                            1
% 27.52/4.04  epr:                                    0
% 27.52/4.04  horn:                                   8
% 27.52/4.04  ground:                                 1
% 27.52/4.04  unary:                                  4
% 27.52/4.04  binary:                                 2
% 27.52/4.04  lits:                                   21
% 27.52/4.04  lits_eq:                                7
% 27.52/4.04  fd_pure:                                0
% 27.52/4.04  fd_pseudo:                              0
% 27.52/4.04  fd_cond:                                0
% 27.52/4.04  fd_pseudo_cond:                         3
% 27.52/4.04  ac_symbols:                             0
% 27.52/4.04  
% 27.52/4.04  ------ Propositional Solver
% 27.52/4.04  
% 27.52/4.04  prop_solver_calls:                      32
% 27.52/4.04  prop_fast_solver_calls:                 1050
% 27.52/4.04  smt_solver_calls:                       0
% 27.52/4.04  smt_fast_solver_calls:                  0
% 27.52/4.04  prop_num_of_clauses:                    18251
% 27.52/4.04  prop_preprocess_simplified:             19544
% 27.52/4.04  prop_fo_subsumed:                       1
% 27.52/4.04  prop_solver_time:                       0.
% 27.52/4.04  smt_solver_time:                        0.
% 27.52/4.04  smt_fast_solver_time:                   0.
% 27.52/4.04  prop_fast_solver_time:                  0.
% 27.52/4.04  prop_unsat_core_time:                   0.001
% 27.52/4.04  
% 27.52/4.04  ------ QBF
% 27.52/4.04  
% 27.52/4.04  qbf_q_res:                              0
% 27.52/4.04  qbf_num_tautologies:                    0
% 27.52/4.04  qbf_prep_cycles:                        0
% 27.52/4.04  
% 27.52/4.04  ------ BMC1
% 27.52/4.04  
% 27.52/4.04  bmc1_current_bound:                     -1
% 27.52/4.04  bmc1_last_solved_bound:                 -1
% 27.52/4.04  bmc1_unsat_core_size:                   -1
% 27.52/4.04  bmc1_unsat_core_parents_size:           -1
% 27.52/4.04  bmc1_merge_next_fun:                    0
% 27.52/4.04  bmc1_unsat_core_clauses_time:           0.
% 27.52/4.04  
% 27.52/4.04  ------ Instantiation
% 27.52/4.04  
% 27.52/4.04  inst_num_of_clauses:                    2305
% 27.52/4.04  inst_num_in_passive:                    137
% 27.52/4.04  inst_num_in_active:                     1166
% 27.52/4.04  inst_num_in_unprocessed:                1002
% 27.52/4.04  inst_num_of_loops:                      1780
% 27.52/4.04  inst_num_of_learning_restarts:          0
% 27.52/4.04  inst_num_moves_active_passive:          606
% 27.52/4.04  inst_lit_activity:                      0
% 27.52/4.04  inst_lit_activity_moves:                0
% 27.52/4.04  inst_num_tautologies:                   0
% 27.52/4.04  inst_num_prop_implied:                  0
% 27.52/4.04  inst_num_existing_simplified:           0
% 27.52/4.04  inst_num_eq_res_simplified:             0
% 27.52/4.04  inst_num_child_elim:                    0
% 27.52/4.04  inst_num_of_dismatching_blockings:      4145
% 27.52/4.04  inst_num_of_non_proper_insts:           4689
% 27.52/4.04  inst_num_of_duplicates:                 0
% 27.52/4.04  inst_inst_num_from_inst_to_res:         0
% 27.52/4.04  inst_dismatching_checking_time:         0.
% 27.52/4.04  
% 27.52/4.04  ------ Resolution
% 27.52/4.04  
% 27.52/4.04  res_num_of_clauses:                     0
% 27.52/4.04  res_num_in_passive:                     0
% 27.52/4.04  res_num_in_active:                      0
% 27.52/4.04  res_num_of_loops:                       44
% 27.52/4.04  res_forward_subset_subsumed:            1417
% 27.52/4.04  res_backward_subset_subsumed:           0
% 27.52/4.04  res_forward_subsumed:                   0
% 27.52/4.04  res_backward_subsumed:                  0
% 27.52/4.04  res_forward_subsumption_resolution:     0
% 27.52/4.04  res_backward_subsumption_resolution:    0
% 27.52/4.04  res_clause_to_clause_subsumption:       249881
% 27.52/4.04  res_orphan_elimination:                 0
% 27.52/4.04  res_tautology_del:                      731
% 27.52/4.04  res_num_eq_res_simplified:              0
% 27.52/4.04  res_num_sel_changes:                    0
% 27.52/4.04  res_moves_from_active_to_pass:          0
% 27.52/4.04  
% 27.52/4.04  ------ Superposition
% 27.52/4.04  
% 27.52/4.04  sup_time_total:                         0.
% 27.52/4.04  sup_time_generating:                    0.
% 27.52/4.04  sup_time_sim_full:                      0.
% 27.52/4.04  sup_time_sim_immed:                     0.
% 27.52/4.04  
% 27.52/4.04  sup_num_of_clauses:                     5944
% 27.52/4.04  sup_num_in_active:                      275
% 27.52/4.04  sup_num_in_passive:                     5669
% 27.52/4.04  sup_num_of_loops:                       355
% 27.52/4.04  sup_fw_superposition:                   7880
% 27.52/4.04  sup_bw_superposition:                   15527
% 27.52/4.04  sup_immediate_simplified:               11131
% 27.52/4.04  sup_given_eliminated:                   5
% 27.52/4.04  comparisons_done:                       0
% 27.52/4.04  comparisons_avoided:                    0
% 27.52/4.04  
% 27.52/4.04  ------ Simplifications
% 27.52/4.04  
% 27.52/4.04  
% 27.52/4.04  sim_fw_subset_subsumed:                 685
% 27.52/4.04  sim_bw_subset_subsumed:                 61
% 27.52/4.04  sim_fw_subsumed:                        2043
% 27.52/4.04  sim_bw_subsumed:                        245
% 27.52/4.04  sim_fw_subsumption_res:                 327
% 27.52/4.04  sim_bw_subsumption_res:                 50
% 27.52/4.04  sim_tautology_del:                      582
% 27.52/4.04  sim_eq_tautology_del:                   770
% 27.52/4.04  sim_eq_res_simp:                        128
% 27.52/4.04  sim_fw_demodulated:                     7687
% 27.52/4.04  sim_bw_demodulated:                     109
% 27.52/4.04  sim_light_normalised:                   3002
% 27.52/4.04  sim_joinable_taut:                      0
% 27.52/4.04  sim_joinable_simp:                      0
% 27.52/4.04  sim_ac_normalised:                      0
% 27.52/4.04  sim_smt_subsumption:                    0
% 27.52/4.04  
%------------------------------------------------------------------------------
