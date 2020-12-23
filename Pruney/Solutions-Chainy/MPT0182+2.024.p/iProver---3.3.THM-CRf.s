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
% DateTime   : Thu Dec  3 11:27:44 EST 2020

% Result     : Theorem 27.52s
% Output     : CNFRefutation 27.52s
% Verified   : 
% Statistics : Number of formulae       :  125 (103872 expanded)
%              Number of clauses        :   90 (17034 expanded)
%              Number of leaves         :   11 (30637 expanded)
%              Depth                    :   44
%              Number of atoms          :  288 (243245 expanded)
%              Number of equality atoms :  202 (118810 expanded)
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
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f16])).

fof(f30,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
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

cnf(c_498,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
    | r2_hidden(X0,k2_xboole_0(k1_enumset1(X4,X1,X2),k1_enumset1(X3,X3,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_191])).

cnf(c_0,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_497,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_639,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_497,c_7])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_190,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_637,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_190])).

cnf(c_967,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top
    | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_637])).

cnf(c_1708,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top
    | r2_hidden(X0,k1_enumset1(X2,X1,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_967])).

cnf(c_3140,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X2
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X1) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X2) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),k1_enumset1(X3,X0,X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_192,c_1708])).

cnf(c_35611,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3140])).

cnf(c_35620,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35611])).

cnf(c_8,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_35624,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = X3
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_35620,c_8])).

cnf(c_664,plain,
    ( k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_639,c_497])).

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

cnf(c_2423,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X3
    | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X3) != iProver_top
    | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_190,c_194])).

cnf(c_5165,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3))) = X4
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
    | r2_hidden(sK0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_2423])).

cnf(c_5219,plain,
    ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5165,c_664])).

cnf(c_9869,plain,
    ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k1_enumset1(X1,X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_190,c_5219])).

cnf(c_37582,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35624,c_9869])).

cnf(c_37626,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37582,c_35624])).

cnf(c_37627,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37626,c_8])).

cnf(c_49401,plain,
    ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37627,c_9869])).

cnf(c_49415,plain,
    ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_49401,c_37627])).

cnf(c_496,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k3_enumset1(X0,X0,X1,X1,X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_517,plain,
    ( k3_enumset1(X0,X0,X1,X1,X1) = k1_enumset1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_496,c_0])).

cnf(c_494,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
    | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_190])).

cnf(c_521,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X2,X3,X4)) = iProver_top
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_494,c_8])).

cnf(c_2424,plain,
    ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X3,X4)) = X5
    | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),X5) != iProver_top
    | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_194])).

cnf(c_12878,plain,
    ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X2,X2)) = X3
    | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X2,X2),X3),X3) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_517,c_2424])).

cnf(c_12895,plain,
    ( k2_xboole_0(X0,k1_enumset1(X1,X1,X2)) = X3
    | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),X3) != iProver_top
    | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12878,c_517])).

cnf(c_37587,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35624,c_12895])).

cnf(c_37599,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37587,c_35624])).

cnf(c_329,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_37600,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37599,c_0,c_329])).

cnf(c_38518,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37600,c_194])).

cnf(c_38533,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37600,c_637])).

cnf(c_38584,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38518,c_38533])).

cnf(c_38585,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_38584,c_0])).

cnf(c_38820,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) ),
    inference(superposition,[status(thm)],[c_38585,c_7])).

cnf(c_38834,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_38585,c_497])).

cnf(c_39158,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_38820,c_38834])).

cnf(c_663,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_639,c_8])).

cnf(c_38724,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_38585,c_663])).

cnf(c_38821,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_38585,c_8])).

cnf(c_39160,plain,
    ( k3_enumset1(X0,X0,X1,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_39158,c_38821])).

cnf(c_39467,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_38724,c_39160])).

cnf(c_39469,plain,
    ( k3_enumset1(X0,X0,X1,X2,X2) = k1_enumset1(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_39467,c_8,c_497])).

cnf(c_49416,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(demodulation,[status(thm)],[c_49415,c_39158,c_39469])).

cnf(c_38621,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[status(thm)],[c_38585,c_0])).

cnf(c_40456,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[status(thm)],[c_38621,c_8])).

cnf(c_50022,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_49416,c_40456])).

cnf(c_49374,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37627,c_194])).

cnf(c_49483,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49374,c_8])).

cnf(c_501,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_49878,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k3_enumset1(X1,X1,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_49416,c_501])).

cnf(c_50879,plain,
    ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_49878,c_38834])).

cnf(c_75046,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X1,X2)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49483,c_50879])).

cnf(c_75084,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_50022,c_75046])).

cnf(c_75109,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_75084,c_329])).

cnf(c_123017,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3140,c_75109])).

cnf(c_123117,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_123017,c_75109])).

cnf(c_123118,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
    | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
    | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X1,X0,X0)),k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_123117,c_0])).

cnf(c_124632,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
    | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_123118,c_194])).

cnf(c_49879,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k2_xboole_0(k1_enumset1(X1,X0,X0),k1_enumset1(X2,X2,X2)) ),
    inference(superposition,[status(thm)],[c_49416,c_7])).

cnf(c_50876,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X2) ),
    inference(demodulation,[status(thm)],[c_49879,c_8,c_38834])).

cnf(c_56743,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X0)) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[status(thm)],[c_49416,c_50876])).

cnf(c_70061,plain,
    ( k3_enumset1(X0,X0,X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[status(thm)],[c_56743,c_8])).

cnf(c_70722,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
    | r2_hidden(X0,k1_enumset1(X2,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_70061,c_521])).

cnf(c_124646,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
    | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
    | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_123118,c_70722])).

cnf(c_124761,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
    | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X1,X0,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_124632,c_124646])).

cnf(c_124762,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
    | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(demodulation,[status(thm)],[c_124761,c_0])).

cnf(c_50024,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_49416,c_38585])).

cnf(c_125557,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[status(thm)],[c_124762,c_50024])).

cnf(c_126313,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_125557,c_38585])).

cnf(c_131280,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X0),k1_enumset1(X2,X2,X2)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[status(thm)],[c_126313,c_7])).

cnf(c_50021,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X0),k1_enumset1(X2,X2,X2)) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_49416,c_38834])).

cnf(c_132882,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_131280,c_0,c_50021])).

cnf(c_9,negated_conjecture,
    ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_138052,plain,
    ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_132882,c_9])).

cnf(c_78,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_575,plain,
    ( k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_138052,c_575])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.52/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.52/4.00  
% 27.52/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.52/4.00  
% 27.52/4.00  ------  iProver source info
% 27.52/4.00  
% 27.52/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.52/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.52/4.00  git: non_committed_changes: false
% 27.52/4.00  git: last_make_outside_of_git: false
% 27.52/4.00  
% 27.52/4.00  ------ 
% 27.52/4.00  
% 27.52/4.00  ------ Input Options
% 27.52/4.00  
% 27.52/4.00  --out_options                           all
% 27.52/4.00  --tptp_safe_out                         true
% 27.52/4.00  --problem_path                          ""
% 27.52/4.00  --include_path                          ""
% 27.52/4.00  --clausifier                            res/vclausify_rel
% 27.52/4.00  --clausifier_options                    --mode clausify
% 27.52/4.00  --stdin                                 false
% 27.52/4.00  --stats_out                             all
% 27.52/4.00  
% 27.52/4.00  ------ General Options
% 27.52/4.00  
% 27.52/4.00  --fof                                   false
% 27.52/4.00  --time_out_real                         305.
% 27.52/4.00  --time_out_virtual                      -1.
% 27.52/4.00  --symbol_type_check                     false
% 27.52/4.00  --clausify_out                          false
% 27.52/4.00  --sig_cnt_out                           false
% 27.52/4.00  --trig_cnt_out                          false
% 27.52/4.00  --trig_cnt_out_tolerance                1.
% 27.52/4.00  --trig_cnt_out_sk_spl                   false
% 27.52/4.00  --abstr_cl_out                          false
% 27.52/4.00  
% 27.52/4.00  ------ Global Options
% 27.52/4.00  
% 27.52/4.00  --schedule                              default
% 27.52/4.00  --add_important_lit                     false
% 27.52/4.00  --prop_solver_per_cl                    1000
% 27.52/4.00  --min_unsat_core                        false
% 27.52/4.00  --soft_assumptions                      false
% 27.52/4.00  --soft_lemma_size                       3
% 27.52/4.00  --prop_impl_unit_size                   0
% 27.52/4.00  --prop_impl_unit                        []
% 27.52/4.00  --share_sel_clauses                     true
% 27.52/4.00  --reset_solvers                         false
% 27.52/4.00  --bc_imp_inh                            [conj_cone]
% 27.52/4.00  --conj_cone_tolerance                   3.
% 27.52/4.00  --extra_neg_conj                        none
% 27.52/4.00  --large_theory_mode                     true
% 27.52/4.00  --prolific_symb_bound                   200
% 27.52/4.00  --lt_threshold                          2000
% 27.52/4.00  --clause_weak_htbl                      true
% 27.52/4.00  --gc_record_bc_elim                     false
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing Options
% 27.52/4.00  
% 27.52/4.00  --preprocessing_flag                    true
% 27.52/4.00  --time_out_prep_mult                    0.1
% 27.52/4.00  --splitting_mode                        input
% 27.52/4.00  --splitting_grd                         true
% 27.52/4.00  --splitting_cvd                         false
% 27.52/4.00  --splitting_cvd_svl                     false
% 27.52/4.00  --splitting_nvd                         32
% 27.52/4.00  --sub_typing                            true
% 27.52/4.00  --prep_gs_sim                           true
% 27.52/4.00  --prep_unflatten                        true
% 27.52/4.00  --prep_res_sim                          true
% 27.52/4.00  --prep_upred                            true
% 27.52/4.00  --prep_sem_filter                       exhaustive
% 27.52/4.00  --prep_sem_filter_out                   false
% 27.52/4.00  --pred_elim                             true
% 27.52/4.00  --res_sim_input                         true
% 27.52/4.00  --eq_ax_congr_red                       true
% 27.52/4.00  --pure_diseq_elim                       true
% 27.52/4.00  --brand_transform                       false
% 27.52/4.00  --non_eq_to_eq                          false
% 27.52/4.00  --prep_def_merge                        true
% 27.52/4.00  --prep_def_merge_prop_impl              false
% 27.52/4.00  --prep_def_merge_mbd                    true
% 27.52/4.00  --prep_def_merge_tr_red                 false
% 27.52/4.00  --prep_def_merge_tr_cl                  false
% 27.52/4.00  --smt_preprocessing                     true
% 27.52/4.00  --smt_ac_axioms                         fast
% 27.52/4.00  --preprocessed_out                      false
% 27.52/4.00  --preprocessed_stats                    false
% 27.52/4.00  
% 27.52/4.00  ------ Abstraction refinement Options
% 27.52/4.00  
% 27.52/4.00  --abstr_ref                             []
% 27.52/4.00  --abstr_ref_prep                        false
% 27.52/4.00  --abstr_ref_until_sat                   false
% 27.52/4.00  --abstr_ref_sig_restrict                funpre
% 27.52/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.52/4.00  --abstr_ref_under                       []
% 27.52/4.00  
% 27.52/4.00  ------ SAT Options
% 27.52/4.00  
% 27.52/4.00  --sat_mode                              false
% 27.52/4.00  --sat_fm_restart_options                ""
% 27.52/4.00  --sat_gr_def                            false
% 27.52/4.00  --sat_epr_types                         true
% 27.52/4.00  --sat_non_cyclic_types                  false
% 27.52/4.00  --sat_finite_models                     false
% 27.52/4.00  --sat_fm_lemmas                         false
% 27.52/4.00  --sat_fm_prep                           false
% 27.52/4.00  --sat_fm_uc_incr                        true
% 27.52/4.00  --sat_out_model                         small
% 27.52/4.00  --sat_out_clauses                       false
% 27.52/4.00  
% 27.52/4.00  ------ QBF Options
% 27.52/4.00  
% 27.52/4.00  --qbf_mode                              false
% 27.52/4.00  --qbf_elim_univ                         false
% 27.52/4.00  --qbf_dom_inst                          none
% 27.52/4.00  --qbf_dom_pre_inst                      false
% 27.52/4.00  --qbf_sk_in                             false
% 27.52/4.00  --qbf_pred_elim                         true
% 27.52/4.00  --qbf_split                             512
% 27.52/4.00  
% 27.52/4.00  ------ BMC1 Options
% 27.52/4.00  
% 27.52/4.00  --bmc1_incremental                      false
% 27.52/4.00  --bmc1_axioms                           reachable_all
% 27.52/4.00  --bmc1_min_bound                        0
% 27.52/4.00  --bmc1_max_bound                        -1
% 27.52/4.00  --bmc1_max_bound_default                -1
% 27.52/4.00  --bmc1_symbol_reachability              true
% 27.52/4.00  --bmc1_property_lemmas                  false
% 27.52/4.00  --bmc1_k_induction                      false
% 27.52/4.00  --bmc1_non_equiv_states                 false
% 27.52/4.00  --bmc1_deadlock                         false
% 27.52/4.00  --bmc1_ucm                              false
% 27.52/4.00  --bmc1_add_unsat_core                   none
% 27.52/4.00  --bmc1_unsat_core_children              false
% 27.52/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.52/4.00  --bmc1_out_stat                         full
% 27.52/4.00  --bmc1_ground_init                      false
% 27.52/4.00  --bmc1_pre_inst_next_state              false
% 27.52/4.00  --bmc1_pre_inst_state                   false
% 27.52/4.00  --bmc1_pre_inst_reach_state             false
% 27.52/4.00  --bmc1_out_unsat_core                   false
% 27.52/4.00  --bmc1_aig_witness_out                  false
% 27.52/4.00  --bmc1_verbose                          false
% 27.52/4.00  --bmc1_dump_clauses_tptp                false
% 27.52/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.52/4.00  --bmc1_dump_file                        -
% 27.52/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.52/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.52/4.00  --bmc1_ucm_extend_mode                  1
% 27.52/4.00  --bmc1_ucm_init_mode                    2
% 27.52/4.00  --bmc1_ucm_cone_mode                    none
% 27.52/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.52/4.00  --bmc1_ucm_relax_model                  4
% 27.52/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.52/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.52/4.00  --bmc1_ucm_layered_model                none
% 27.52/4.00  --bmc1_ucm_max_lemma_size               10
% 27.52/4.00  
% 27.52/4.00  ------ AIG Options
% 27.52/4.00  
% 27.52/4.00  --aig_mode                              false
% 27.52/4.00  
% 27.52/4.00  ------ Instantiation Options
% 27.52/4.00  
% 27.52/4.00  --instantiation_flag                    true
% 27.52/4.00  --inst_sos_flag                         false
% 27.52/4.00  --inst_sos_phase                        true
% 27.52/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.52/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.52/4.00  --inst_lit_sel_side                     num_symb
% 27.52/4.00  --inst_solver_per_active                1400
% 27.52/4.00  --inst_solver_calls_frac                1.
% 27.52/4.00  --inst_passive_queue_type               priority_queues
% 27.52/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.52/4.00  --inst_passive_queues_freq              [25;2]
% 27.52/4.00  --inst_dismatching                      true
% 27.52/4.00  --inst_eager_unprocessed_to_passive     true
% 27.52/4.00  --inst_prop_sim_given                   true
% 27.52/4.00  --inst_prop_sim_new                     false
% 27.52/4.00  --inst_subs_new                         false
% 27.52/4.00  --inst_eq_res_simp                      false
% 27.52/4.00  --inst_subs_given                       false
% 27.52/4.00  --inst_orphan_elimination               true
% 27.52/4.00  --inst_learning_loop_flag               true
% 27.52/4.00  --inst_learning_start                   3000
% 27.52/4.00  --inst_learning_factor                  2
% 27.52/4.00  --inst_start_prop_sim_after_learn       3
% 27.52/4.00  --inst_sel_renew                        solver
% 27.52/4.00  --inst_lit_activity_flag                true
% 27.52/4.00  --inst_restr_to_given                   false
% 27.52/4.00  --inst_activity_threshold               500
% 27.52/4.00  --inst_out_proof                        true
% 27.52/4.00  
% 27.52/4.00  ------ Resolution Options
% 27.52/4.00  
% 27.52/4.00  --resolution_flag                       true
% 27.52/4.00  --res_lit_sel                           adaptive
% 27.52/4.00  --res_lit_sel_side                      none
% 27.52/4.00  --res_ordering                          kbo
% 27.52/4.00  --res_to_prop_solver                    active
% 27.52/4.00  --res_prop_simpl_new                    false
% 27.52/4.00  --res_prop_simpl_given                  true
% 27.52/4.00  --res_passive_queue_type                priority_queues
% 27.52/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.52/4.00  --res_passive_queues_freq               [15;5]
% 27.52/4.00  --res_forward_subs                      full
% 27.52/4.00  --res_backward_subs                     full
% 27.52/4.00  --res_forward_subs_resolution           true
% 27.52/4.00  --res_backward_subs_resolution          true
% 27.52/4.00  --res_orphan_elimination                true
% 27.52/4.00  --res_time_limit                        2.
% 27.52/4.00  --res_out_proof                         true
% 27.52/4.00  
% 27.52/4.00  ------ Superposition Options
% 27.52/4.00  
% 27.52/4.00  --superposition_flag                    true
% 27.52/4.00  --sup_passive_queue_type                priority_queues
% 27.52/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.52/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.52/4.00  --demod_completeness_check              fast
% 27.52/4.00  --demod_use_ground                      true
% 27.52/4.00  --sup_to_prop_solver                    passive
% 27.52/4.00  --sup_prop_simpl_new                    true
% 27.52/4.00  --sup_prop_simpl_given                  true
% 27.52/4.00  --sup_fun_splitting                     false
% 27.52/4.00  --sup_smt_interval                      50000
% 27.52/4.00  
% 27.52/4.00  ------ Superposition Simplification Setup
% 27.52/4.00  
% 27.52/4.00  --sup_indices_passive                   []
% 27.52/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.52/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.00  --sup_full_bw                           [BwDemod]
% 27.52/4.00  --sup_immed_triv                        [TrivRules]
% 27.52/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.00  --sup_immed_bw_main                     []
% 27.52/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.52/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.00  
% 27.52/4.00  ------ Combination Options
% 27.52/4.00  
% 27.52/4.00  --comb_res_mult                         3
% 27.52/4.00  --comb_sup_mult                         2
% 27.52/4.00  --comb_inst_mult                        10
% 27.52/4.00  
% 27.52/4.00  ------ Debug Options
% 27.52/4.00  
% 27.52/4.00  --dbg_backtrace                         false
% 27.52/4.00  --dbg_dump_prop_clauses                 false
% 27.52/4.00  --dbg_dump_prop_clauses_file            -
% 27.52/4.00  --dbg_out_stat                          false
% 27.52/4.00  ------ Parsing...
% 27.52/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.52/4.00  ------ Proving...
% 27.52/4.00  ------ Problem Properties 
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  clauses                                 10
% 27.52/4.00  conjectures                             1
% 27.52/4.00  EPR                                     0
% 27.52/4.00  Horn                                    8
% 27.52/4.00  unary                                   4
% 27.52/4.00  binary                                  2
% 27.52/4.00  lits                                    21
% 27.52/4.00  lits eq                                 7
% 27.52/4.00  fd_pure                                 0
% 27.52/4.00  fd_pseudo                               0
% 27.52/4.00  fd_cond                                 0
% 27.52/4.00  fd_pseudo_cond                          3
% 27.52/4.00  AC symbols                              0
% 27.52/4.00  
% 27.52/4.00  ------ Schedule dynamic 5 is on 
% 27.52/4.00  
% 27.52/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  ------ 
% 27.52/4.00  Current options:
% 27.52/4.00  ------ 
% 27.52/4.00  
% 27.52/4.00  ------ Input Options
% 27.52/4.00  
% 27.52/4.00  --out_options                           all
% 27.52/4.00  --tptp_safe_out                         true
% 27.52/4.00  --problem_path                          ""
% 27.52/4.00  --include_path                          ""
% 27.52/4.00  --clausifier                            res/vclausify_rel
% 27.52/4.00  --clausifier_options                    --mode clausify
% 27.52/4.00  --stdin                                 false
% 27.52/4.00  --stats_out                             all
% 27.52/4.00  
% 27.52/4.00  ------ General Options
% 27.52/4.00  
% 27.52/4.00  --fof                                   false
% 27.52/4.00  --time_out_real                         305.
% 27.52/4.00  --time_out_virtual                      -1.
% 27.52/4.00  --symbol_type_check                     false
% 27.52/4.00  --clausify_out                          false
% 27.52/4.00  --sig_cnt_out                           false
% 27.52/4.00  --trig_cnt_out                          false
% 27.52/4.00  --trig_cnt_out_tolerance                1.
% 27.52/4.00  --trig_cnt_out_sk_spl                   false
% 27.52/4.00  --abstr_cl_out                          false
% 27.52/4.00  
% 27.52/4.00  ------ Global Options
% 27.52/4.00  
% 27.52/4.00  --schedule                              default
% 27.52/4.00  --add_important_lit                     false
% 27.52/4.00  --prop_solver_per_cl                    1000
% 27.52/4.00  --min_unsat_core                        false
% 27.52/4.00  --soft_assumptions                      false
% 27.52/4.00  --soft_lemma_size                       3
% 27.52/4.00  --prop_impl_unit_size                   0
% 27.52/4.00  --prop_impl_unit                        []
% 27.52/4.00  --share_sel_clauses                     true
% 27.52/4.00  --reset_solvers                         false
% 27.52/4.00  --bc_imp_inh                            [conj_cone]
% 27.52/4.00  --conj_cone_tolerance                   3.
% 27.52/4.00  --extra_neg_conj                        none
% 27.52/4.00  --large_theory_mode                     true
% 27.52/4.00  --prolific_symb_bound                   200
% 27.52/4.00  --lt_threshold                          2000
% 27.52/4.00  --clause_weak_htbl                      true
% 27.52/4.00  --gc_record_bc_elim                     false
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing Options
% 27.52/4.00  
% 27.52/4.00  --preprocessing_flag                    true
% 27.52/4.00  --time_out_prep_mult                    0.1
% 27.52/4.00  --splitting_mode                        input
% 27.52/4.00  --splitting_grd                         true
% 27.52/4.00  --splitting_cvd                         false
% 27.52/4.00  --splitting_cvd_svl                     false
% 27.52/4.00  --splitting_nvd                         32
% 27.52/4.00  --sub_typing                            true
% 27.52/4.00  --prep_gs_sim                           true
% 27.52/4.00  --prep_unflatten                        true
% 27.52/4.00  --prep_res_sim                          true
% 27.52/4.00  --prep_upred                            true
% 27.52/4.00  --prep_sem_filter                       exhaustive
% 27.52/4.00  --prep_sem_filter_out                   false
% 27.52/4.00  --pred_elim                             true
% 27.52/4.00  --res_sim_input                         true
% 27.52/4.00  --eq_ax_congr_red                       true
% 27.52/4.00  --pure_diseq_elim                       true
% 27.52/4.00  --brand_transform                       false
% 27.52/4.00  --non_eq_to_eq                          false
% 27.52/4.00  --prep_def_merge                        true
% 27.52/4.00  --prep_def_merge_prop_impl              false
% 27.52/4.00  --prep_def_merge_mbd                    true
% 27.52/4.00  --prep_def_merge_tr_red                 false
% 27.52/4.00  --prep_def_merge_tr_cl                  false
% 27.52/4.00  --smt_preprocessing                     true
% 27.52/4.00  --smt_ac_axioms                         fast
% 27.52/4.00  --preprocessed_out                      false
% 27.52/4.00  --preprocessed_stats                    false
% 27.52/4.00  
% 27.52/4.00  ------ Abstraction refinement Options
% 27.52/4.00  
% 27.52/4.00  --abstr_ref                             []
% 27.52/4.00  --abstr_ref_prep                        false
% 27.52/4.00  --abstr_ref_until_sat                   false
% 27.52/4.00  --abstr_ref_sig_restrict                funpre
% 27.52/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.52/4.00  --abstr_ref_under                       []
% 27.52/4.00  
% 27.52/4.00  ------ SAT Options
% 27.52/4.00  
% 27.52/4.00  --sat_mode                              false
% 27.52/4.00  --sat_fm_restart_options                ""
% 27.52/4.00  --sat_gr_def                            false
% 27.52/4.00  --sat_epr_types                         true
% 27.52/4.00  --sat_non_cyclic_types                  false
% 27.52/4.00  --sat_finite_models                     false
% 27.52/4.00  --sat_fm_lemmas                         false
% 27.52/4.00  --sat_fm_prep                           false
% 27.52/4.00  --sat_fm_uc_incr                        true
% 27.52/4.00  --sat_out_model                         small
% 27.52/4.00  --sat_out_clauses                       false
% 27.52/4.00  
% 27.52/4.00  ------ QBF Options
% 27.52/4.00  
% 27.52/4.00  --qbf_mode                              false
% 27.52/4.00  --qbf_elim_univ                         false
% 27.52/4.00  --qbf_dom_inst                          none
% 27.52/4.00  --qbf_dom_pre_inst                      false
% 27.52/4.00  --qbf_sk_in                             false
% 27.52/4.00  --qbf_pred_elim                         true
% 27.52/4.00  --qbf_split                             512
% 27.52/4.00  
% 27.52/4.00  ------ BMC1 Options
% 27.52/4.00  
% 27.52/4.00  --bmc1_incremental                      false
% 27.52/4.00  --bmc1_axioms                           reachable_all
% 27.52/4.00  --bmc1_min_bound                        0
% 27.52/4.00  --bmc1_max_bound                        -1
% 27.52/4.00  --bmc1_max_bound_default                -1
% 27.52/4.00  --bmc1_symbol_reachability              true
% 27.52/4.00  --bmc1_property_lemmas                  false
% 27.52/4.00  --bmc1_k_induction                      false
% 27.52/4.00  --bmc1_non_equiv_states                 false
% 27.52/4.00  --bmc1_deadlock                         false
% 27.52/4.00  --bmc1_ucm                              false
% 27.52/4.00  --bmc1_add_unsat_core                   none
% 27.52/4.00  --bmc1_unsat_core_children              false
% 27.52/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.52/4.00  --bmc1_out_stat                         full
% 27.52/4.00  --bmc1_ground_init                      false
% 27.52/4.00  --bmc1_pre_inst_next_state              false
% 27.52/4.00  --bmc1_pre_inst_state                   false
% 27.52/4.00  --bmc1_pre_inst_reach_state             false
% 27.52/4.00  --bmc1_out_unsat_core                   false
% 27.52/4.00  --bmc1_aig_witness_out                  false
% 27.52/4.00  --bmc1_verbose                          false
% 27.52/4.00  --bmc1_dump_clauses_tptp                false
% 27.52/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.52/4.00  --bmc1_dump_file                        -
% 27.52/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.52/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.52/4.00  --bmc1_ucm_extend_mode                  1
% 27.52/4.00  --bmc1_ucm_init_mode                    2
% 27.52/4.00  --bmc1_ucm_cone_mode                    none
% 27.52/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.52/4.00  --bmc1_ucm_relax_model                  4
% 27.52/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.52/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.52/4.00  --bmc1_ucm_layered_model                none
% 27.52/4.00  --bmc1_ucm_max_lemma_size               10
% 27.52/4.00  
% 27.52/4.00  ------ AIG Options
% 27.52/4.00  
% 27.52/4.00  --aig_mode                              false
% 27.52/4.00  
% 27.52/4.00  ------ Instantiation Options
% 27.52/4.00  
% 27.52/4.00  --instantiation_flag                    true
% 27.52/4.00  --inst_sos_flag                         false
% 27.52/4.00  --inst_sos_phase                        true
% 27.52/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.52/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.52/4.00  --inst_lit_sel_side                     none
% 27.52/4.00  --inst_solver_per_active                1400
% 27.52/4.00  --inst_solver_calls_frac                1.
% 27.52/4.00  --inst_passive_queue_type               priority_queues
% 27.52/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.52/4.00  --inst_passive_queues_freq              [25;2]
% 27.52/4.00  --inst_dismatching                      true
% 27.52/4.00  --inst_eager_unprocessed_to_passive     true
% 27.52/4.00  --inst_prop_sim_given                   true
% 27.52/4.00  --inst_prop_sim_new                     false
% 27.52/4.00  --inst_subs_new                         false
% 27.52/4.00  --inst_eq_res_simp                      false
% 27.52/4.00  --inst_subs_given                       false
% 27.52/4.00  --inst_orphan_elimination               true
% 27.52/4.00  --inst_learning_loop_flag               true
% 27.52/4.00  --inst_learning_start                   3000
% 27.52/4.00  --inst_learning_factor                  2
% 27.52/4.00  --inst_start_prop_sim_after_learn       3
% 27.52/4.00  --inst_sel_renew                        solver
% 27.52/4.00  --inst_lit_activity_flag                true
% 27.52/4.00  --inst_restr_to_given                   false
% 27.52/4.00  --inst_activity_threshold               500
% 27.52/4.00  --inst_out_proof                        true
% 27.52/4.00  
% 27.52/4.00  ------ Resolution Options
% 27.52/4.00  
% 27.52/4.00  --resolution_flag                       false
% 27.52/4.00  --res_lit_sel                           adaptive
% 27.52/4.00  --res_lit_sel_side                      none
% 27.52/4.00  --res_ordering                          kbo
% 27.52/4.00  --res_to_prop_solver                    active
% 27.52/4.00  --res_prop_simpl_new                    false
% 27.52/4.00  --res_prop_simpl_given                  true
% 27.52/4.00  --res_passive_queue_type                priority_queues
% 27.52/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.52/4.00  --res_passive_queues_freq               [15;5]
% 27.52/4.00  --res_forward_subs                      full
% 27.52/4.00  --res_backward_subs                     full
% 27.52/4.00  --res_forward_subs_resolution           true
% 27.52/4.00  --res_backward_subs_resolution          true
% 27.52/4.00  --res_orphan_elimination                true
% 27.52/4.00  --res_time_limit                        2.
% 27.52/4.00  --res_out_proof                         true
% 27.52/4.00  
% 27.52/4.00  ------ Superposition Options
% 27.52/4.00  
% 27.52/4.00  --superposition_flag                    true
% 27.52/4.00  --sup_passive_queue_type                priority_queues
% 27.52/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.52/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.52/4.00  --demod_completeness_check              fast
% 27.52/4.00  --demod_use_ground                      true
% 27.52/4.00  --sup_to_prop_solver                    passive
% 27.52/4.00  --sup_prop_simpl_new                    true
% 27.52/4.00  --sup_prop_simpl_given                  true
% 27.52/4.00  --sup_fun_splitting                     false
% 27.52/4.00  --sup_smt_interval                      50000
% 27.52/4.00  
% 27.52/4.00  ------ Superposition Simplification Setup
% 27.52/4.00  
% 27.52/4.00  --sup_indices_passive                   []
% 27.52/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.52/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.00  --sup_full_bw                           [BwDemod]
% 27.52/4.00  --sup_immed_triv                        [TrivRules]
% 27.52/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.00  --sup_immed_bw_main                     []
% 27.52/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.52/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.52/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.52/4.00  
% 27.52/4.00  ------ Combination Options
% 27.52/4.00  
% 27.52/4.00  --comb_res_mult                         3
% 27.52/4.00  --comb_sup_mult                         2
% 27.52/4.00  --comb_inst_mult                        10
% 27.52/4.00  
% 27.52/4.00  ------ Debug Options
% 27.52/4.00  
% 27.52/4.00  --dbg_backtrace                         false
% 27.52/4.00  --dbg_dump_prop_clauses                 false
% 27.52/4.00  --dbg_dump_prop_clauses_file            -
% 27.52/4.00  --dbg_out_stat                          false
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  ------ Proving...
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  % SZS status Theorem for theBenchmark.p
% 27.52/4.00  
% 27.52/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.52/4.00  
% 27.52/4.00  fof(f1,axiom,(
% 27.52/4.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f11,plain,(
% 27.52/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.00    inference(nnf_transformation,[],[f1])).
% 27.52/4.00  
% 27.52/4.00  fof(f12,plain,(
% 27.52/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.00    inference(flattening,[],[f11])).
% 27.52/4.00  
% 27.52/4.00  fof(f13,plain,(
% 27.52/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.00    inference(rectify,[],[f12])).
% 27.52/4.00  
% 27.52/4.00  fof(f14,plain,(
% 27.52/4.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.52/4.00    introduced(choice_axiom,[])).
% 27.52/4.00  
% 27.52/4.00  fof(f15,plain,(
% 27.52/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.52/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 27.52/4.00  
% 27.52/4.00  fof(f21,plain,(
% 27.52/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f15])).
% 27.52/4.00  
% 27.52/4.00  fof(f3,axiom,(
% 27.52/4.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f25,plain,(
% 27.52/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f3])).
% 27.52/4.00  
% 27.52/4.00  fof(f2,axiom,(
% 27.52/4.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f24,plain,(
% 27.52/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f2])).
% 27.52/4.00  
% 27.52/4.00  fof(f4,axiom,(
% 27.52/4.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f26,plain,(
% 27.52/4.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f4])).
% 27.52/4.00  
% 27.52/4.00  fof(f5,axiom,(
% 27.52/4.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f27,plain,(
% 27.52/4.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f5])).
% 27.52/4.00  
% 27.52/4.00  fof(f31,plain,(
% 27.52/4.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 27.52/4.00    inference(definition_unfolding,[],[f26,f27])).
% 27.52/4.00  
% 27.52/4.00  fof(f32,plain,(
% 27.52/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.52/4.00    inference(definition_unfolding,[],[f24,f31])).
% 27.52/4.00  
% 27.52/4.00  fof(f34,plain,(
% 27.52/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) )),
% 27.52/4.00    inference(definition_unfolding,[],[f25,f31,f32])).
% 27.52/4.00  
% 27.52/4.00  fof(f20,plain,(
% 27.52/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 27.52/4.00    inference(cnf_transformation,[],[f15])).
% 27.52/4.00  
% 27.52/4.00  fof(f36,plain,(
% 27.52/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 27.52/4.00    inference(equality_resolution,[],[f20])).
% 27.52/4.00  
% 27.52/4.00  fof(f6,axiom,(
% 27.52/4.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f28,plain,(
% 27.52/4.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f6])).
% 27.52/4.00  
% 27.52/4.00  fof(f33,plain,(
% 27.52/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 27.52/4.00    inference(definition_unfolding,[],[f28,f32])).
% 27.52/4.00  
% 27.52/4.00  fof(f19,plain,(
% 27.52/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 27.52/4.00    inference(cnf_transformation,[],[f15])).
% 27.52/4.00  
% 27.52/4.00  fof(f37,plain,(
% 27.52/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 27.52/4.00    inference(equality_resolution,[],[f19])).
% 27.52/4.00  
% 27.52/4.00  fof(f7,axiom,(
% 27.52/4.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f29,plain,(
% 27.52/4.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f7])).
% 27.52/4.00  
% 27.52/4.00  fof(f35,plain,(
% 27.52/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.52/4.00    inference(definition_unfolding,[],[f29,f32])).
% 27.52/4.00  
% 27.52/4.00  fof(f23,plain,(
% 27.52/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 27.52/4.00    inference(cnf_transformation,[],[f15])).
% 27.52/4.00  
% 27.52/4.00  fof(f8,conjecture,(
% 27.52/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 27.52/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.52/4.00  
% 27.52/4.00  fof(f9,negated_conjecture,(
% 27.52/4.00    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 27.52/4.00    inference(negated_conjecture,[],[f8])).
% 27.52/4.00  
% 27.52/4.00  fof(f10,plain,(
% 27.52/4.00    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 27.52/4.00    inference(ennf_transformation,[],[f9])).
% 27.52/4.00  
% 27.52/4.00  fof(f16,plain,(
% 27.52/4.00    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 27.52/4.00    introduced(choice_axiom,[])).
% 27.52/4.00  
% 27.52/4.00  fof(f17,plain,(
% 27.52/4.00    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 27.52/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f16])).
% 27.52/4.00  
% 27.52/4.00  fof(f30,plain,(
% 27.52/4.00    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 27.52/4.00    inference(cnf_transformation,[],[f17])).
% 27.52/4.00  
% 27.52/4.00  cnf(c_3,plain,
% 27.52/4.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X0)
% 27.52/4.00      | k2_xboole_0(X0,X1) = X2 ),
% 27.52/4.00      inference(cnf_transformation,[],[f21]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_192,plain,
% 27.52/4.00      ( k2_xboole_0(X0,X1) = X2
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 27.52/4.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_7,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
% 27.52/4.00      inference(cnf_transformation,[],[f34]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_4,plain,
% 27.52/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 27.52/4.00      inference(cnf_transformation,[],[f36]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_191,plain,
% 27.52/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 27.52/4.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_498,plain,
% 27.52/4.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k2_xboole_0(k1_enumset1(X4,X1,X2),k1_enumset1(X3,X3,X3))) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_7,c_191]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_0,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(cnf_transformation,[],[f33]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_497,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_639,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_497,c_7]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_5,plain,
% 27.52/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 27.52/4.00      inference(cnf_transformation,[],[f37]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_190,plain,
% 27.52/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 27.52/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_637,plain,
% 27.52/4.00      ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_497,c_190]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_967,plain,
% 27.52/4.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) = iProver_top
% 27.52/4.00      | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_639,c_637]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_1708,plain,
% 27.52/4.00      ( r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k1_enumset1(X2,X1,X3)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_498,c_967]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_3140,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X2
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X1) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),X2) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),X1,X2),k1_enumset1(X3,X0,X4)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_192,c_1708]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_35611,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top
% 27.52/4.00      | iProver_top != iProver_top ),
% 27.52/4.00      inference(equality_factoring,[status(thm)],[c_3140]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_35620,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = X3
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.00      inference(equality_resolution_simp,[status(thm)],[c_35611]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_8,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
% 27.52/4.00      inference(cnf_transformation,[],[f35]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_35624,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = X3
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),X3) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),X3),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_35620,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_664,plain,
% 27.52/4.00      ( k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_639,c_497]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_1,plain,
% 27.52/4.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 27.52/4.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 27.52/4.00      | k2_xboole_0(X0,X1) = X2 ),
% 27.52/4.00      inference(cnf_transformation,[],[f23]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_194,plain,
% 27.52/4.00      ( k2_xboole_0(X0,X1) = X2
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 27.52/4.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_2423,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X3
% 27.52/4.00      | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X3) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k2_xboole_0(X1,X2),X3),X1) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_190,c_194]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_5165,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3))) = X4
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X3,X3,X3)),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_664,c_2423]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_5219,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) != iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_5165,c_664]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_9869,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k1_enumset1(X1,X2,X3)) = X4
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),X4) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X2,X3),X4),k1_enumset1(X1,X2,X2)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_190,c_5219]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_37582,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_35624,c_9869]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_37626,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.00      inference(forward_subsumption_resolution,
% 27.52/4.00                [status(thm)],
% 27.52/4.00                [c_37582,c_35624]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_37627,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_37626,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49401,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_37627,c_9869]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49415,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X0) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X0)) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.00      inference(forward_subsumption_resolution,
% 27.52/4.00                [status(thm)],
% 27.52/4.00                [c_49401,c_37627]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_496,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k3_enumset1(X0,X0,X1,X1,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_517,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X1,X1) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_496,c_0]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_494,plain,
% 27.52/4.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_7,c_190]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_521,plain,
% 27.52/4.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X2,X3,X4)) = iProver_top
% 27.52/4.00      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_494,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_2424,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X3,X4)) = X5
% 27.52/4.00      | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),X5) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X3,X4),X5),k1_enumset1(X1,X2,X3)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_521,c_194]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_12878,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k3_enumset1(X1,X1,X2,X2,X2)) = X3
% 27.52/4.00      | r2_hidden(sK0(X0,k3_enumset1(X1,X1,X2,X2,X2),X3),X3) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_517,c_2424]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_12895,plain,
% 27.52/4.00      ( k2_xboole_0(X0,k1_enumset1(X1,X1,X2)) = X3
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),X3) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(X0,k1_enumset1(X1,X1,X2),X3),k1_enumset1(X1,X2,X2)) != iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_12878,c_517]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_37587,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_35624,c_12895]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_37599,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.00      inference(forward_subsumption_resolution,
% 27.52/4.00                [status(thm)],
% 27.52/4.00                [c_37587,c_35624]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_329,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_37600,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_37599,c_0,c_329]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38518,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_37600,c_194]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38533,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X2)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_37600,c_637]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38584,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.00      inference(forward_subsumption_resolution,
% 27.52/4.00                [status(thm)],
% 27.52/4.00                [c_38518,c_38533]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38585,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_38584,c_0]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38820,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_38585,c_7]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38834,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_38585,c_497]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_39158,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(light_normalisation,[status(thm)],[c_38820,c_38834]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_663,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X2,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_639,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38724,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_38585,c_663]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38821,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X2)) = k3_enumset1(X0,X0,X1,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_38585,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_39160,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X1,X2) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_39158,c_38821]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_39467,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(light_normalisation,[status(thm)],[c_38724,c_39160]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_39469,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X2,X2) = k1_enumset1(X0,X1,X2) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_39467,c_8,c_497]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49416,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_49415,c_39158,c_39469]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_38621,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_38585,c_0]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_40456,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_38621,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_50022,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k1_enumset1(X1,X0,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_49416,c_40456]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49374,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_37627,c_194]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49483,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2),k1_enumset1(X1,X0,X0)),k1_enumset1(X1,X0,X0)) != iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_49374,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_501,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49878,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X1),k1_enumset1(X2,X2,X2)) = k3_enumset1(X1,X1,X0,X1,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_49416,c_501]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_50879,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X1,X0,X2) = k1_enumset1(X1,X0,X2) ),
% 27.52/4.00      inference(light_normalisation,[status(thm)],[c_49878,c_38834]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_75046,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X1,X2)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_49483,c_50879]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_75084,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_50022,c_75046]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_75109,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_75084,c_329]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_123017,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_3140,c_75109]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_123117,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X1,X1,X0)) = iProver_top ),
% 27.52/4.00      inference(forward_subsumption_resolution,
% 27.52/4.00                [status(thm)],
% 27.52/4.00                [c_123017,c_75109]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_123118,plain,
% 27.52/4.00      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1),k1_enumset1(X1,X0,X0)),k1_enumset1(X0,X0,X1)) = iProver_top ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_123117,c_0]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_124632,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
% 27.52/4.00      | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0)) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) != iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_123118,c_194]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_49879,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k2_xboole_0(k1_enumset1(X1,X0,X0),k1_enumset1(X2,X2,X2)) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_49416,c_7]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_50876,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X0,X2)) = k1_enumset1(X1,X0,X2) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_49879,c_8,c_38834]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_56743,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X0)) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_49416,c_50876]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_70061,plain,
% 27.52/4.00      ( k3_enumset1(X0,X0,X0,X1,X0) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_56743,c_8]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_70722,plain,
% 27.52/4.00      ( r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top
% 27.52/4.00      | r2_hidden(X0,k1_enumset1(X2,X1,X1)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_70061,c_521]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_124646,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
% 27.52/4.00      | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)
% 27.52/4.00      | r2_hidden(sK0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X0),k1_enumset1(X0,X1,X1)),k1_enumset1(X0,X1,X1)) = iProver_top ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_123118,c_70722]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_124761,plain,
% 27.52/4.00      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k1_enumset1(X1,X0,X1) = k1_enumset1(X1,X0,X0)
% 27.52/4.00      | k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) = k1_enumset1(X1,X0,X0) ),
% 27.52/4.00      inference(forward_subsumption_resolution,
% 27.52/4.00                [status(thm)],
% 27.52/4.00                [c_124632,c_124646]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_124762,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X1,X0)
% 27.52/4.00      | k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_124761,c_0]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_50024,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X1,X1,X0) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_49416,c_38585]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_125557,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_124762,c_50024]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_126313,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_125557,c_38585]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_131280,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X0),k1_enumset1(X2,X2,X2)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_126313,c_7]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_50021,plain,
% 27.52/4.00      ( k2_xboole_0(k1_enumset1(X0,X1,X0),k1_enumset1(X2,X2,X2)) = k1_enumset1(X1,X0,X2) ),
% 27.52/4.00      inference(superposition,[status(thm)],[c_49416,c_38834]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_132882,plain,
% 27.52/4.00      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
% 27.52/4.00      inference(light_normalisation,[status(thm)],[c_131280,c_0,c_50021]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_9,negated_conjecture,
% 27.52/4.00      ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
% 27.52/4.00      inference(cnf_transformation,[],[f30]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_138052,plain,
% 27.52/4.00      ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK2,sK3) ),
% 27.52/4.00      inference(demodulation,[status(thm)],[c_132882,c_9]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_78,plain,( X0 = X0 ),theory(equality) ).
% 27.52/4.00  
% 27.52/4.00  cnf(c_575,plain,
% 27.52/4.00      ( k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK1,sK2,sK3) ),
% 27.52/4.00      inference(instantiation,[status(thm)],[c_78]) ).
% 27.52/4.00  
% 27.52/4.00  cnf(contradiction,plain,
% 27.52/4.00      ( $false ),
% 27.52/4.00      inference(minisat,[status(thm)],[c_138052,c_575]) ).
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.52/4.00  
% 27.52/4.00  ------                               Statistics
% 27.52/4.00  
% 27.52/4.00  ------ General
% 27.52/4.00  
% 27.52/4.00  abstr_ref_over_cycles:                  0
% 27.52/4.00  abstr_ref_under_cycles:                 0
% 27.52/4.00  gc_basic_clause_elim:                   0
% 27.52/4.00  forced_gc_time:                         0
% 27.52/4.00  parsing_time:                           0.008
% 27.52/4.00  unif_index_cands_time:                  0.
% 27.52/4.00  unif_index_add_time:                    0.
% 27.52/4.00  orderings_time:                         0.
% 27.52/4.00  out_proof_time:                         0.01
% 27.52/4.00  total_time:                             3.338
% 27.52/4.00  num_of_symbols:                         39
% 27.52/4.00  num_of_terms:                           92970
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing
% 27.52/4.00  
% 27.52/4.00  num_of_splits:                          0
% 27.52/4.00  num_of_split_atoms:                     0
% 27.52/4.00  num_of_reused_defs:                     0
% 27.52/4.00  num_eq_ax_congr_red:                    16
% 27.52/4.00  num_of_sem_filtered_clauses:            1
% 27.52/4.00  num_of_subtypes:                        0
% 27.52/4.00  monotx_restored_types:                  0
% 27.52/4.00  sat_num_of_epr_types:                   0
% 27.52/4.00  sat_num_of_non_cyclic_types:            0
% 27.52/4.00  sat_guarded_non_collapsed_types:        0
% 27.52/4.00  num_pure_diseq_elim:                    0
% 27.52/4.00  simp_replaced_by:                       0
% 27.52/4.00  res_preprocessed:                       41
% 27.52/4.00  prep_upred:                             0
% 27.52/4.00  prep_unflattend:                        0
% 27.52/4.00  smt_new_axioms:                         0
% 27.52/4.00  pred_elim_cands:                        1
% 27.52/4.00  pred_elim:                              0
% 27.52/4.00  pred_elim_cl:                           0
% 27.52/4.00  pred_elim_cycles:                       1
% 27.52/4.00  merged_defs:                            0
% 27.52/4.00  merged_defs_ncl:                        0
% 27.52/4.00  bin_hyper_res:                          0
% 27.52/4.00  prep_cycles:                            3
% 27.52/4.00  pred_elim_time:                         0.
% 27.52/4.00  splitting_time:                         0.
% 27.52/4.00  sem_filter_time:                        0.
% 27.52/4.00  monotx_time:                            0.
% 27.52/4.00  subtype_inf_time:                       0.
% 27.52/4.00  
% 27.52/4.00  ------ Problem properties
% 27.52/4.00  
% 27.52/4.00  clauses:                                10
% 27.52/4.00  conjectures:                            1
% 27.52/4.00  epr:                                    0
% 27.52/4.00  horn:                                   8
% 27.52/4.00  ground:                                 1
% 27.52/4.00  unary:                                  4
% 27.52/4.00  binary:                                 2
% 27.52/4.00  lits:                                   21
% 27.52/4.00  lits_eq:                                7
% 27.52/4.00  fd_pure:                                0
% 27.52/4.00  fd_pseudo:                              0
% 27.52/4.00  fd_cond:                                0
% 27.52/4.00  fd_pseudo_cond:                         3
% 27.52/4.00  ac_symbols:                             0
% 27.52/4.00  
% 27.52/4.00  ------ Propositional Solver
% 27.52/4.00  
% 27.52/4.00  prop_solver_calls:                      32
% 27.52/4.00  prop_fast_solver_calls:                 1055
% 27.52/4.00  smt_solver_calls:                       0
% 27.52/4.00  smt_fast_solver_calls:                  0
% 27.52/4.00  prop_num_of_clauses:                    20639
% 27.52/4.00  prop_preprocess_simplified:             27647
% 27.52/4.00  prop_fo_subsumed:                       1
% 27.52/4.00  prop_solver_time:                       0.
% 27.52/4.00  smt_solver_time:                        0.
% 27.52/4.00  smt_fast_solver_time:                   0.
% 27.52/4.00  prop_fast_solver_time:                  0.
% 27.52/4.00  prop_unsat_core_time:                   0.001
% 27.52/4.00  
% 27.52/4.00  ------ QBF
% 27.52/4.00  
% 27.52/4.00  qbf_q_res:                              0
% 27.52/4.00  qbf_num_tautologies:                    0
% 27.52/4.00  qbf_prep_cycles:                        0
% 27.52/4.00  
% 27.52/4.00  ------ BMC1
% 27.52/4.00  
% 27.52/4.00  bmc1_current_bound:                     -1
% 27.52/4.00  bmc1_last_solved_bound:                 -1
% 27.52/4.00  bmc1_unsat_core_size:                   -1
% 27.52/4.00  bmc1_unsat_core_parents_size:           -1
% 27.52/4.00  bmc1_merge_next_fun:                    0
% 27.52/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.52/4.00  
% 27.52/4.00  ------ Instantiation
% 27.52/4.00  
% 27.52/4.00  inst_num_of_clauses:                    3010
% 27.52/4.00  inst_num_in_passive:                    1423
% 27.52/4.00  inst_num_in_active:                     1251
% 27.52/4.00  inst_num_in_unprocessed:                336
% 27.52/4.00  inst_num_of_loops:                      1790
% 27.52/4.00  inst_num_of_learning_restarts:          0
% 27.52/4.00  inst_num_moves_active_passive:          532
% 27.52/4.00  inst_lit_activity:                      0
% 27.52/4.00  inst_lit_activity_moves:                0
% 27.52/4.00  inst_num_tautologies:                   0
% 27.52/4.00  inst_num_prop_implied:                  0
% 27.52/4.00  inst_num_existing_simplified:           0
% 27.52/4.00  inst_num_eq_res_simplified:             0
% 27.52/4.00  inst_num_child_elim:                    0
% 27.52/4.00  inst_num_of_dismatching_blockings:      3283
% 27.52/4.00  inst_num_of_non_proper_insts:           5455
% 27.52/4.00  inst_num_of_duplicates:                 0
% 27.52/4.00  inst_inst_num_from_inst_to_res:         0
% 27.52/4.00  inst_dismatching_checking_time:         0.
% 27.52/4.00  
% 27.52/4.00  ------ Resolution
% 27.52/4.00  
% 27.52/4.00  res_num_of_clauses:                     0
% 27.52/4.00  res_num_in_passive:                     0
% 27.52/4.00  res_num_in_active:                      0
% 27.52/4.00  res_num_of_loops:                       44
% 27.52/4.00  res_forward_subset_subsumed:            696
% 27.52/4.00  res_backward_subset_subsumed:           2
% 27.52/4.00  res_forward_subsumed:                   0
% 27.52/4.00  res_backward_subsumed:                  0
% 27.52/4.00  res_forward_subsumption_resolution:     0
% 27.52/4.00  res_backward_subsumption_resolution:    0
% 27.52/4.00  res_clause_to_clause_subsumption:       263040
% 27.52/4.00  res_orphan_elimination:                 0
% 27.52/4.00  res_tautology_del:                      572
% 27.52/4.00  res_num_eq_res_simplified:              0
% 27.52/4.00  res_num_sel_changes:                    0
% 27.52/4.00  res_moves_from_active_to_pass:          0
% 27.52/4.00  
% 27.52/4.00  ------ Superposition
% 27.52/4.00  
% 27.52/4.00  sup_time_total:                         0.
% 27.52/4.00  sup_time_generating:                    0.
% 27.52/4.00  sup_time_sim_full:                      0.
% 27.52/4.00  sup_time_sim_immed:                     0.
% 27.52/4.00  
% 27.52/4.00  sup_num_of_clauses:                     6176
% 27.52/4.00  sup_num_in_active:                      277
% 27.52/4.00  sup_num_in_passive:                     5899
% 27.52/4.00  sup_num_of_loops:                       357
% 27.52/4.00  sup_fw_superposition:                   7985
% 27.52/4.00  sup_bw_superposition:                   16416
% 27.52/4.00  sup_immediate_simplified:               11228
% 27.52/4.00  sup_given_eliminated:                   5
% 27.52/4.00  comparisons_done:                       0
% 27.52/4.00  comparisons_avoided:                    0
% 27.52/4.00  
% 27.52/4.00  ------ Simplifications
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  sim_fw_subset_subsumed:                 689
% 27.52/4.00  sim_bw_subset_subsumed:                 61
% 27.52/4.00  sim_fw_subsumed:                        2090
% 27.52/4.00  sim_bw_subsumed:                        254
% 27.52/4.00  sim_fw_subsumption_res:                 346
% 27.52/4.00  sim_bw_subsumption_res:                 50
% 27.52/4.00  sim_tautology_del:                      608
% 27.52/4.00  sim_eq_tautology_del:                   778
% 27.52/4.00  sim_eq_res_simp:                        134
% 27.52/4.00  sim_fw_demodulated:                     7718
% 27.52/4.00  sim_bw_demodulated:                     109
% 27.52/4.00  sim_light_normalised:                   3002
% 27.52/4.00  sim_joinable_taut:                      0
% 27.52/4.00  sim_joinable_simp:                      0
% 27.52/4.00  sim_ac_normalised:                      0
% 27.52/4.00  sim_smt_subsumption:                    0
% 27.52/4.00  
%------------------------------------------------------------------------------
