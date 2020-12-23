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
% DateTime   : Thu Dec  3 11:34:27 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   88 (1469 expanded)
%              Number of clauses        :   41 ( 345 expanded)
%              Number of leaves         :   12 ( 377 expanded)
%              Depth                    :   23
%              Number of atoms          :  223 (5137 expanded)
%              Number of equality atoms :  114 (1742 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f37,f37])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f21])).

fof(f39,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f33,f37,f34,f34])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) ),
    inference(definition_unfolding,[],[f38,f37,f34])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f37])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_264,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_384,plain,
    ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_13])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_262,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1213,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_384,c_262])).

cnf(c_1811,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = X1
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_264,c_1213])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_99,plain,
    ( X0 != X1
    | k3_tarski(k2_tarski(X2,X1)) = X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_100,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_99])).

cnf(c_1212,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_100,c_262])).

cnf(c_2764,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = X1
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1811,c_1212])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_263,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1585,plain,
    ( r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_384,c_263])).

cnf(c_2783,plain,
    ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2764,c_1585])).

cnf(c_2794,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2783,c_384])).

cnf(c_2927,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2794,c_1212])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1208,plain,
    ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
    | r2_hidden(X0,k2_tarski(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_262])).

cnf(c_2932,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(X0,X0)),k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_1208])).

cnf(c_9,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_548,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_12])).

cnf(c_7054,plain,
    ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(X0,X0)),k2_tarski(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2932,c_548])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_265,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2930,plain,
    ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = X0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_265])).

cnf(c_2969,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2930,c_384])).

cnf(c_3095,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2927,c_2969])).

cnf(c_7060,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_tarski(sK1,sK2),k2_tarski(X0,X0)),k2_tarski(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7054,c_3095])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_266,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7067,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK2))) = k2_tarski(sK1,sK1)
    | r2_hidden(sK0(k1_xboole_0,k2_tarski(sK1,sK2),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7060,c_266])).

cnf(c_7084,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK2))) = k2_tarski(sK1,sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7067,c_7060])).

cnf(c_3230,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3095,c_384])).

cnf(c_7085,plain,
    ( k2_tarski(sK1,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7084,c_3230])).

cnf(c_7285,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7085,c_548])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.69/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.01  
% 2.69/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.01  
% 2.69/1.01  ------  iProver source info
% 2.69/1.01  
% 2.69/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.01  git: non_committed_changes: false
% 2.69/1.01  git: last_make_outside_of_git: false
% 2.69/1.01  
% 2.69/1.01  ------ 
% 2.69/1.01  
% 2.69/1.01  ------ Input Options
% 2.69/1.01  
% 2.69/1.01  --out_options                           all
% 2.69/1.01  --tptp_safe_out                         true
% 2.69/1.01  --problem_path                          ""
% 2.69/1.01  --include_path                          ""
% 2.69/1.01  --clausifier                            res/vclausify_rel
% 2.69/1.01  --clausifier_options                    --mode clausify
% 2.69/1.01  --stdin                                 false
% 2.69/1.01  --stats_out                             all
% 2.69/1.01  
% 2.69/1.01  ------ General Options
% 2.69/1.01  
% 2.69/1.01  --fof                                   false
% 2.69/1.01  --time_out_real                         305.
% 2.69/1.01  --time_out_virtual                      -1.
% 2.69/1.01  --symbol_type_check                     false
% 2.69/1.01  --clausify_out                          false
% 2.69/1.01  --sig_cnt_out                           false
% 2.69/1.01  --trig_cnt_out                          false
% 2.69/1.01  --trig_cnt_out_tolerance                1.
% 2.69/1.01  --trig_cnt_out_sk_spl                   false
% 2.69/1.01  --abstr_cl_out                          false
% 2.69/1.01  
% 2.69/1.01  ------ Global Options
% 2.69/1.01  
% 2.69/1.01  --schedule                              default
% 2.69/1.01  --add_important_lit                     false
% 2.69/1.01  --prop_solver_per_cl                    1000
% 2.69/1.01  --min_unsat_core                        false
% 2.69/1.01  --soft_assumptions                      false
% 2.69/1.01  --soft_lemma_size                       3
% 2.69/1.01  --prop_impl_unit_size                   0
% 2.69/1.01  --prop_impl_unit                        []
% 2.69/1.01  --share_sel_clauses                     true
% 2.69/1.01  --reset_solvers                         false
% 2.69/1.01  --bc_imp_inh                            [conj_cone]
% 2.69/1.01  --conj_cone_tolerance                   3.
% 2.69/1.01  --extra_neg_conj                        none
% 2.69/1.01  --large_theory_mode                     true
% 2.69/1.01  --prolific_symb_bound                   200
% 2.69/1.01  --lt_threshold                          2000
% 2.69/1.01  --clause_weak_htbl                      true
% 2.69/1.01  --gc_record_bc_elim                     false
% 2.69/1.01  
% 2.69/1.01  ------ Preprocessing Options
% 2.69/1.01  
% 2.69/1.01  --preprocessing_flag                    true
% 2.69/1.01  --time_out_prep_mult                    0.1
% 2.69/1.01  --splitting_mode                        input
% 2.69/1.01  --splitting_grd                         true
% 2.69/1.01  --splitting_cvd                         false
% 2.69/1.01  --splitting_cvd_svl                     false
% 2.69/1.01  --splitting_nvd                         32
% 2.69/1.01  --sub_typing                            true
% 2.69/1.01  --prep_gs_sim                           true
% 2.69/1.01  --prep_unflatten                        true
% 2.69/1.01  --prep_res_sim                          true
% 2.69/1.01  --prep_upred                            true
% 2.69/1.01  --prep_sem_filter                       exhaustive
% 2.69/1.01  --prep_sem_filter_out                   false
% 2.69/1.01  --pred_elim                             true
% 2.69/1.01  --res_sim_input                         true
% 2.69/1.01  --eq_ax_congr_red                       true
% 2.69/1.01  --pure_diseq_elim                       true
% 2.69/1.01  --brand_transform                       false
% 2.69/1.01  --non_eq_to_eq                          false
% 2.69/1.01  --prep_def_merge                        true
% 2.69/1.01  --prep_def_merge_prop_impl              false
% 2.69/1.01  --prep_def_merge_mbd                    true
% 2.69/1.01  --prep_def_merge_tr_red                 false
% 2.69/1.01  --prep_def_merge_tr_cl                  false
% 2.69/1.01  --smt_preprocessing                     true
% 2.69/1.01  --smt_ac_axioms                         fast
% 2.69/1.01  --preprocessed_out                      false
% 2.69/1.01  --preprocessed_stats                    false
% 2.69/1.01  
% 2.69/1.01  ------ Abstraction refinement Options
% 2.69/1.01  
% 2.69/1.01  --abstr_ref                             []
% 2.69/1.01  --abstr_ref_prep                        false
% 2.69/1.01  --abstr_ref_until_sat                   false
% 2.69/1.01  --abstr_ref_sig_restrict                funpre
% 2.69/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.01  --abstr_ref_under                       []
% 2.69/1.01  
% 2.69/1.01  ------ SAT Options
% 2.69/1.01  
% 2.69/1.01  --sat_mode                              false
% 2.69/1.01  --sat_fm_restart_options                ""
% 2.69/1.01  --sat_gr_def                            false
% 2.69/1.01  --sat_epr_types                         true
% 2.69/1.01  --sat_non_cyclic_types                  false
% 2.69/1.01  --sat_finite_models                     false
% 2.69/1.01  --sat_fm_lemmas                         false
% 2.69/1.01  --sat_fm_prep                           false
% 2.69/1.01  --sat_fm_uc_incr                        true
% 2.69/1.01  --sat_out_model                         small
% 2.69/1.01  --sat_out_clauses                       false
% 2.69/1.01  
% 2.69/1.01  ------ QBF Options
% 2.69/1.01  
% 2.69/1.01  --qbf_mode                              false
% 2.69/1.01  --qbf_elim_univ                         false
% 2.69/1.01  --qbf_dom_inst                          none
% 2.69/1.01  --qbf_dom_pre_inst                      false
% 2.69/1.01  --qbf_sk_in                             false
% 2.69/1.01  --qbf_pred_elim                         true
% 2.69/1.01  --qbf_split                             512
% 2.69/1.01  
% 2.69/1.01  ------ BMC1 Options
% 2.69/1.01  
% 2.69/1.01  --bmc1_incremental                      false
% 2.69/1.01  --bmc1_axioms                           reachable_all
% 2.69/1.01  --bmc1_min_bound                        0
% 2.69/1.01  --bmc1_max_bound                        -1
% 2.69/1.01  --bmc1_max_bound_default                -1
% 2.69/1.01  --bmc1_symbol_reachability              true
% 2.69/1.01  --bmc1_property_lemmas                  false
% 2.69/1.01  --bmc1_k_induction                      false
% 2.69/1.01  --bmc1_non_equiv_states                 false
% 2.69/1.01  --bmc1_deadlock                         false
% 2.69/1.01  --bmc1_ucm                              false
% 2.69/1.01  --bmc1_add_unsat_core                   none
% 2.69/1.01  --bmc1_unsat_core_children              false
% 2.69/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.01  --bmc1_out_stat                         full
% 2.69/1.01  --bmc1_ground_init                      false
% 2.69/1.01  --bmc1_pre_inst_next_state              false
% 2.69/1.01  --bmc1_pre_inst_state                   false
% 2.69/1.01  --bmc1_pre_inst_reach_state             false
% 2.69/1.01  --bmc1_out_unsat_core                   false
% 2.69/1.01  --bmc1_aig_witness_out                  false
% 2.69/1.01  --bmc1_verbose                          false
% 2.69/1.01  --bmc1_dump_clauses_tptp                false
% 2.69/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.01  --bmc1_dump_file                        -
% 2.69/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.01  --bmc1_ucm_extend_mode                  1
% 2.69/1.01  --bmc1_ucm_init_mode                    2
% 2.69/1.01  --bmc1_ucm_cone_mode                    none
% 2.69/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.01  --bmc1_ucm_relax_model                  4
% 2.69/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.01  --bmc1_ucm_layered_model                none
% 2.69/1.01  --bmc1_ucm_max_lemma_size               10
% 2.69/1.01  
% 2.69/1.01  ------ AIG Options
% 2.69/1.01  
% 2.69/1.01  --aig_mode                              false
% 2.69/1.01  
% 2.69/1.01  ------ Instantiation Options
% 2.69/1.01  
% 2.69/1.01  --instantiation_flag                    true
% 2.69/1.01  --inst_sos_flag                         false
% 2.69/1.01  --inst_sos_phase                        true
% 2.69/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.01  --inst_lit_sel_side                     num_symb
% 2.69/1.01  --inst_solver_per_active                1400
% 2.69/1.01  --inst_solver_calls_frac                1.
% 2.69/1.01  --inst_passive_queue_type               priority_queues
% 2.69/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.01  --inst_passive_queues_freq              [25;2]
% 2.69/1.01  --inst_dismatching                      true
% 2.69/1.01  --inst_eager_unprocessed_to_passive     true
% 2.69/1.01  --inst_prop_sim_given                   true
% 2.69/1.01  --inst_prop_sim_new                     false
% 2.69/1.01  --inst_subs_new                         false
% 2.69/1.01  --inst_eq_res_simp                      false
% 2.69/1.01  --inst_subs_given                       false
% 2.69/1.01  --inst_orphan_elimination               true
% 2.69/1.01  --inst_learning_loop_flag               true
% 2.69/1.01  --inst_learning_start                   3000
% 2.69/1.01  --inst_learning_factor                  2
% 2.69/1.01  --inst_start_prop_sim_after_learn       3
% 2.69/1.01  --inst_sel_renew                        solver
% 2.69/1.01  --inst_lit_activity_flag                true
% 2.69/1.01  --inst_restr_to_given                   false
% 2.69/1.01  --inst_activity_threshold               500
% 2.69/1.01  --inst_out_proof                        true
% 2.69/1.01  
% 2.69/1.01  ------ Resolution Options
% 2.69/1.01  
% 2.69/1.01  --resolution_flag                       true
% 2.69/1.01  --res_lit_sel                           adaptive
% 2.69/1.01  --res_lit_sel_side                      none
% 2.69/1.01  --res_ordering                          kbo
% 2.69/1.01  --res_to_prop_solver                    active
% 2.69/1.01  --res_prop_simpl_new                    false
% 2.69/1.01  --res_prop_simpl_given                  true
% 2.69/1.01  --res_passive_queue_type                priority_queues
% 2.69/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.01  --res_passive_queues_freq               [15;5]
% 2.69/1.01  --res_forward_subs                      full
% 2.69/1.01  --res_backward_subs                     full
% 2.69/1.01  --res_forward_subs_resolution           true
% 2.69/1.01  --res_backward_subs_resolution          true
% 2.69/1.01  --res_orphan_elimination                true
% 2.69/1.01  --res_time_limit                        2.
% 2.69/1.01  --res_out_proof                         true
% 2.69/1.01  
% 2.69/1.01  ------ Superposition Options
% 2.69/1.01  
% 2.69/1.01  --superposition_flag                    true
% 2.69/1.01  --sup_passive_queue_type                priority_queues
% 2.69/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.01  --demod_completeness_check              fast
% 2.69/1.01  --demod_use_ground                      true
% 2.69/1.01  --sup_to_prop_solver                    passive
% 2.69/1.01  --sup_prop_simpl_new                    true
% 2.69/1.01  --sup_prop_simpl_given                  true
% 2.69/1.01  --sup_fun_splitting                     false
% 2.69/1.01  --sup_smt_interval                      50000
% 2.69/1.01  
% 2.69/1.01  ------ Superposition Simplification Setup
% 2.69/1.01  
% 2.69/1.01  --sup_indices_passive                   []
% 2.69/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.01  --sup_full_bw                           [BwDemod]
% 2.69/1.01  --sup_immed_triv                        [TrivRules]
% 2.69/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.01  --sup_immed_bw_main                     []
% 2.69/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.01  
% 2.69/1.01  ------ Combination Options
% 2.69/1.01  
% 2.69/1.01  --comb_res_mult                         3
% 2.69/1.01  --comb_sup_mult                         2
% 2.69/1.01  --comb_inst_mult                        10
% 2.69/1.01  
% 2.69/1.01  ------ Debug Options
% 2.69/1.01  
% 2.69/1.01  --dbg_backtrace                         false
% 2.69/1.01  --dbg_dump_prop_clauses                 false
% 2.69/1.01  --dbg_dump_prop_clauses_file            -
% 2.69/1.01  --dbg_out_stat                          false
% 2.69/1.01  ------ Parsing...
% 2.69/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.01  
% 2.69/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.69/1.01  
% 2.69/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.01  
% 2.69/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.01  ------ Proving...
% 2.69/1.01  ------ Problem Properties 
% 2.69/1.01  
% 2.69/1.01  
% 2.69/1.01  clauses                                 13
% 2.69/1.01  conjectures                             1
% 2.69/1.01  EPR                                     0
% 2.69/1.01  Horn                                    11
% 2.69/1.01  unary                                   7
% 2.69/1.01  binary                                  2
% 2.69/1.01  lits                                    24
% 2.69/1.01  lits eq                                 10
% 2.69/1.01  fd_pure                                 0
% 2.69/1.01  fd_pseudo                               0
% 2.69/1.01  fd_cond                                 0
% 2.69/1.01  fd_pseudo_cond                          3
% 2.69/1.01  AC symbols                              0
% 2.69/1.01  
% 2.69/1.01  ------ Schedule dynamic 5 is on 
% 2.69/1.01  
% 2.69/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.01  
% 2.69/1.01  
% 2.69/1.01  ------ 
% 2.69/1.01  Current options:
% 2.69/1.01  ------ 
% 2.69/1.01  
% 2.69/1.01  ------ Input Options
% 2.69/1.01  
% 2.69/1.01  --out_options                           all
% 2.69/1.01  --tptp_safe_out                         true
% 2.69/1.01  --problem_path                          ""
% 2.69/1.01  --include_path                          ""
% 2.69/1.01  --clausifier                            res/vclausify_rel
% 2.69/1.01  --clausifier_options                    --mode clausify
% 2.69/1.01  --stdin                                 false
% 2.69/1.01  --stats_out                             all
% 2.69/1.01  
% 2.69/1.01  ------ General Options
% 2.69/1.01  
% 2.69/1.01  --fof                                   false
% 2.69/1.01  --time_out_real                         305.
% 2.69/1.01  --time_out_virtual                      -1.
% 2.69/1.01  --symbol_type_check                     false
% 2.69/1.01  --clausify_out                          false
% 2.69/1.01  --sig_cnt_out                           false
% 2.69/1.01  --trig_cnt_out                          false
% 2.69/1.01  --trig_cnt_out_tolerance                1.
% 2.69/1.01  --trig_cnt_out_sk_spl                   false
% 2.69/1.01  --abstr_cl_out                          false
% 2.69/1.01  
% 2.69/1.01  ------ Global Options
% 2.69/1.01  
% 2.69/1.01  --schedule                              default
% 2.69/1.01  --add_important_lit                     false
% 2.69/1.01  --prop_solver_per_cl                    1000
% 2.69/1.01  --min_unsat_core                        false
% 2.69/1.01  --soft_assumptions                      false
% 2.69/1.01  --soft_lemma_size                       3
% 2.69/1.01  --prop_impl_unit_size                   0
% 2.69/1.01  --prop_impl_unit                        []
% 2.69/1.01  --share_sel_clauses                     true
% 2.69/1.01  --reset_solvers                         false
% 2.69/1.01  --bc_imp_inh                            [conj_cone]
% 2.69/1.01  --conj_cone_tolerance                   3.
% 2.69/1.01  --extra_neg_conj                        none
% 2.69/1.01  --large_theory_mode                     true
% 2.69/1.01  --prolific_symb_bound                   200
% 2.69/1.01  --lt_threshold                          2000
% 2.69/1.01  --clause_weak_htbl                      true
% 2.69/1.01  --gc_record_bc_elim                     false
% 2.69/1.01  
% 2.69/1.01  ------ Preprocessing Options
% 2.69/1.01  
% 2.69/1.01  --preprocessing_flag                    true
% 2.69/1.01  --time_out_prep_mult                    0.1
% 2.69/1.01  --splitting_mode                        input
% 2.69/1.01  --splitting_grd                         true
% 2.69/1.01  --splitting_cvd                         false
% 2.69/1.01  --splitting_cvd_svl                     false
% 2.69/1.01  --splitting_nvd                         32
% 2.69/1.01  --sub_typing                            true
% 2.69/1.01  --prep_gs_sim                           true
% 2.69/1.01  --prep_unflatten                        true
% 2.69/1.01  --prep_res_sim                          true
% 2.69/1.01  --prep_upred                            true
% 2.69/1.01  --prep_sem_filter                       exhaustive
% 2.69/1.01  --prep_sem_filter_out                   false
% 2.69/1.01  --pred_elim                             true
% 2.69/1.01  --res_sim_input                         true
% 2.69/1.01  --eq_ax_congr_red                       true
% 2.69/1.01  --pure_diseq_elim                       true
% 2.69/1.01  --brand_transform                       false
% 2.69/1.01  --non_eq_to_eq                          false
% 2.69/1.01  --prep_def_merge                        true
% 2.69/1.01  --prep_def_merge_prop_impl              false
% 2.69/1.01  --prep_def_merge_mbd                    true
% 2.69/1.01  --prep_def_merge_tr_red                 false
% 2.69/1.01  --prep_def_merge_tr_cl                  false
% 2.69/1.01  --smt_preprocessing                     true
% 2.69/1.01  --smt_ac_axioms                         fast
% 2.69/1.01  --preprocessed_out                      false
% 2.69/1.01  --preprocessed_stats                    false
% 2.69/1.01  
% 2.69/1.01  ------ Abstraction refinement Options
% 2.69/1.01  
% 2.69/1.01  --abstr_ref                             []
% 2.69/1.01  --abstr_ref_prep                        false
% 2.69/1.01  --abstr_ref_until_sat                   false
% 2.69/1.01  --abstr_ref_sig_restrict                funpre
% 2.69/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.01  --abstr_ref_under                       []
% 2.69/1.01  
% 2.69/1.01  ------ SAT Options
% 2.69/1.01  
% 2.69/1.01  --sat_mode                              false
% 2.69/1.01  --sat_fm_restart_options                ""
% 2.69/1.01  --sat_gr_def                            false
% 2.69/1.01  --sat_epr_types                         true
% 2.69/1.01  --sat_non_cyclic_types                  false
% 2.69/1.01  --sat_finite_models                     false
% 2.69/1.01  --sat_fm_lemmas                         false
% 2.69/1.01  --sat_fm_prep                           false
% 2.69/1.01  --sat_fm_uc_incr                        true
% 2.69/1.01  --sat_out_model                         small
% 2.69/1.01  --sat_out_clauses                       false
% 2.69/1.01  
% 2.69/1.01  ------ QBF Options
% 2.69/1.01  
% 2.69/1.01  --qbf_mode                              false
% 2.69/1.01  --qbf_elim_univ                         false
% 2.69/1.01  --qbf_dom_inst                          none
% 2.69/1.01  --qbf_dom_pre_inst                      false
% 2.69/1.01  --qbf_sk_in                             false
% 2.69/1.01  --qbf_pred_elim                         true
% 2.69/1.01  --qbf_split                             512
% 2.69/1.01  
% 2.69/1.01  ------ BMC1 Options
% 2.69/1.01  
% 2.69/1.01  --bmc1_incremental                      false
% 2.69/1.01  --bmc1_axioms                           reachable_all
% 2.69/1.01  --bmc1_min_bound                        0
% 2.69/1.01  --bmc1_max_bound                        -1
% 2.69/1.01  --bmc1_max_bound_default                -1
% 2.69/1.01  --bmc1_symbol_reachability              true
% 2.69/1.01  --bmc1_property_lemmas                  false
% 2.69/1.01  --bmc1_k_induction                      false
% 2.69/1.01  --bmc1_non_equiv_states                 false
% 2.69/1.01  --bmc1_deadlock                         false
% 2.69/1.01  --bmc1_ucm                              false
% 2.69/1.01  --bmc1_add_unsat_core                   none
% 2.69/1.01  --bmc1_unsat_core_children              false
% 2.69/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.01  --bmc1_out_stat                         full
% 2.69/1.01  --bmc1_ground_init                      false
% 2.69/1.01  --bmc1_pre_inst_next_state              false
% 2.69/1.01  --bmc1_pre_inst_state                   false
% 2.69/1.01  --bmc1_pre_inst_reach_state             false
% 2.69/1.01  --bmc1_out_unsat_core                   false
% 2.69/1.01  --bmc1_aig_witness_out                  false
% 2.69/1.01  --bmc1_verbose                          false
% 2.69/1.01  --bmc1_dump_clauses_tptp                false
% 2.69/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.01  --bmc1_dump_file                        -
% 2.69/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.01  --bmc1_ucm_extend_mode                  1
% 2.69/1.01  --bmc1_ucm_init_mode                    2
% 2.69/1.01  --bmc1_ucm_cone_mode                    none
% 2.69/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.01  --bmc1_ucm_relax_model                  4
% 2.69/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.01  --bmc1_ucm_layered_model                none
% 2.69/1.01  --bmc1_ucm_max_lemma_size               10
% 2.69/1.01  
% 2.69/1.01  ------ AIG Options
% 2.69/1.01  
% 2.69/1.01  --aig_mode                              false
% 2.69/1.01  
% 2.69/1.01  ------ Instantiation Options
% 2.69/1.01  
% 2.69/1.01  --instantiation_flag                    true
% 2.69/1.01  --inst_sos_flag                         false
% 2.69/1.01  --inst_sos_phase                        true
% 2.69/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.01  --inst_lit_sel_side                     none
% 2.69/1.01  --inst_solver_per_active                1400
% 2.69/1.01  --inst_solver_calls_frac                1.
% 2.69/1.01  --inst_passive_queue_type               priority_queues
% 2.69/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.02  --inst_passive_queues_freq              [25;2]
% 2.69/1.02  --inst_dismatching                      true
% 2.69/1.02  --inst_eager_unprocessed_to_passive     true
% 2.69/1.02  --inst_prop_sim_given                   true
% 2.69/1.02  --inst_prop_sim_new                     false
% 2.69/1.02  --inst_subs_new                         false
% 2.69/1.02  --inst_eq_res_simp                      false
% 2.69/1.02  --inst_subs_given                       false
% 2.69/1.02  --inst_orphan_elimination               true
% 2.69/1.02  --inst_learning_loop_flag               true
% 2.69/1.02  --inst_learning_start                   3000
% 2.69/1.02  --inst_learning_factor                  2
% 2.69/1.02  --inst_start_prop_sim_after_learn       3
% 2.69/1.02  --inst_sel_renew                        solver
% 2.69/1.02  --inst_lit_activity_flag                true
% 2.69/1.02  --inst_restr_to_given                   false
% 2.69/1.02  --inst_activity_threshold               500
% 2.69/1.02  --inst_out_proof                        true
% 2.69/1.02  
% 2.69/1.02  ------ Resolution Options
% 2.69/1.02  
% 2.69/1.02  --resolution_flag                       false
% 2.69/1.02  --res_lit_sel                           adaptive
% 2.69/1.02  --res_lit_sel_side                      none
% 2.69/1.02  --res_ordering                          kbo
% 2.69/1.02  --res_to_prop_solver                    active
% 2.69/1.02  --res_prop_simpl_new                    false
% 2.69/1.02  --res_prop_simpl_given                  true
% 2.69/1.02  --res_passive_queue_type                priority_queues
% 2.69/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.02  --res_passive_queues_freq               [15;5]
% 2.69/1.02  --res_forward_subs                      full
% 2.69/1.02  --res_backward_subs                     full
% 2.69/1.02  --res_forward_subs_resolution           true
% 2.69/1.02  --res_backward_subs_resolution          true
% 2.69/1.02  --res_orphan_elimination                true
% 2.69/1.02  --res_time_limit                        2.
% 2.69/1.02  --res_out_proof                         true
% 2.69/1.02  
% 2.69/1.02  ------ Superposition Options
% 2.69/1.02  
% 2.69/1.02  --superposition_flag                    true
% 2.69/1.02  --sup_passive_queue_type                priority_queues
% 2.69/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.02  --demod_completeness_check              fast
% 2.69/1.02  --demod_use_ground                      true
% 2.69/1.02  --sup_to_prop_solver                    passive
% 2.69/1.02  --sup_prop_simpl_new                    true
% 2.69/1.02  --sup_prop_simpl_given                  true
% 2.69/1.02  --sup_fun_splitting                     false
% 2.69/1.02  --sup_smt_interval                      50000
% 2.69/1.02  
% 2.69/1.02  ------ Superposition Simplification Setup
% 2.69/1.02  
% 2.69/1.02  --sup_indices_passive                   []
% 2.69/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.02  --sup_full_bw                           [BwDemod]
% 2.69/1.02  --sup_immed_triv                        [TrivRules]
% 2.69/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.02  --sup_immed_bw_main                     []
% 2.69/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.02  
% 2.69/1.02  ------ Combination Options
% 2.69/1.02  
% 2.69/1.02  --comb_res_mult                         3
% 2.69/1.02  --comb_sup_mult                         2
% 2.69/1.02  --comb_inst_mult                        10
% 2.69/1.02  
% 2.69/1.02  ------ Debug Options
% 2.69/1.02  
% 2.69/1.02  --dbg_backtrace                         false
% 2.69/1.02  --dbg_dump_prop_clauses                 false
% 2.69/1.02  --dbg_dump_prop_clauses_file            -
% 2.69/1.02  --dbg_out_stat                          false
% 2.69/1.02  
% 2.69/1.02  
% 2.69/1.02  
% 2.69/1.02  
% 2.69/1.02  ------ Proving...
% 2.69/1.02  
% 2.69/1.02  
% 2.69/1.02  % SZS status Theorem for theBenchmark.p
% 2.69/1.02  
% 2.69/1.02   Resolution empty clause
% 2.69/1.02  
% 2.69/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.02  
% 2.69/1.02  fof(f2,axiom,(
% 2.69/1.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f16,plain,(
% 2.69/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.69/1.02    inference(nnf_transformation,[],[f2])).
% 2.69/1.02  
% 2.69/1.02  fof(f17,plain,(
% 2.69/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.69/1.02    inference(flattening,[],[f16])).
% 2.69/1.02  
% 2.69/1.02  fof(f18,plain,(
% 2.69/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.69/1.02    inference(rectify,[],[f17])).
% 2.69/1.02  
% 2.69/1.02  fof(f19,plain,(
% 2.69/1.02    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.69/1.02    introduced(choice_axiom,[])).
% 2.69/1.02  
% 2.69/1.02  fof(f20,plain,(
% 2.69/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.69/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 2.69/1.02  
% 2.69/1.02  fof(f27,plain,(
% 2.69/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f20])).
% 2.69/1.02  
% 2.69/1.02  fof(f10,axiom,(
% 2.69/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f37,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.69/1.02    inference(cnf_transformation,[],[f10])).
% 2.69/1.02  
% 2.69/1.02  fof(f44,plain,(
% 2.69/1.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.69/1.02    inference(definition_unfolding,[],[f27,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f1,axiom,(
% 2.69/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f23,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f1])).
% 2.69/1.02  
% 2.69/1.02  fof(f41,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 2.69/1.02    inference(definition_unfolding,[],[f23,f37,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f12,conjecture,(
% 2.69/1.02    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f13,negated_conjecture,(
% 2.69/1.02    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 2.69/1.02    inference(negated_conjecture,[],[f12])).
% 2.69/1.02  
% 2.69/1.02  fof(f15,plain,(
% 2.69/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0),
% 2.69/1.02    inference(ennf_transformation,[],[f13])).
% 2.69/1.02  
% 2.69/1.02  fof(f21,plain,(
% 2.69/1.02    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 2.69/1.02    introduced(choice_axiom,[])).
% 2.69/1.02  
% 2.69/1.02  fof(f22,plain,(
% 2.69/1.02    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 2.69/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f21])).
% 2.69/1.02  
% 2.69/1.02  fof(f39,plain,(
% 2.69/1.02    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 2.69/1.02    inference(cnf_transformation,[],[f22])).
% 2.69/1.02  
% 2.69/1.02  fof(f52,plain,(
% 2.69/1.02    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3))),
% 2.69/1.02    inference(definition_unfolding,[],[f39,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f25,plain,(
% 2.69/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.69/1.02    inference(cnf_transformation,[],[f20])).
% 2.69/1.02  
% 2.69/1.02  fof(f46,plain,(
% 2.69/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 2.69/1.02    inference(definition_unfolding,[],[f25,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f54,plain,(
% 2.69/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.69/1.02    inference(equality_resolution,[],[f46])).
% 2.69/1.02  
% 2.69/1.02  fof(f3,axiom,(
% 2.69/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f14,plain,(
% 2.69/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.69/1.02    inference(ennf_transformation,[],[f3])).
% 2.69/1.02  
% 2.69/1.02  fof(f30,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f14])).
% 2.69/1.02  
% 2.69/1.02  fof(f48,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.69/1.02    inference(definition_unfolding,[],[f30,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f5,axiom,(
% 2.69/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f32,plain,(
% 2.69/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f5])).
% 2.69/1.02  
% 2.69/1.02  fof(f26,plain,(
% 2.69/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.69/1.02    inference(cnf_transformation,[],[f20])).
% 2.69/1.02  
% 2.69/1.02  fof(f45,plain,(
% 2.69/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 2.69/1.02    inference(definition_unfolding,[],[f26,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f53,plain,(
% 2.69/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.69/1.02    inference(equality_resolution,[],[f45])).
% 2.69/1.02  
% 2.69/1.02  fof(f6,axiom,(
% 2.69/1.02    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f33,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f6])).
% 2.69/1.02  
% 2.69/1.02  fof(f7,axiom,(
% 2.69/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f34,plain,(
% 2.69/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f7])).
% 2.69/1.02  
% 2.69/1.02  fof(f40,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 2.69/1.02    inference(definition_unfolding,[],[f33,f37,f34,f34])).
% 2.69/1.02  
% 2.69/1.02  fof(f4,axiom,(
% 2.69/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f31,plain,(
% 2.69/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/1.02    inference(cnf_transformation,[],[f4])).
% 2.69/1.02  
% 2.69/1.02  fof(f49,plain,(
% 2.69/1.02    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.69/1.02    inference(definition_unfolding,[],[f31,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f11,axiom,(
% 2.69/1.02    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 2.69/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.02  
% 2.69/1.02  fof(f38,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 2.69/1.02    inference(cnf_transformation,[],[f11])).
% 2.69/1.02  
% 2.69/1.02  fof(f51,plain,(
% 2.69/1.02    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) )),
% 2.69/1.02    inference(definition_unfolding,[],[f38,f37,f34])).
% 2.69/1.02  
% 2.69/1.02  fof(f28,plain,(
% 2.69/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f20])).
% 2.69/1.02  
% 2.69/1.02  fof(f43,plain,(
% 2.69/1.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.69/1.02    inference(definition_unfolding,[],[f28,f37])).
% 2.69/1.02  
% 2.69/1.02  fof(f29,plain,(
% 2.69/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.69/1.02    inference(cnf_transformation,[],[f20])).
% 2.69/1.02  
% 2.69/1.02  fof(f42,plain,(
% 2.69/1.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.69/1.02    inference(definition_unfolding,[],[f29,f37])).
% 2.69/1.02  
% 2.69/1.02  cnf(c_4,plain,
% 2.69/1.02      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.69/1.02      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 2.69/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_264,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 2.69/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_1,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 2.69/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_13,negated_conjecture,
% 2.69/1.02      ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
% 2.69/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_384,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_1,c_13]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_6,plain,
% 2.69/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 2.69/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_262,plain,
% 2.69/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.69/1.02      | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
% 2.69/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_1213,plain,
% 2.69/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 2.69/1.02      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_384,c_262]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_1811,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(sK3,X0)) = X1
% 2.69/1.02      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(sK3,X0,X1),k1_xboole_0) = iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_264,c_1213]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_8,plain,
% 2.69/1.02      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 2.69/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_10,plain,
% 2.69/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.69/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_99,plain,
% 2.69/1.02      ( X0 != X1 | k3_tarski(k2_tarski(X2,X1)) = X1 | k1_xboole_0 != X2 ),
% 2.69/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_100,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 2.69/1.02      inference(unflattening,[status(thm)],[c_99]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_1212,plain,
% 2.69/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.69/1.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_100,c_262]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2764,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(sK3,X0)) = X1
% 2.69/1.02      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top ),
% 2.69/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1811,c_1212]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_5,plain,
% 2.69/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 2.69/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_263,plain,
% 2.69/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.69/1.02      | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 2.69/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_1585,plain,
% 2.69/1.02      ( r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top
% 2.69/1.02      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_384,c_263]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2783,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = X0
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_2764,c_1585]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2794,plain,
% 2.69/1.02      ( k1_xboole_0 = X0
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
% 2.69/1.02      inference(demodulation,[status(thm)],[c_2783,c_384]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2927,plain,
% 2.69/1.02      ( k1_xboole_0 = X0
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top ),
% 2.69/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_2794,c_1212]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_0,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 2.69/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_1208,plain,
% 2.69/1.02      ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
% 2.69/1.02      | r2_hidden(X0,k2_tarski(X1,X2)) = iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_0,c_262]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2932,plain,
% 2.69/1.02      ( k2_tarski(X0,X0) = k1_xboole_0
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(X0,X0)),k2_tarski(X0,X1)) = iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_2927,c_1208]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_9,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 2.69/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_12,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) != k1_xboole_0 ),
% 2.69/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_548,plain,
% 2.69/1.02      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_9,c_12]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_7054,plain,
% 2.69/1.02      ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(X0,X0)),k2_tarski(X0,X1)) = iProver_top ),
% 2.69/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2932,c_548]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_3,plain,
% 2.69/1.02      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.69/1.02      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.69/1.02      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 2.69/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_265,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
% 2.69/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2930,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = X0
% 2.69/1.02      | k1_xboole_0 = X0
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),sK3) != iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_2927,c_265]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2969,plain,
% 2.69/1.02      ( k1_xboole_0 = X0
% 2.69/1.02      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),sK3) != iProver_top ),
% 2.69/1.02      inference(demodulation,[status(thm)],[c_2930,c_384]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_3095,plain,
% 2.69/1.02      ( sK3 = k1_xboole_0 ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_2927,c_2969]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_7060,plain,
% 2.69/1.02      ( r2_hidden(sK0(k1_xboole_0,k2_tarski(sK1,sK2),k2_tarski(X0,X0)),k2_tarski(X0,X1)) = iProver_top ),
% 2.69/1.02      inference(light_normalisation,[status(thm)],[c_7054,c_3095]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_2,plain,
% 2.69/1.02      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.69/1.02      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.69/1.02      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 2.69/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_266,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 2.69/1.02      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 2.69/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_7067,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK2))) = k2_tarski(sK1,sK1)
% 2.69/1.02      | r2_hidden(sK0(k1_xboole_0,k2_tarski(sK1,sK2),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) != iProver_top ),
% 2.69/1.02      inference(superposition,[status(thm)],[c_7060,c_266]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_7084,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK2))) = k2_tarski(sK1,sK1) ),
% 2.69/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_7067,c_7060]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_3230,plain,
% 2.69/1.02      ( k3_tarski(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
% 2.69/1.02      inference(demodulation,[status(thm)],[c_3095,c_384]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_7085,plain,
% 2.69/1.02      ( k2_tarski(sK1,sK1) = k1_xboole_0 ),
% 2.69/1.02      inference(light_normalisation,[status(thm)],[c_7084,c_3230]) ).
% 2.69/1.02  
% 2.69/1.02  cnf(c_7285,plain,
% 2.69/1.02      ( $false ),
% 2.69/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_7085,c_548]) ).
% 2.69/1.02  
% 2.69/1.02  
% 2.69/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.02  
% 2.69/1.02  ------                               Statistics
% 2.69/1.02  
% 2.69/1.02  ------ General
% 2.69/1.02  
% 2.69/1.02  abstr_ref_over_cycles:                  0
% 2.69/1.02  abstr_ref_under_cycles:                 0
% 2.69/1.02  gc_basic_clause_elim:                   0
% 2.69/1.02  forced_gc_time:                         0
% 2.69/1.02  parsing_time:                           0.013
% 2.69/1.02  unif_index_cands_time:                  0.
% 2.69/1.02  unif_index_add_time:                    0.
% 2.69/1.02  orderings_time:                         0.
% 2.69/1.02  out_proof_time:                         0.008
% 2.69/1.02  total_time:                             0.266
% 2.69/1.02  num_of_symbols:                         41
% 2.69/1.02  num_of_terms:                           8124
% 2.69/1.02  
% 2.69/1.02  ------ Preprocessing
% 2.69/1.02  
% 2.69/1.02  num_of_splits:                          0
% 2.69/1.02  num_of_split_atoms:                     0
% 2.69/1.02  num_of_reused_defs:                     0
% 2.69/1.02  num_eq_ax_congr_red:                    22
% 2.69/1.02  num_of_sem_filtered_clauses:            1
% 2.69/1.02  num_of_subtypes:                        0
% 2.69/1.02  monotx_restored_types:                  0
% 2.69/1.02  sat_num_of_epr_types:                   0
% 2.69/1.02  sat_num_of_non_cyclic_types:            0
% 2.69/1.02  sat_guarded_non_collapsed_types:        0
% 2.69/1.02  num_pure_diseq_elim:                    0
% 2.69/1.02  simp_replaced_by:                       0
% 2.69/1.02  res_preprocessed:                       64
% 2.69/1.02  prep_upred:                             0
% 2.69/1.02  prep_unflattend:                        2
% 2.69/1.02  smt_new_axioms:                         0
% 2.69/1.02  pred_elim_cands:                        1
% 2.69/1.02  pred_elim:                              1
% 2.69/1.02  pred_elim_cl:                           1
% 2.69/1.02  pred_elim_cycles:                       3
% 2.69/1.02  merged_defs:                            0
% 2.69/1.02  merged_defs_ncl:                        0
% 2.69/1.02  bin_hyper_res:                          0
% 2.69/1.02  prep_cycles:                            4
% 2.69/1.02  pred_elim_time:                         0.
% 2.69/1.02  splitting_time:                         0.
% 2.69/1.02  sem_filter_time:                        0.
% 2.69/1.02  monotx_time:                            0.
% 2.69/1.02  subtype_inf_time:                       0.
% 2.69/1.02  
% 2.69/1.02  ------ Problem properties
% 2.69/1.02  
% 2.69/1.02  clauses:                                13
% 2.69/1.02  conjectures:                            1
% 2.69/1.02  epr:                                    0
% 2.69/1.02  horn:                                   11
% 2.69/1.02  ground:                                 1
% 2.69/1.02  unary:                                  7
% 2.69/1.02  binary:                                 2
% 2.69/1.02  lits:                                   24
% 2.69/1.02  lits_eq:                                10
% 2.69/1.02  fd_pure:                                0
% 2.69/1.02  fd_pseudo:                              0
% 2.69/1.02  fd_cond:                                0
% 2.69/1.02  fd_pseudo_cond:                         3
% 2.69/1.02  ac_symbols:                             0
% 2.69/1.02  
% 2.69/1.02  ------ Propositional Solver
% 2.69/1.02  
% 2.69/1.02  prop_solver_calls:                      29
% 2.69/1.02  prop_fast_solver_calls:                 393
% 2.69/1.02  smt_solver_calls:                       0
% 2.69/1.02  smt_fast_solver_calls:                  0
% 2.69/1.02  prop_num_of_clauses:                    1817
% 2.69/1.02  prop_preprocess_simplified:             5360
% 2.69/1.02  prop_fo_subsumed:                       2
% 2.69/1.02  prop_solver_time:                       0.
% 2.69/1.02  smt_solver_time:                        0.
% 2.69/1.02  smt_fast_solver_time:                   0.
% 2.69/1.02  prop_fast_solver_time:                  0.
% 2.69/1.02  prop_unsat_core_time:                   0.
% 2.69/1.02  
% 2.69/1.02  ------ QBF
% 2.69/1.02  
% 2.69/1.02  qbf_q_res:                              0
% 2.69/1.02  qbf_num_tautologies:                    0
% 2.69/1.02  qbf_prep_cycles:                        0
% 2.69/1.02  
% 2.69/1.02  ------ BMC1
% 2.69/1.02  
% 2.69/1.02  bmc1_current_bound:                     -1
% 2.69/1.02  bmc1_last_solved_bound:                 -1
% 2.69/1.02  bmc1_unsat_core_size:                   -1
% 2.69/1.02  bmc1_unsat_core_parents_size:           -1
% 2.69/1.02  bmc1_merge_next_fun:                    0
% 2.69/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.02  
% 2.69/1.02  ------ Instantiation
% 2.69/1.02  
% 2.69/1.02  inst_num_of_clauses:                    680
% 2.69/1.02  inst_num_in_passive:                    427
% 2.69/1.02  inst_num_in_active:                     229
% 2.69/1.02  inst_num_in_unprocessed:                24
% 2.69/1.02  inst_num_of_loops:                      240
% 2.69/1.02  inst_num_of_learning_restarts:          0
% 2.69/1.02  inst_num_moves_active_passive:          9
% 2.69/1.02  inst_lit_activity:                      0
% 2.69/1.02  inst_lit_activity_moves:                0
% 2.69/1.02  inst_num_tautologies:                   0
% 2.69/1.02  inst_num_prop_implied:                  0
% 2.69/1.02  inst_num_existing_simplified:           0
% 2.69/1.02  inst_num_eq_res_simplified:             0
% 2.69/1.02  inst_num_child_elim:                    0
% 2.69/1.02  inst_num_of_dismatching_blockings:      857
% 2.69/1.02  inst_num_of_non_proper_insts:           727
% 2.69/1.02  inst_num_of_duplicates:                 0
% 2.69/1.02  inst_inst_num_from_inst_to_res:         0
% 2.69/1.02  inst_dismatching_checking_time:         0.
% 2.69/1.02  
% 2.69/1.02  ------ Resolution
% 2.69/1.02  
% 2.69/1.02  res_num_of_clauses:                     0
% 2.69/1.02  res_num_in_passive:                     0
% 2.69/1.02  res_num_in_active:                      0
% 2.69/1.02  res_num_of_loops:                       68
% 2.69/1.02  res_forward_subset_subsumed:            78
% 2.69/1.02  res_backward_subset_subsumed:           0
% 2.69/1.02  res_forward_subsumed:                   0
% 2.69/1.02  res_backward_subsumed:                  0
% 2.69/1.02  res_forward_subsumption_resolution:     0
% 2.69/1.02  res_backward_subsumption_resolution:    0
% 2.69/1.02  res_clause_to_clause_subsumption:       3630
% 2.69/1.02  res_orphan_elimination:                 0
% 2.69/1.02  res_tautology_del:                      114
% 2.69/1.02  res_num_eq_res_simplified:              0
% 2.69/1.02  res_num_sel_changes:                    0
% 2.69/1.02  res_moves_from_active_to_pass:          0
% 2.69/1.02  
% 2.69/1.02  ------ Superposition
% 2.69/1.02  
% 2.69/1.02  sup_time_total:                         0.
% 2.69/1.02  sup_time_generating:                    0.
% 2.69/1.02  sup_time_sim_full:                      0.
% 2.69/1.02  sup_time_sim_immed:                     0.
% 2.69/1.02  
% 2.69/1.02  sup_num_of_clauses:                     198
% 2.69/1.02  sup_num_in_active:                      34
% 2.69/1.02  sup_num_in_passive:                     164
% 2.69/1.02  sup_num_of_loops:                       47
% 2.69/1.02  sup_fw_superposition:                   162
% 2.69/1.02  sup_bw_superposition:                   287
% 2.69/1.02  sup_immediate_simplified:               149
% 2.69/1.02  sup_given_eliminated:                   2
% 2.69/1.02  comparisons_done:                       0
% 2.69/1.02  comparisons_avoided:                    0
% 2.69/1.02  
% 2.69/1.02  ------ Simplifications
% 2.69/1.02  
% 2.69/1.02  
% 2.69/1.02  sim_fw_subset_subsumed:                 64
% 2.69/1.02  sim_bw_subset_subsumed:                 16
% 2.69/1.02  sim_fw_subsumed:                        46
% 2.69/1.02  sim_bw_subsumed:                        0
% 2.69/1.02  sim_fw_subsumption_res:                 12
% 2.69/1.02  sim_bw_subsumption_res:                 0
% 2.69/1.02  sim_tautology_del:                      38
% 2.69/1.02  sim_eq_tautology_del:                   19
% 2.69/1.02  sim_eq_res_simp:                        40
% 2.69/1.02  sim_fw_demodulated:                     43
% 2.69/1.02  sim_bw_demodulated:                     9
% 2.69/1.02  sim_light_normalised:                   53
% 2.69/1.02  sim_joinable_taut:                      0
% 2.69/1.02  sim_joinable_simp:                      0
% 2.69/1.02  sim_ac_normalised:                      0
% 2.69/1.02  sim_smt_subsumption:                    0
% 2.69/1.02  
%------------------------------------------------------------------------------
