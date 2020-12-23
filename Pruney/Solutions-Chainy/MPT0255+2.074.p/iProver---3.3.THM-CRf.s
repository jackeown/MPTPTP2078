%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:27 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  106 (1395 expanded)
%              Number of clauses        :   60 ( 373 expanded)
%              Number of leaves         :   12 ( 356 expanded)
%              Depth                    :   26
%              Number of atoms          :  292 (4663 expanded)
%              Number of equality atoms :  164 (1661 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f36,f36])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f22])).

fof(f41,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f33,f36,f34,f34])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) ),
    inference(definition_unfolding,[],[f40,f36,f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_420,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_528,plain,
    ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_15])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_418,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1206,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_418])).

cnf(c_3285,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = X1
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_1206])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_138,plain,
    ( X0 != X1
    | k3_tarski(k2_tarski(X2,X1)) = X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_139,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_1205,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_139,c_418])).

cnf(c_6358,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = X1
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3285,c_1205])).

cnf(c_6375,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = sK3
    | r2_hidden(sK0(sK3,X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6358,c_1206])).

cnf(c_3318,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_1205])).

cnf(c_529,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_139])).

cnf(c_3398,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3318,c_529])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_422,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4405,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_422])).

cnf(c_4601,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4405,c_3398])).

cnf(c_4602,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4601,c_529])).

cnf(c_4857,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4602,c_1206])).

cnf(c_4401,plain,
    ( sK3 = X0
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_1206])).

cnf(c_4782,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4401])).

cnf(c_5243,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4857,c_4782])).

cnf(c_5249,plain,
    ( k3_tarski(k2_tarski(sK3,k1_xboole_0)) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5243,c_422])).

cnf(c_5487,plain,
    ( sK3 = X0
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4401,c_1205])).

cnf(c_5527,plain,
    ( sK3 = X0
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_5487])).

cnf(c_5529,plain,
    ( sK3 = X0
    | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5527])).

cnf(c_5709,plain,
    ( k3_tarski(k2_tarski(sK3,k1_xboole_0)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5249,c_5529])).

cnf(c_5710,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5709,c_529])).

cnf(c_8523,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6375,c_139,c_5710])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_419,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1508,plain,
    ( r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_419])).

cnf(c_4859,plain,
    ( k2_tarski(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4602,c_1508])).

cnf(c_4403,plain,
    ( k2_tarski(sK1,sK2) = X0
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_1508])).

cnf(c_4788,plain,
    ( k2_tarski(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4403])).

cnf(c_5268,plain,
    ( k2_tarski(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4859,c_4788])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_801,plain,
    ( k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_5274,plain,
    ( r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5268,c_801])).

cnf(c_11,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_144,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | X1 != X3
    | k2_tarski(X2,X0) != X4
    | k3_tarski(k2_tarski(X4,X3)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k3_tarski(k2_tarski(k2_tarski(X0,X2),X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_416,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X1),X2)) = X2
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_5278,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),X0),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5274,c_416])).

cnf(c_5666,plain,
    ( k2_tarski(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5278,c_529])).

cnf(c_8123,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5666,c_801])).

cnf(c_8527,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0,k1_xboole_0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8523,c_8123])).

cnf(c_1202,plain,
    ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
    | r2_hidden(X0,k2_tarski(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_418])).

cnf(c_8538,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k2_tarski(X0,X0),k1_xboole_0),k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8527,c_1202])).

cnf(c_688,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_529,c_14])).

cnf(c_9365,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_tarski(X0,X0),k1_xboole_0),k2_tarski(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8538,c_688])).

cnf(c_9387,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_tarski(sK1,sK1),k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9365,c_1508])).

cnf(c_9428,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9387,c_8123])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:12:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.82/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/0.98  
% 2.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/0.98  
% 2.82/0.98  ------  iProver source info
% 2.82/0.98  
% 2.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/0.98  git: non_committed_changes: false
% 2.82/0.98  git: last_make_outside_of_git: false
% 2.82/0.98  
% 2.82/0.98  ------ 
% 2.82/0.98  
% 2.82/0.98  ------ Input Options
% 2.82/0.98  
% 2.82/0.98  --out_options                           all
% 2.82/0.98  --tptp_safe_out                         true
% 2.82/0.98  --problem_path                          ""
% 2.82/0.98  --include_path                          ""
% 2.82/0.98  --clausifier                            res/vclausify_rel
% 2.82/0.98  --clausifier_options                    --mode clausify
% 2.82/0.98  --stdin                                 false
% 2.82/0.98  --stats_out                             all
% 2.82/0.98  
% 2.82/0.98  ------ General Options
% 2.82/0.98  
% 2.82/0.98  --fof                                   false
% 2.82/0.98  --time_out_real                         305.
% 2.82/0.98  --time_out_virtual                      -1.
% 2.82/0.98  --symbol_type_check                     false
% 2.82/0.98  --clausify_out                          false
% 2.82/0.98  --sig_cnt_out                           false
% 2.82/0.98  --trig_cnt_out                          false
% 2.82/0.98  --trig_cnt_out_tolerance                1.
% 2.82/0.98  --trig_cnt_out_sk_spl                   false
% 2.82/0.98  --abstr_cl_out                          false
% 2.82/0.98  
% 2.82/0.98  ------ Global Options
% 2.82/0.98  
% 2.82/0.98  --schedule                              default
% 2.82/0.98  --add_important_lit                     false
% 2.82/0.98  --prop_solver_per_cl                    1000
% 2.82/0.98  --min_unsat_core                        false
% 2.82/0.98  --soft_assumptions                      false
% 2.82/0.98  --soft_lemma_size                       3
% 2.82/0.98  --prop_impl_unit_size                   0
% 2.82/0.98  --prop_impl_unit                        []
% 2.82/0.98  --share_sel_clauses                     true
% 2.82/0.98  --reset_solvers                         false
% 2.82/0.98  --bc_imp_inh                            [conj_cone]
% 2.82/0.98  --conj_cone_tolerance                   3.
% 2.82/0.98  --extra_neg_conj                        none
% 2.82/0.98  --large_theory_mode                     true
% 2.82/0.98  --prolific_symb_bound                   200
% 2.82/0.98  --lt_threshold                          2000
% 2.82/0.98  --clause_weak_htbl                      true
% 2.82/0.98  --gc_record_bc_elim                     false
% 2.82/0.98  
% 2.82/0.98  ------ Preprocessing Options
% 2.82/0.98  
% 2.82/0.98  --preprocessing_flag                    true
% 2.82/0.98  --time_out_prep_mult                    0.1
% 2.82/0.98  --splitting_mode                        input
% 2.82/0.98  --splitting_grd                         true
% 2.82/0.98  --splitting_cvd                         false
% 2.82/0.98  --splitting_cvd_svl                     false
% 2.82/0.98  --splitting_nvd                         32
% 2.82/0.98  --sub_typing                            true
% 2.82/0.98  --prep_gs_sim                           true
% 2.82/0.98  --prep_unflatten                        true
% 2.82/0.98  --prep_res_sim                          true
% 2.82/0.98  --prep_upred                            true
% 2.82/0.98  --prep_sem_filter                       exhaustive
% 2.82/0.98  --prep_sem_filter_out                   false
% 2.82/0.98  --pred_elim                             true
% 2.82/0.98  --res_sim_input                         true
% 2.82/0.98  --eq_ax_congr_red                       true
% 2.82/0.98  --pure_diseq_elim                       true
% 2.82/0.98  --brand_transform                       false
% 2.82/0.98  --non_eq_to_eq                          false
% 2.82/0.98  --prep_def_merge                        true
% 2.82/0.98  --prep_def_merge_prop_impl              false
% 2.82/0.98  --prep_def_merge_mbd                    true
% 2.82/0.98  --prep_def_merge_tr_red                 false
% 2.82/0.98  --prep_def_merge_tr_cl                  false
% 2.82/0.98  --smt_preprocessing                     true
% 2.82/0.98  --smt_ac_axioms                         fast
% 2.82/0.98  --preprocessed_out                      false
% 2.82/0.98  --preprocessed_stats                    false
% 2.82/0.98  
% 2.82/0.98  ------ Abstraction refinement Options
% 2.82/0.98  
% 2.82/0.98  --abstr_ref                             []
% 2.82/0.98  --abstr_ref_prep                        false
% 2.82/0.98  --abstr_ref_until_sat                   false
% 2.82/0.98  --abstr_ref_sig_restrict                funpre
% 2.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.98  --abstr_ref_under                       []
% 2.82/0.98  
% 2.82/0.98  ------ SAT Options
% 2.82/0.98  
% 2.82/0.98  --sat_mode                              false
% 2.82/0.98  --sat_fm_restart_options                ""
% 2.82/0.98  --sat_gr_def                            false
% 2.82/0.98  --sat_epr_types                         true
% 2.82/0.98  --sat_non_cyclic_types                  false
% 2.82/0.98  --sat_finite_models                     false
% 2.82/0.98  --sat_fm_lemmas                         false
% 2.82/0.98  --sat_fm_prep                           false
% 2.82/0.98  --sat_fm_uc_incr                        true
% 2.82/0.98  --sat_out_model                         small
% 2.82/0.98  --sat_out_clauses                       false
% 2.82/0.98  
% 2.82/0.98  ------ QBF Options
% 2.82/0.98  
% 2.82/0.98  --qbf_mode                              false
% 2.82/0.98  --qbf_elim_univ                         false
% 2.82/0.98  --qbf_dom_inst                          none
% 2.82/0.98  --qbf_dom_pre_inst                      false
% 2.82/0.98  --qbf_sk_in                             false
% 2.82/0.98  --qbf_pred_elim                         true
% 2.82/0.98  --qbf_split                             512
% 2.82/0.98  
% 2.82/0.98  ------ BMC1 Options
% 2.82/0.98  
% 2.82/0.98  --bmc1_incremental                      false
% 2.82/0.98  --bmc1_axioms                           reachable_all
% 2.82/0.98  --bmc1_min_bound                        0
% 2.82/0.98  --bmc1_max_bound                        -1
% 2.82/0.98  --bmc1_max_bound_default                -1
% 2.82/0.98  --bmc1_symbol_reachability              true
% 2.82/0.98  --bmc1_property_lemmas                  false
% 2.82/0.98  --bmc1_k_induction                      false
% 2.82/0.98  --bmc1_non_equiv_states                 false
% 2.82/0.98  --bmc1_deadlock                         false
% 2.82/0.98  --bmc1_ucm                              false
% 2.82/0.98  --bmc1_add_unsat_core                   none
% 2.82/0.98  --bmc1_unsat_core_children              false
% 2.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.98  --bmc1_out_stat                         full
% 2.82/0.98  --bmc1_ground_init                      false
% 2.82/0.98  --bmc1_pre_inst_next_state              false
% 2.82/0.98  --bmc1_pre_inst_state                   false
% 2.82/0.98  --bmc1_pre_inst_reach_state             false
% 2.82/0.98  --bmc1_out_unsat_core                   false
% 2.82/0.98  --bmc1_aig_witness_out                  false
% 2.82/0.98  --bmc1_verbose                          false
% 2.82/0.98  --bmc1_dump_clauses_tptp                false
% 2.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.98  --bmc1_dump_file                        -
% 2.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.98  --bmc1_ucm_extend_mode                  1
% 2.82/0.98  --bmc1_ucm_init_mode                    2
% 2.82/0.98  --bmc1_ucm_cone_mode                    none
% 2.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.98  --bmc1_ucm_relax_model                  4
% 2.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.98  --bmc1_ucm_layered_model                none
% 2.82/0.98  --bmc1_ucm_max_lemma_size               10
% 2.82/0.98  
% 2.82/0.98  ------ AIG Options
% 2.82/0.98  
% 2.82/0.98  --aig_mode                              false
% 2.82/0.98  
% 2.82/0.98  ------ Instantiation Options
% 2.82/0.98  
% 2.82/0.98  --instantiation_flag                    true
% 2.82/0.98  --inst_sos_flag                         false
% 2.82/0.98  --inst_sos_phase                        true
% 2.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.98  --inst_lit_sel_side                     num_symb
% 2.82/0.98  --inst_solver_per_active                1400
% 2.82/0.98  --inst_solver_calls_frac                1.
% 2.82/0.98  --inst_passive_queue_type               priority_queues
% 2.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.98  --inst_passive_queues_freq              [25;2]
% 2.82/0.98  --inst_dismatching                      true
% 2.82/0.98  --inst_eager_unprocessed_to_passive     true
% 2.82/0.98  --inst_prop_sim_given                   true
% 2.82/0.98  --inst_prop_sim_new                     false
% 2.82/0.98  --inst_subs_new                         false
% 2.82/0.98  --inst_eq_res_simp                      false
% 2.82/0.98  --inst_subs_given                       false
% 2.82/0.98  --inst_orphan_elimination               true
% 2.82/0.98  --inst_learning_loop_flag               true
% 2.82/0.98  --inst_learning_start                   3000
% 2.82/0.98  --inst_learning_factor                  2
% 2.82/0.98  --inst_start_prop_sim_after_learn       3
% 2.82/0.98  --inst_sel_renew                        solver
% 2.82/0.98  --inst_lit_activity_flag                true
% 2.82/0.98  --inst_restr_to_given                   false
% 2.82/0.98  --inst_activity_threshold               500
% 2.82/0.98  --inst_out_proof                        true
% 2.82/0.98  
% 2.82/0.98  ------ Resolution Options
% 2.82/0.98  
% 2.82/0.98  --resolution_flag                       true
% 2.82/0.98  --res_lit_sel                           adaptive
% 2.82/0.98  --res_lit_sel_side                      none
% 2.82/0.98  --res_ordering                          kbo
% 2.82/0.98  --res_to_prop_solver                    active
% 2.82/0.98  --res_prop_simpl_new                    false
% 2.82/0.98  --res_prop_simpl_given                  true
% 2.82/0.98  --res_passive_queue_type                priority_queues
% 2.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  ------ Parsing...
% 2.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/0.99  ------ Proving...
% 2.82/0.99  ------ Problem Properties 
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  clauses                                 15
% 2.82/0.99  conjectures                             1
% 2.82/0.99  EPR                                     0
% 2.82/0.99  Horn                                    13
% 2.82/0.99  unary                                   6
% 2.82/0.99  binary                                  4
% 2.82/0.99  lits                                    30
% 2.82/0.99  lits eq                                 12
% 2.82/0.99  fd_pure                                 0
% 2.82/0.99  fd_pseudo                               0
% 2.82/0.99  fd_cond                                 0
% 2.82/0.99  fd_pseudo_cond                          3
% 2.82/0.99  AC symbols                              0
% 2.82/0.99  
% 2.82/0.99  ------ Schedule dynamic 5 is on 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ 
% 2.82/0.99  Current options:
% 2.82/0.99  ------ 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options
% 2.82/0.99  
% 2.82/0.99  --out_options                           all
% 2.82/0.99  --tptp_safe_out                         true
% 2.82/0.99  --problem_path                          ""
% 2.82/0.99  --include_path                          ""
% 2.82/0.99  --clausifier                            res/vclausify_rel
% 2.82/0.99  --clausifier_options                    --mode clausify
% 2.82/0.99  --stdin                                 false
% 2.82/0.99  --stats_out                             all
% 2.82/0.99  
% 2.82/0.99  ------ General Options
% 2.82/0.99  
% 2.82/0.99  --fof                                   false
% 2.82/0.99  --time_out_real                         305.
% 2.82/0.99  --time_out_virtual                      -1.
% 2.82/0.99  --symbol_type_check                     false
% 2.82/0.99  --clausify_out                          false
% 2.82/0.99  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/0.99  --bc_imp_inh                            [conj_cone]
% 2.82/0.99  --conj_cone_tolerance                   3.
% 2.82/0.99  --extra_neg_conj                        none
% 2.82/0.99  --large_theory_mode                     true
% 2.82/0.99  --prolific_symb_bound                   200
% 2.82/0.99  --lt_threshold                          2000
% 2.82/0.99  --clause_weak_htbl                      true
% 2.82/0.99  --gc_record_bc_elim                     false
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing Options
% 2.82/0.99  
% 2.82/0.99  --preprocessing_flag                    true
% 2.82/0.99  --time_out_prep_mult                    0.1
% 2.82/0.99  --splitting_mode                        input
% 2.82/0.99  --splitting_grd                         true
% 2.82/0.99  --splitting_cvd                         false
% 2.82/0.99  --splitting_cvd_svl                     false
% 2.82/0.99  --splitting_nvd                         32
% 2.82/0.99  --sub_typing                            true
% 2.82/0.99  --prep_gs_sim                           true
% 2.82/0.99  --prep_unflatten                        true
% 2.82/0.99  --prep_res_sim                          true
% 2.82/0.99  --prep_upred                            true
% 2.82/0.99  --prep_sem_filter                       exhaustive
% 2.82/0.99  --prep_sem_filter_out                   false
% 2.82/0.99  --pred_elim                             true
% 2.82/0.99  --res_sim_input                         true
% 2.82/0.99  --eq_ax_congr_red                       true
% 2.82/0.99  --pure_diseq_elim                       true
% 2.82/0.99  --brand_transform                       false
% 2.82/0.99  --non_eq_to_eq                          false
% 2.82/0.99  --prep_def_merge                        true
% 2.82/0.99  --prep_def_merge_prop_impl              false
% 2.82/0.99  --prep_def_merge_mbd                    true
% 2.82/0.99  --prep_def_merge_tr_red                 false
% 2.82/0.99  --prep_def_merge_tr_cl                  false
% 2.82/0.99  --smt_preprocessing                     true
% 2.82/0.99  --smt_ac_axioms                         fast
% 2.82/0.99  --preprocessed_out                      false
% 2.82/0.99  --preprocessed_stats                    false
% 2.82/0.99  
% 2.82/0.99  ------ Abstraction refinement Options
% 2.82/0.99  
% 2.82/0.99  --abstr_ref                             []
% 2.82/0.99  --abstr_ref_prep                        false
% 2.82/0.99  --abstr_ref_until_sat                   false
% 2.82/0.99  --abstr_ref_sig_restrict                funpre
% 2.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.99  --abstr_ref_under                       []
% 2.82/0.99  
% 2.82/0.99  ------ SAT Options
% 2.82/0.99  
% 2.82/0.99  --sat_mode                              false
% 2.82/0.99  --sat_fm_restart_options                ""
% 2.82/0.99  --sat_gr_def                            false
% 2.82/0.99  --sat_epr_types                         true
% 2.82/0.99  --sat_non_cyclic_types                  false
% 2.82/0.99  --sat_finite_models                     false
% 2.82/0.99  --sat_fm_lemmas                         false
% 2.82/0.99  --sat_fm_prep                           false
% 2.82/0.99  --sat_fm_uc_incr                        true
% 2.82/0.99  --sat_out_model                         small
% 2.82/0.99  --sat_out_clauses                       false
% 2.82/0.99  
% 2.82/0.99  ------ QBF Options
% 2.82/0.99  
% 2.82/0.99  --qbf_mode                              false
% 2.82/0.99  --qbf_elim_univ                         false
% 2.82/0.99  --qbf_dom_inst                          none
% 2.82/0.99  --qbf_dom_pre_inst                      false
% 2.82/0.99  --qbf_sk_in                             false
% 2.82/0.99  --qbf_pred_elim                         true
% 2.82/0.99  --qbf_split                             512
% 2.82/0.99  
% 2.82/0.99  ------ BMC1 Options
% 2.82/0.99  
% 2.82/0.99  --bmc1_incremental                      false
% 2.82/0.99  --bmc1_axioms                           reachable_all
% 2.82/0.99  --bmc1_min_bound                        0
% 2.82/0.99  --bmc1_max_bound                        -1
% 2.82/0.99  --bmc1_max_bound_default                -1
% 2.82/0.99  --bmc1_symbol_reachability              true
% 2.82/0.99  --bmc1_property_lemmas                  false
% 2.82/0.99  --bmc1_k_induction                      false
% 2.82/0.99  --bmc1_non_equiv_states                 false
% 2.82/0.99  --bmc1_deadlock                         false
% 2.82/0.99  --bmc1_ucm                              false
% 2.82/0.99  --bmc1_add_unsat_core                   none
% 2.82/0.99  --bmc1_unsat_core_children              false
% 2.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.99  --bmc1_out_stat                         full
% 2.82/0.99  --bmc1_ground_init                      false
% 2.82/0.99  --bmc1_pre_inst_next_state              false
% 2.82/0.99  --bmc1_pre_inst_state                   false
% 2.82/0.99  --bmc1_pre_inst_reach_state             false
% 2.82/0.99  --bmc1_out_unsat_core                   false
% 2.82/0.99  --bmc1_aig_witness_out                  false
% 2.82/0.99  --bmc1_verbose                          false
% 2.82/0.99  --bmc1_dump_clauses_tptp                false
% 2.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.99  --bmc1_dump_file                        -
% 2.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.99  --bmc1_ucm_extend_mode                  1
% 2.82/0.99  --bmc1_ucm_init_mode                    2
% 2.82/0.99  --bmc1_ucm_cone_mode                    none
% 2.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.99  --bmc1_ucm_relax_model                  4
% 2.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.99  --bmc1_ucm_layered_model                none
% 2.82/0.99  --bmc1_ucm_max_lemma_size               10
% 2.82/0.99  
% 2.82/0.99  ------ AIG Options
% 2.82/0.99  
% 2.82/0.99  --aig_mode                              false
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation Options
% 2.82/0.99  
% 2.82/0.99  --instantiation_flag                    true
% 2.82/0.99  --inst_sos_flag                         false
% 2.82/0.99  --inst_sos_phase                        true
% 2.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel_side                     none
% 2.82/0.99  --inst_solver_per_active                1400
% 2.82/0.99  --inst_solver_calls_frac                1.
% 2.82/0.99  --inst_passive_queue_type               priority_queues
% 2.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.99  --inst_passive_queues_freq              [25;2]
% 2.82/0.99  --inst_dismatching                      true
% 2.82/0.99  --inst_eager_unprocessed_to_passive     true
% 2.82/0.99  --inst_prop_sim_given                   true
% 2.82/0.99  --inst_prop_sim_new                     false
% 2.82/0.99  --inst_subs_new                         false
% 2.82/0.99  --inst_eq_res_simp                      false
% 2.82/0.99  --inst_subs_given                       false
% 2.82/0.99  --inst_orphan_elimination               true
% 2.82/0.99  --inst_learning_loop_flag               true
% 2.82/0.99  --inst_learning_start                   3000
% 2.82/0.99  --inst_learning_factor                  2
% 2.82/0.99  --inst_start_prop_sim_after_learn       3
% 2.82/0.99  --inst_sel_renew                        solver
% 2.82/0.99  --inst_lit_activity_flag                true
% 2.82/0.99  --inst_restr_to_given                   false
% 2.82/0.99  --inst_activity_threshold               500
% 2.82/0.99  --inst_out_proof                        true
% 2.82/0.99  
% 2.82/0.99  ------ Resolution Options
% 2.82/0.99  
% 2.82/0.99  --resolution_flag                       false
% 2.82/0.99  --res_lit_sel                           adaptive
% 2.82/0.99  --res_lit_sel_side                      none
% 2.82/0.99  --res_ordering                          kbo
% 2.82/0.99  --res_to_prop_solver                    active
% 2.82/0.99  --res_prop_simpl_new                    false
% 2.82/0.99  --res_prop_simpl_given                  true
% 2.82/0.99  --res_passive_queue_type                priority_queues
% 2.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ Proving...
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  % SZS status Theorem for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99   Resolution empty clause
% 2.82/0.99  
% 2.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  fof(f2,axiom,(
% 2.82/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f15,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.82/0.99    inference(nnf_transformation,[],[f2])).
% 2.82/0.99  
% 2.82/0.99  fof(f16,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.82/0.99    inference(flattening,[],[f15])).
% 2.82/0.99  
% 2.82/0.99  fof(f17,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.82/0.99    inference(rectify,[],[f16])).
% 2.82/0.99  
% 2.82/0.99  fof(f18,plain,(
% 2.82/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f19,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 2.82/0.99  
% 2.82/0.99  fof(f28,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f19])).
% 2.82/0.99  
% 2.82/0.99  fof(f8,axiom,(
% 2.82/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f36,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f8])).
% 2.82/0.99  
% 2.82/0.99  fof(f46,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.82/0.99    inference(definition_unfolding,[],[f28,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f1,axiom,(
% 2.82/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f24,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f1])).
% 2.82/0.99  
% 2.82/0.99  fof(f43,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 2.82/0.99    inference(definition_unfolding,[],[f24,f36,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f11,conjecture,(
% 2.82/0.99    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f12,negated_conjecture,(
% 2.82/0.99    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 2.82/0.99    inference(negated_conjecture,[],[f11])).
% 2.82/0.99  
% 2.82/0.99  fof(f14,plain,(
% 2.82/0.99    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0),
% 2.82/0.99    inference(ennf_transformation,[],[f12])).
% 2.82/0.99  
% 2.82/0.99  fof(f22,plain,(
% 2.82/0.99    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f23,plain,(
% 2.82/0.99    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f22])).
% 2.82/0.99  
% 2.82/0.99  fof(f41,plain,(
% 2.82/0.99    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 2.82/0.99    inference(cnf_transformation,[],[f23])).
% 2.82/0.99  
% 2.82/0.99  fof(f52,plain,(
% 2.82/0.99    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3))),
% 2.82/0.99    inference(definition_unfolding,[],[f41,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f26,plain,(
% 2.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.82/0.99    inference(cnf_transformation,[],[f19])).
% 2.82/0.99  
% 2.82/0.99  fof(f48,plain,(
% 2.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 2.82/0.99    inference(definition_unfolding,[],[f26,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f54,plain,(
% 2.82/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.82/0.99    inference(equality_resolution,[],[f48])).
% 2.82/0.99  
% 2.82/0.99  fof(f3,axiom,(
% 2.82/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f13,plain,(
% 2.82/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.82/0.99    inference(ennf_transformation,[],[f3])).
% 2.82/0.99  
% 2.82/0.99  fof(f31,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f13])).
% 2.82/0.99  
% 2.82/0.99  fof(f50,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.82/0.99    inference(definition_unfolding,[],[f31,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f4,axiom,(
% 2.82/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f32,plain,(
% 2.82/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f4])).
% 2.82/0.99  
% 2.82/0.99  fof(f30,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f19])).
% 2.82/0.99  
% 2.82/0.99  fof(f44,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.82/0.99    inference(definition_unfolding,[],[f30,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f27,plain,(
% 2.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.82/0.99    inference(cnf_transformation,[],[f19])).
% 2.82/0.99  
% 2.82/0.99  fof(f47,plain,(
% 2.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 2.82/0.99    inference(definition_unfolding,[],[f27,f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f53,plain,(
% 2.82/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.82/0.99    inference(equality_resolution,[],[f47])).
% 2.82/0.99  
% 2.82/0.99  fof(f5,axiom,(
% 2.82/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f33,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f5])).
% 2.82/0.99  
% 2.82/0.99  fof(f6,axiom,(
% 2.82/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f34,plain,(
% 2.82/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f6])).
% 2.82/0.99  
% 2.82/0.99  fof(f42,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 2.82/0.99    inference(definition_unfolding,[],[f33,f36,f34,f34])).
% 2.82/0.99  
% 2.82/0.99  fof(f10,axiom,(
% 2.82/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f40,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 2.82/0.99    inference(cnf_transformation,[],[f10])).
% 2.82/0.99  
% 2.82/0.99  fof(f51,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) )),
% 2.82/0.99    inference(definition_unfolding,[],[f40,f36,f34])).
% 2.82/0.99  
% 2.82/0.99  fof(f9,axiom,(
% 2.82/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.82/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f20,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.82/0.99    inference(nnf_transformation,[],[f9])).
% 2.82/0.99  
% 2.82/0.99  fof(f21,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.82/0.99    inference(flattening,[],[f20])).
% 2.82/0.99  
% 2.82/0.99  fof(f39,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f21])).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4,plain,
% 2.82/0.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.82/0.99      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 2.82/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_420,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_15,negated_conjecture,
% 2.82/0.99      ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_528,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1,c_15]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6,plain,
% 2.82/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 2.82/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_418,plain,
% 2.82/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.82/0.99      | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1206,plain,
% 2.82/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 2.82/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_528,c_418]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3285,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(sK3,X0)) = X1
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,X1),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_420,c_1206]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_8,plain,
% 2.82/0.99      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 2.82/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_9,plain,
% 2.82/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_138,plain,
% 2.82/0.99      ( X0 != X1 | k3_tarski(k2_tarski(X2,X1)) = X1 | k1_xboole_0 != X2 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_139,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_138]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1205,plain,
% 2.82/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.82/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_139,c_418]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6358,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(sK3,X0)) = X1
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3285,c_1205]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6375,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(sK3,X0)) = sK3
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,sK3),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,X0,sK3),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_6358,c_1206]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3318,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X1
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_420,c_1205]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_529,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1,c_139]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3398,plain,
% 2.82/0.99      ( X0 = X1
% 2.82/0.99      | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_3318,c_529]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2,plain,
% 2.82/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.82/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.82/0.99      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 2.82/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_422,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4405,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0
% 2.82/0.99      | k1_xboole_0 = X0
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_3398,c_422]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4601,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0
% 2.82/0.99      | k1_xboole_0 = X0
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4405,c_3398]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4602,plain,
% 2.82/0.99      ( k1_xboole_0 = X0
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(X0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_4601,c_529]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4857,plain,
% 2.82/0.99      ( sK3 = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_4602,c_1206]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4401,plain,
% 2.82/0.99      ( sK3 = X0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,X0),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_3398,c_1206]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4782,plain,
% 2.82/0.99      ( sK3 = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_4401]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5243,plain,
% 2.82/0.99      ( sK3 = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4857,c_4782]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5249,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(sK3,k1_xboole_0)) = k1_xboole_0
% 2.82/0.99      | sK3 = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_5243,c_422]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5487,plain,
% 2.82/0.99      ( sK3 = X0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,X0),X1) = iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4401,c_1205]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5527,plain,
% 2.82/0.99      ( sK3 = X0
% 2.82/0.99      | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top
% 2.82/0.99      | iProver_top != iProver_top ),
% 2.82/0.99      inference(equality_factoring,[status(thm)],[c_5487]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5529,plain,
% 2.82/0.99      ( sK3 = X0 | r2_hidden(sK0(sK3,k1_xboole_0,X0),X0) = iProver_top ),
% 2.82/0.99      inference(equality_resolution_simp,[status(thm)],[c_5527]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5709,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(sK3,k1_xboole_0)) = k1_xboole_0
% 2.82/0.99      | sK3 = k1_xboole_0 ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5249,c_5529]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5710,plain,
% 2.82/0.99      ( sK3 = k1_xboole_0 ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_5709,c_529]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_8523,plain,
% 2.82/0.99      ( k1_xboole_0 = X0
% 2.82/0.99      | r2_hidden(sK0(k1_xboole_0,X0,k1_xboole_0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(k1_xboole_0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(light_normalisation,[status(thm)],[c_6375,c_139,c_5710]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5,plain,
% 2.82/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 2.82/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_419,plain,
% 2.82/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.82/0.99      | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1508,plain,
% 2.82/0.99      ( r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top
% 2.82/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_528,c_419]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4859,plain,
% 2.82/0.99      ( k2_tarski(sK1,sK2) = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_4602,c_1508]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4403,plain,
% 2.82/0.99      ( k2_tarski(sK1,sK2) = X0
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,X0),X0) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,X0),X1) = iProver_top
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_3398,c_1508]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4788,plain,
% 2.82/0.99      ( k2_tarski(sK1,sK2) = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_4403]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5268,plain,
% 2.82/0.99      ( k2_tarski(sK1,sK2) = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4859,c_4788]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_0,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_14,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) != k1_xboole_0 ),
% 2.82/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_801,plain,
% 2.82/0.99      ( k2_tarski(X0,X1) != k1_xboole_0 ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5274,plain,
% 2.82/0.99      ( r2_hidden(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5268,c_801]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_11,plain,
% 2.82/0.99      ( r1_tarski(k2_tarski(X0,X1),X2)
% 2.82/0.99      | ~ r2_hidden(X1,X2)
% 2.82/0.99      | ~ r2_hidden(X0,X2) ),
% 2.82/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_144,plain,
% 2.82/0.99      ( ~ r2_hidden(X0,X1)
% 2.82/0.99      | ~ r2_hidden(X2,X1)
% 2.82/0.99      | X1 != X3
% 2.82/0.99      | k2_tarski(X2,X0) != X4
% 2.82/0.99      | k3_tarski(k2_tarski(X4,X3)) = X3 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_145,plain,
% 2.82/0.99      ( ~ r2_hidden(X0,X1)
% 2.82/0.99      | ~ r2_hidden(X2,X1)
% 2.82/0.99      | k3_tarski(k2_tarski(k2_tarski(X0,X2),X1)) = X1 ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_144]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_416,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X1),X2)) = X2
% 2.82/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.82/0.99      | r2_hidden(X1,X2) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5278,plain,
% 2.82/0.99      ( k3_tarski(k2_tarski(k2_tarski(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),X0),k1_xboole_0)) = k1_xboole_0
% 2.82/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_5274,c_416]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5666,plain,
% 2.82/0.99      ( k2_tarski(sK0(k2_tarski(sK1,sK2),k1_xboole_0,k1_xboole_0),X0) = k1_xboole_0
% 2.82/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_5278,c_529]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_8123,plain,
% 2.82/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5666,c_801]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_8527,plain,
% 2.82/0.99      ( k1_xboole_0 = X0
% 2.82/0.99      | r2_hidden(sK0(k1_xboole_0,X0,k1_xboole_0),X0) = iProver_top ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_8523,c_8123]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1202,plain,
% 2.82/0.99      ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
% 2.82/0.99      | r2_hidden(X0,k2_tarski(X1,X2)) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_0,c_418]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_8538,plain,
% 2.82/0.99      ( k2_tarski(X0,X0) = k1_xboole_0
% 2.82/0.99      | r2_hidden(sK0(k1_xboole_0,k2_tarski(X0,X0),k1_xboole_0),k2_tarski(X0,X1)) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_8527,c_1202]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_688,plain,
% 2.82/0.99      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_529,c_14]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_9365,plain,
% 2.82/0.99      ( r2_hidden(sK0(k1_xboole_0,k2_tarski(X0,X0),k1_xboole_0),k2_tarski(X0,X1)) = iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8538,c_688]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_9387,plain,
% 2.82/0.99      ( r2_hidden(sK0(k1_xboole_0,k2_tarski(sK1,sK1),k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_9365,c_1508]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_9428,plain,
% 2.82/0.99      ( $false ),
% 2.82/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_9387,c_8123]) ).
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  ------                               Statistics
% 2.82/0.99  
% 2.82/0.99  ------ General
% 2.82/0.99  
% 2.82/0.99  abstr_ref_over_cycles:                  0
% 2.82/0.99  abstr_ref_under_cycles:                 0
% 2.82/0.99  gc_basic_clause_elim:                   0
% 2.82/0.99  forced_gc_time:                         0
% 2.82/0.99  parsing_time:                           0.008
% 2.82/0.99  unif_index_cands_time:                  0.
% 2.82/0.99  unif_index_add_time:                    0.
% 2.82/0.99  orderings_time:                         0.
% 2.82/0.99  out_proof_time:                         0.008
% 2.82/0.99  total_time:                             0.289
% 2.82/0.99  num_of_symbols:                         41
% 2.82/0.99  num_of_terms:                           12215
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing
% 2.82/0.99  
% 2.82/0.99  num_of_splits:                          0
% 2.82/0.99  num_of_split_atoms:                     0
% 2.82/0.99  num_of_reused_defs:                     0
% 2.82/0.99  num_eq_ax_congr_red:                    19
% 2.82/0.99  num_of_sem_filtered_clauses:            1
% 2.82/0.99  num_of_subtypes:                        0
% 2.82/0.99  monotx_restored_types:                  0
% 2.82/0.99  sat_num_of_epr_types:                   0
% 2.82/0.99  sat_num_of_non_cyclic_types:            0
% 2.82/0.99  sat_guarded_non_collapsed_types:        0
% 2.82/0.99  num_pure_diseq_elim:                    0
% 2.82/0.99  simp_replaced_by:                       0
% 2.82/0.99  res_preprocessed:                       72
% 2.82/0.99  prep_upred:                             0
% 2.82/0.99  prep_unflattend:                        6
% 2.82/0.99  smt_new_axioms:                         0
% 2.82/0.99  pred_elim_cands:                        1
% 2.82/0.99  pred_elim:                              1
% 2.82/0.99  pred_elim_cl:                           1
% 2.82/0.99  pred_elim_cycles:                       3
% 2.82/0.99  merged_defs:                            0
% 2.82/0.99  merged_defs_ncl:                        0
% 2.82/0.99  bin_hyper_res:                          0
% 2.82/0.99  prep_cycles:                            4
% 2.82/0.99  pred_elim_time:                         0.001
% 2.82/0.99  splitting_time:                         0.
% 2.82/0.99  sem_filter_time:                        0.
% 2.82/0.99  monotx_time:                            0.
% 2.82/0.99  subtype_inf_time:                       0.
% 2.82/0.99  
% 2.82/0.99  ------ Problem properties
% 2.82/0.99  
% 2.82/0.99  clauses:                                15
% 2.82/0.99  conjectures:                            1
% 2.82/0.99  epr:                                    0
% 2.82/0.99  horn:                                   13
% 2.82/0.99  ground:                                 1
% 2.82/0.99  unary:                                  6
% 2.82/0.99  binary:                                 4
% 2.82/0.99  lits:                                   30
% 2.82/0.99  lits_eq:                                12
% 2.82/0.99  fd_pure:                                0
% 2.82/0.99  fd_pseudo:                              0
% 2.82/0.99  fd_cond:                                0
% 2.82/0.99  fd_pseudo_cond:                         3
% 2.82/0.99  ac_symbols:                             0
% 2.82/0.99  
% 2.82/0.99  ------ Propositional Solver
% 2.82/0.99  
% 2.82/0.99  prop_solver_calls:                      29
% 2.82/0.99  prop_fast_solver_calls:                 493
% 2.82/0.99  smt_solver_calls:                       0
% 2.82/0.99  smt_fast_solver_calls:                  0
% 2.82/0.99  prop_num_of_clauses:                    2653
% 2.82/0.99  prop_preprocess_simplified:             7107
% 2.82/0.99  prop_fo_subsumed:                       9
% 2.82/0.99  prop_solver_time:                       0.
% 2.82/0.99  smt_solver_time:                        0.
% 2.82/0.99  smt_fast_solver_time:                   0.
% 2.82/0.99  prop_fast_solver_time:                  0.
% 2.82/0.99  prop_unsat_core_time:                   0.
% 2.82/0.99  
% 2.82/0.99  ------ QBF
% 2.82/0.99  
% 2.82/0.99  qbf_q_res:                              0
% 2.82/0.99  qbf_num_tautologies:                    0
% 2.82/0.99  qbf_prep_cycles:                        0
% 2.82/0.99  
% 2.82/0.99  ------ BMC1
% 2.82/0.99  
% 2.82/0.99  bmc1_current_bound:                     -1
% 2.82/0.99  bmc1_last_solved_bound:                 -1
% 2.82/0.99  bmc1_unsat_core_size:                   -1
% 2.82/0.99  bmc1_unsat_core_parents_size:           -1
% 2.82/0.99  bmc1_merge_next_fun:                    0
% 2.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation
% 2.82/0.99  
% 2.82/0.99  inst_num_of_clauses:                    812
% 2.82/0.99  inst_num_in_passive:                    545
% 2.82/0.99  inst_num_in_active:                     237
% 2.82/0.99  inst_num_in_unprocessed:                30
% 2.82/0.99  inst_num_of_loops:                      280
% 2.82/0.99  inst_num_of_learning_restarts:          0
% 2.82/0.99  inst_num_moves_active_passive:          41
% 2.82/0.99  inst_lit_activity:                      0
% 2.82/0.99  inst_lit_activity_moves:                0
% 2.82/0.99  inst_num_tautologies:                   0
% 2.82/0.99  inst_num_prop_implied:                  0
% 2.82/0.99  inst_num_existing_simplified:           0
% 2.82/0.99  inst_num_eq_res_simplified:             0
% 2.82/0.99  inst_num_child_elim:                    0
% 2.82/0.99  inst_num_of_dismatching_blockings:      900
% 2.82/0.99  inst_num_of_non_proper_insts:           887
% 2.82/0.99  inst_num_of_duplicates:                 0
% 2.82/0.99  inst_inst_num_from_inst_to_res:         0
% 2.82/0.99  inst_dismatching_checking_time:         0.
% 2.82/0.99  
% 2.82/0.99  ------ Resolution
% 2.82/0.99  
% 2.82/0.99  res_num_of_clauses:                     0
% 2.82/0.99  res_num_in_passive:                     0
% 2.82/0.99  res_num_in_active:                      0
% 2.82/0.99  res_num_of_loops:                       76
% 2.82/0.99  res_forward_subset_subsumed:            116
% 2.82/0.99  res_backward_subset_subsumed:           0
% 2.82/0.99  res_forward_subsumed:                   0
% 2.82/0.99  res_backward_subsumed:                  0
% 2.82/0.99  res_forward_subsumption_resolution:     0
% 2.82/0.99  res_backward_subsumption_resolution:    0
% 2.82/0.99  res_clause_to_clause_subsumption:       3378
% 2.82/0.99  res_orphan_elimination:                 0
% 2.82/0.99  res_tautology_del:                      91
% 2.82/0.99  res_num_eq_res_simplified:              0
% 2.82/0.99  res_num_sel_changes:                    0
% 2.82/0.99  res_moves_from_active_to_pass:          0
% 2.82/0.99  
% 2.82/0.99  ------ Superposition
% 2.82/0.99  
% 2.82/0.99  sup_time_total:                         0.
% 2.82/0.99  sup_time_generating:                    0.
% 2.82/0.99  sup_time_sim_full:                      0.
% 2.82/0.99  sup_time_sim_immed:                     0.
% 2.82/0.99  
% 2.82/0.99  sup_num_of_clauses:                     289
% 2.82/0.99  sup_num_in_active:                      39
% 2.82/0.99  sup_num_in_passive:                     250
% 2.82/0.99  sup_num_of_loops:                       55
% 2.82/0.99  sup_fw_superposition:                   131
% 2.82/0.99  sup_bw_superposition:                   453
% 2.82/0.99  sup_immediate_simplified:               202
% 2.82/0.99  sup_given_eliminated:                   3
% 2.82/0.99  comparisons_done:                       0
% 2.82/0.99  comparisons_avoided:                    0
% 2.82/0.99  
% 2.82/0.99  ------ Simplifications
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  sim_fw_subset_subsumed:                 56
% 2.82/0.99  sim_bw_subset_subsumed:                 24
% 2.82/0.99  sim_fw_subsumed:                        70
% 2.82/0.99  sim_bw_subsumed:                        8
% 2.82/0.99  sim_fw_subsumption_res:                 13
% 2.82/0.99  sim_bw_subsumption_res:                 6
% 2.82/0.99  sim_tautology_del:                      26
% 2.82/0.99  sim_eq_tautology_del:                   19
% 2.82/0.99  sim_eq_res_simp:                        14
% 2.82/0.99  sim_fw_demodulated:                     43
% 2.82/0.99  sim_bw_demodulated:                     27
% 2.82/0.99  sim_light_normalised:                   12
% 2.82/0.99  sim_joinable_taut:                      0
% 2.82/0.99  sim_joinable_simp:                      0
% 2.82/0.99  sim_ac_normalised:                      0
% 2.82/0.99  sim_smt_subsumption:                    0
% 2.82/0.99  
%------------------------------------------------------------------------------
