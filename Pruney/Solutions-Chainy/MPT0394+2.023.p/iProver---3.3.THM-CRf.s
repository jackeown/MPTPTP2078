%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:42 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 205 expanded)
%              Number of clauses        :   32 (  54 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   20
%              Number of atoms          :  221 ( 468 expanded)
%              Number of equality atoms :  169 ( 359 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(definition_unfolding,[],[f41,f46,f42])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f29,f46])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) != X3 ) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f70,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2))) != X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f71,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2)))) ),
    inference(equality_resolution,[],[f70])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f26])).

fof(f49,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f49,f29])).

cnf(c_13,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1676,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_16,c_15])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_104,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_185,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) = X0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_104])).

cnf(c_186,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_1041,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_186])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_102,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,X1)
    | X1 != X2
    | k4_xboole_0(X3,X2) != X3
    | k2_tarski(X0,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_102,c_14])).

cnf(c_201,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X0),X1) != k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_1025,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) != k2_tarski(X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_1523,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0
    | r2_hidden(X0,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_1025])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1028,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1352,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1028])).

cnf(c_2296,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1523,c_1352])).

cnf(c_2903,plain,
    ( k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1676,c_2296])).

cnf(c_2908,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
    | k2_tarski(X1,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_2903])).

cnf(c_1532,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_13])).

cnf(c_2930,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_tarski(X0,X1))
    | k2_tarski(X1,X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2908,c_1532])).

cnf(c_2931,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))
    | k2_tarski(X1,X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2930,c_16])).

cnf(c_2940,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2931,c_2296])).

cnf(c_17,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2942,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2940,c_17])).

cnf(c_2948,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2942])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:30:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.24/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/0.98  
% 2.24/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.24/0.98  
% 2.24/0.98  ------  iProver source info
% 2.24/0.98  
% 2.24/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.24/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.24/0.98  git: non_committed_changes: false
% 2.24/0.98  git: last_make_outside_of_git: false
% 2.24/0.98  
% 2.24/0.98  ------ 
% 2.24/0.98  
% 2.24/0.98  ------ Input Options
% 2.24/0.98  
% 2.24/0.98  --out_options                           all
% 2.24/0.98  --tptp_safe_out                         true
% 2.24/0.98  --problem_path                          ""
% 2.24/0.98  --include_path                          ""
% 2.24/0.98  --clausifier                            res/vclausify_rel
% 2.24/0.98  --clausifier_options                    --mode clausify
% 2.24/0.98  --stdin                                 false
% 2.24/0.98  --stats_out                             all
% 2.24/0.98  
% 2.24/0.98  ------ General Options
% 2.24/0.98  
% 2.24/0.98  --fof                                   false
% 2.24/0.98  --time_out_real                         305.
% 2.24/0.98  --time_out_virtual                      -1.
% 2.24/0.98  --symbol_type_check                     false
% 2.24/0.98  --clausify_out                          false
% 2.24/0.98  --sig_cnt_out                           false
% 2.24/0.99  --trig_cnt_out                          false
% 2.24/0.99  --trig_cnt_out_tolerance                1.
% 2.24/0.99  --trig_cnt_out_sk_spl                   false
% 2.24/0.99  --abstr_cl_out                          false
% 2.24/0.99  
% 2.24/0.99  ------ Global Options
% 2.24/0.99  
% 2.24/0.99  --schedule                              default
% 2.24/0.99  --add_important_lit                     false
% 2.24/0.99  --prop_solver_per_cl                    1000
% 2.24/0.99  --min_unsat_core                        false
% 2.24/0.99  --soft_assumptions                      false
% 2.24/0.99  --soft_lemma_size                       3
% 2.24/0.99  --prop_impl_unit_size                   0
% 2.24/0.99  --prop_impl_unit                        []
% 2.24/0.99  --share_sel_clauses                     true
% 2.24/0.99  --reset_solvers                         false
% 2.24/0.99  --bc_imp_inh                            [conj_cone]
% 2.24/0.99  --conj_cone_tolerance                   3.
% 2.24/0.99  --extra_neg_conj                        none
% 2.24/0.99  --large_theory_mode                     true
% 2.24/0.99  --prolific_symb_bound                   200
% 2.24/0.99  --lt_threshold                          2000
% 2.24/0.99  --clause_weak_htbl                      true
% 2.24/0.99  --gc_record_bc_elim                     false
% 2.24/0.99  
% 2.24/0.99  ------ Preprocessing Options
% 2.24/0.99  
% 2.24/0.99  --preprocessing_flag                    true
% 2.24/0.99  --time_out_prep_mult                    0.1
% 2.24/0.99  --splitting_mode                        input
% 2.24/0.99  --splitting_grd                         true
% 2.24/0.99  --splitting_cvd                         false
% 2.24/0.99  --splitting_cvd_svl                     false
% 2.24/0.99  --splitting_nvd                         32
% 2.24/0.99  --sub_typing                            true
% 2.24/0.99  --prep_gs_sim                           true
% 2.24/0.99  --prep_unflatten                        true
% 2.24/0.99  --prep_res_sim                          true
% 2.24/0.99  --prep_upred                            true
% 2.24/0.99  --prep_sem_filter                       exhaustive
% 2.24/0.99  --prep_sem_filter_out                   false
% 2.24/0.99  --pred_elim                             true
% 2.24/0.99  --res_sim_input                         true
% 2.24/0.99  --eq_ax_congr_red                       true
% 2.24/0.99  --pure_diseq_elim                       true
% 2.24/0.99  --brand_transform                       false
% 2.24/0.99  --non_eq_to_eq                          false
% 2.24/0.99  --prep_def_merge                        true
% 2.24/0.99  --prep_def_merge_prop_impl              false
% 2.24/0.99  --prep_def_merge_mbd                    true
% 2.24/0.99  --prep_def_merge_tr_red                 false
% 2.24/0.99  --prep_def_merge_tr_cl                  false
% 2.24/0.99  --smt_preprocessing                     true
% 2.24/0.99  --smt_ac_axioms                         fast
% 2.24/0.99  --preprocessed_out                      false
% 2.24/0.99  --preprocessed_stats                    false
% 2.24/0.99  
% 2.24/0.99  ------ Abstraction refinement Options
% 2.24/0.99  
% 2.24/0.99  --abstr_ref                             []
% 2.24/0.99  --abstr_ref_prep                        false
% 2.24/0.99  --abstr_ref_until_sat                   false
% 2.24/0.99  --abstr_ref_sig_restrict                funpre
% 2.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/0.99  --abstr_ref_under                       []
% 2.24/0.99  
% 2.24/0.99  ------ SAT Options
% 2.24/0.99  
% 2.24/0.99  --sat_mode                              false
% 2.24/0.99  --sat_fm_restart_options                ""
% 2.24/0.99  --sat_gr_def                            false
% 2.24/0.99  --sat_epr_types                         true
% 2.24/0.99  --sat_non_cyclic_types                  false
% 2.24/0.99  --sat_finite_models                     false
% 2.24/0.99  --sat_fm_lemmas                         false
% 2.24/0.99  --sat_fm_prep                           false
% 2.24/0.99  --sat_fm_uc_incr                        true
% 2.24/0.99  --sat_out_model                         small
% 2.24/0.99  --sat_out_clauses                       false
% 2.24/0.99  
% 2.24/0.99  ------ QBF Options
% 2.24/0.99  
% 2.24/0.99  --qbf_mode                              false
% 2.24/0.99  --qbf_elim_univ                         false
% 2.24/0.99  --qbf_dom_inst                          none
% 2.24/0.99  --qbf_dom_pre_inst                      false
% 2.24/0.99  --qbf_sk_in                             false
% 2.24/0.99  --qbf_pred_elim                         true
% 2.24/0.99  --qbf_split                             512
% 2.24/0.99  
% 2.24/0.99  ------ BMC1 Options
% 2.24/0.99  
% 2.24/0.99  --bmc1_incremental                      false
% 2.24/0.99  --bmc1_axioms                           reachable_all
% 2.24/0.99  --bmc1_min_bound                        0
% 2.24/0.99  --bmc1_max_bound                        -1
% 2.24/0.99  --bmc1_max_bound_default                -1
% 2.24/0.99  --bmc1_symbol_reachability              true
% 2.24/0.99  --bmc1_property_lemmas                  false
% 2.24/0.99  --bmc1_k_induction                      false
% 2.24/0.99  --bmc1_non_equiv_states                 false
% 2.24/0.99  --bmc1_deadlock                         false
% 2.24/0.99  --bmc1_ucm                              false
% 2.24/0.99  --bmc1_add_unsat_core                   none
% 2.24/0.99  --bmc1_unsat_core_children              false
% 2.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/0.99  --bmc1_out_stat                         full
% 2.24/0.99  --bmc1_ground_init                      false
% 2.24/0.99  --bmc1_pre_inst_next_state              false
% 2.24/0.99  --bmc1_pre_inst_state                   false
% 2.24/0.99  --bmc1_pre_inst_reach_state             false
% 2.24/0.99  --bmc1_out_unsat_core                   false
% 2.24/0.99  --bmc1_aig_witness_out                  false
% 2.24/0.99  --bmc1_verbose                          false
% 2.24/0.99  --bmc1_dump_clauses_tptp                false
% 2.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.24/0.99  --bmc1_dump_file                        -
% 2.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.24/0.99  --bmc1_ucm_extend_mode                  1
% 2.24/0.99  --bmc1_ucm_init_mode                    2
% 2.24/0.99  --bmc1_ucm_cone_mode                    none
% 2.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.24/0.99  --bmc1_ucm_relax_model                  4
% 2.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/0.99  --bmc1_ucm_layered_model                none
% 2.24/0.99  --bmc1_ucm_max_lemma_size               10
% 2.24/0.99  
% 2.24/0.99  ------ AIG Options
% 2.24/0.99  
% 2.24/0.99  --aig_mode                              false
% 2.24/0.99  
% 2.24/0.99  ------ Instantiation Options
% 2.24/0.99  
% 2.24/0.99  --instantiation_flag                    true
% 2.24/0.99  --inst_sos_flag                         false
% 2.24/0.99  --inst_sos_phase                        true
% 2.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/0.99  --inst_lit_sel_side                     num_symb
% 2.24/0.99  --inst_solver_per_active                1400
% 2.24/0.99  --inst_solver_calls_frac                1.
% 2.24/0.99  --inst_passive_queue_type               priority_queues
% 2.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/0.99  --inst_passive_queues_freq              [25;2]
% 2.24/0.99  --inst_dismatching                      true
% 2.24/0.99  --inst_eager_unprocessed_to_passive     true
% 2.24/0.99  --inst_prop_sim_given                   true
% 2.24/0.99  --inst_prop_sim_new                     false
% 2.24/0.99  --inst_subs_new                         false
% 2.24/0.99  --inst_eq_res_simp                      false
% 2.24/0.99  --inst_subs_given                       false
% 2.24/0.99  --inst_orphan_elimination               true
% 2.24/0.99  --inst_learning_loop_flag               true
% 2.24/0.99  --inst_learning_start                   3000
% 2.24/0.99  --inst_learning_factor                  2
% 2.24/0.99  --inst_start_prop_sim_after_learn       3
% 2.24/0.99  --inst_sel_renew                        solver
% 2.24/0.99  --inst_lit_activity_flag                true
% 2.24/0.99  --inst_restr_to_given                   false
% 2.24/0.99  --inst_activity_threshold               500
% 2.24/0.99  --inst_out_proof                        true
% 2.24/0.99  
% 2.24/0.99  ------ Resolution Options
% 2.24/0.99  
% 2.24/0.99  --resolution_flag                       true
% 2.24/0.99  --res_lit_sel                           adaptive
% 2.24/0.99  --res_lit_sel_side                      none
% 2.24/0.99  --res_ordering                          kbo
% 2.24/0.99  --res_to_prop_solver                    active
% 2.24/0.99  --res_prop_simpl_new                    false
% 2.24/0.99  --res_prop_simpl_given                  true
% 2.24/0.99  --res_passive_queue_type                priority_queues
% 2.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/0.99  --res_passive_queues_freq               [15;5]
% 2.24/0.99  --res_forward_subs                      full
% 2.24/0.99  --res_backward_subs                     full
% 2.24/0.99  --res_forward_subs_resolution           true
% 2.24/0.99  --res_backward_subs_resolution          true
% 2.24/0.99  --res_orphan_elimination                true
% 2.24/0.99  --res_time_limit                        2.
% 2.24/0.99  --res_out_proof                         true
% 2.24/0.99  
% 2.24/0.99  ------ Superposition Options
% 2.24/0.99  
% 2.24/0.99  --superposition_flag                    true
% 2.24/0.99  --sup_passive_queue_type                priority_queues
% 2.24/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.24/0.99  --demod_completeness_check              fast
% 2.24/0.99  --demod_use_ground                      true
% 2.24/0.99  --sup_to_prop_solver                    passive
% 2.24/0.99  --sup_prop_simpl_new                    true
% 2.24/0.99  --sup_prop_simpl_given                  true
% 2.24/0.99  --sup_fun_splitting                     false
% 2.24/0.99  --sup_smt_interval                      50000
% 2.24/0.99  
% 2.24/0.99  ------ Superposition Simplification Setup
% 2.24/0.99  
% 2.24/0.99  --sup_indices_passive                   []
% 2.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.99  --sup_full_bw                           [BwDemod]
% 2.24/0.99  --sup_immed_triv                        [TrivRules]
% 2.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.99  --sup_immed_bw_main                     []
% 2.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.99  
% 2.24/0.99  ------ Combination Options
% 2.24/0.99  
% 2.24/0.99  --comb_res_mult                         3
% 2.24/0.99  --comb_sup_mult                         2
% 2.24/0.99  --comb_inst_mult                        10
% 2.24/0.99  
% 2.24/0.99  ------ Debug Options
% 2.24/0.99  
% 2.24/0.99  --dbg_backtrace                         false
% 2.24/0.99  --dbg_dump_prop_clauses                 false
% 2.24/0.99  --dbg_dump_prop_clauses_file            -
% 2.24/0.99  --dbg_out_stat                          false
% 2.24/0.99  ------ Parsing...
% 2.24/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.24/0.99  
% 2.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.24/0.99  
% 2.24/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.24/0.99  
% 2.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.24/0.99  ------ Proving...
% 2.24/0.99  ------ Problem Properties 
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  clauses                                 17
% 2.24/0.99  conjectures                             1
% 2.24/0.99  EPR                                     1
% 2.24/0.99  Horn                                    14
% 2.24/0.99  unary                                   10
% 2.24/0.99  binary                                  1
% 2.24/0.99  lits                                    33
% 2.24/0.99  lits eq                                 23
% 2.24/0.99  fd_pure                                 0
% 2.24/0.99  fd_pseudo                               0
% 2.24/0.99  fd_cond                                 1
% 2.24/0.99  fd_pseudo_cond                          4
% 2.24/0.99  AC symbols                              0
% 2.24/0.99  
% 2.24/0.99  ------ Schedule dynamic 5 is on 
% 2.24/0.99  
% 2.24/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  ------ 
% 2.24/0.99  Current options:
% 2.24/0.99  ------ 
% 2.24/0.99  
% 2.24/0.99  ------ Input Options
% 2.24/0.99  
% 2.24/0.99  --out_options                           all
% 2.24/0.99  --tptp_safe_out                         true
% 2.24/0.99  --problem_path                          ""
% 2.24/0.99  --include_path                          ""
% 2.24/0.99  --clausifier                            res/vclausify_rel
% 2.24/0.99  --clausifier_options                    --mode clausify
% 2.24/0.99  --stdin                                 false
% 2.24/0.99  --stats_out                             all
% 2.24/0.99  
% 2.24/0.99  ------ General Options
% 2.24/0.99  
% 2.24/0.99  --fof                                   false
% 2.24/0.99  --time_out_real                         305.
% 2.24/0.99  --time_out_virtual                      -1.
% 2.24/0.99  --symbol_type_check                     false
% 2.24/0.99  --clausify_out                          false
% 2.24/0.99  --sig_cnt_out                           false
% 2.24/0.99  --trig_cnt_out                          false
% 2.24/0.99  --trig_cnt_out_tolerance                1.
% 2.24/0.99  --trig_cnt_out_sk_spl                   false
% 2.24/0.99  --abstr_cl_out                          false
% 2.24/0.99  
% 2.24/0.99  ------ Global Options
% 2.24/0.99  
% 2.24/0.99  --schedule                              default
% 2.24/0.99  --add_important_lit                     false
% 2.24/0.99  --prop_solver_per_cl                    1000
% 2.24/0.99  --min_unsat_core                        false
% 2.24/0.99  --soft_assumptions                      false
% 2.24/0.99  --soft_lemma_size                       3
% 2.24/0.99  --prop_impl_unit_size                   0
% 2.24/0.99  --prop_impl_unit                        []
% 2.24/0.99  --share_sel_clauses                     true
% 2.24/0.99  --reset_solvers                         false
% 2.24/0.99  --bc_imp_inh                            [conj_cone]
% 2.24/0.99  --conj_cone_tolerance                   3.
% 2.24/0.99  --extra_neg_conj                        none
% 2.24/0.99  --large_theory_mode                     true
% 2.24/0.99  --prolific_symb_bound                   200
% 2.24/0.99  --lt_threshold                          2000
% 2.24/0.99  --clause_weak_htbl                      true
% 2.24/0.99  --gc_record_bc_elim                     false
% 2.24/0.99  
% 2.24/0.99  ------ Preprocessing Options
% 2.24/0.99  
% 2.24/0.99  --preprocessing_flag                    true
% 2.24/0.99  --time_out_prep_mult                    0.1
% 2.24/0.99  --splitting_mode                        input
% 2.24/0.99  --splitting_grd                         true
% 2.24/0.99  --splitting_cvd                         false
% 2.24/0.99  --splitting_cvd_svl                     false
% 2.24/0.99  --splitting_nvd                         32
% 2.24/0.99  --sub_typing                            true
% 2.24/0.99  --prep_gs_sim                           true
% 2.24/0.99  --prep_unflatten                        true
% 2.24/0.99  --prep_res_sim                          true
% 2.24/0.99  --prep_upred                            true
% 2.24/0.99  --prep_sem_filter                       exhaustive
% 2.24/0.99  --prep_sem_filter_out                   false
% 2.24/0.99  --pred_elim                             true
% 2.24/0.99  --res_sim_input                         true
% 2.24/0.99  --eq_ax_congr_red                       true
% 2.24/0.99  --pure_diseq_elim                       true
% 2.24/0.99  --brand_transform                       false
% 2.24/0.99  --non_eq_to_eq                          false
% 2.24/0.99  --prep_def_merge                        true
% 2.24/0.99  --prep_def_merge_prop_impl              false
% 2.24/0.99  --prep_def_merge_mbd                    true
% 2.24/0.99  --prep_def_merge_tr_red                 false
% 2.24/0.99  --prep_def_merge_tr_cl                  false
% 2.24/0.99  --smt_preprocessing                     true
% 2.24/0.99  --smt_ac_axioms                         fast
% 2.24/0.99  --preprocessed_out                      false
% 2.24/0.99  --preprocessed_stats                    false
% 2.24/0.99  
% 2.24/0.99  ------ Abstraction refinement Options
% 2.24/0.99  
% 2.24/0.99  --abstr_ref                             []
% 2.24/0.99  --abstr_ref_prep                        false
% 2.24/0.99  --abstr_ref_until_sat                   false
% 2.24/0.99  --abstr_ref_sig_restrict                funpre
% 2.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/0.99  --abstr_ref_under                       []
% 2.24/0.99  
% 2.24/0.99  ------ SAT Options
% 2.24/0.99  
% 2.24/0.99  --sat_mode                              false
% 2.24/0.99  --sat_fm_restart_options                ""
% 2.24/0.99  --sat_gr_def                            false
% 2.24/0.99  --sat_epr_types                         true
% 2.24/0.99  --sat_non_cyclic_types                  false
% 2.24/0.99  --sat_finite_models                     false
% 2.24/0.99  --sat_fm_lemmas                         false
% 2.24/0.99  --sat_fm_prep                           false
% 2.24/0.99  --sat_fm_uc_incr                        true
% 2.24/0.99  --sat_out_model                         small
% 2.24/0.99  --sat_out_clauses                       false
% 2.24/0.99  
% 2.24/0.99  ------ QBF Options
% 2.24/0.99  
% 2.24/0.99  --qbf_mode                              false
% 2.24/0.99  --qbf_elim_univ                         false
% 2.24/0.99  --qbf_dom_inst                          none
% 2.24/0.99  --qbf_dom_pre_inst                      false
% 2.24/0.99  --qbf_sk_in                             false
% 2.24/0.99  --qbf_pred_elim                         true
% 2.24/0.99  --qbf_split                             512
% 2.24/0.99  
% 2.24/0.99  ------ BMC1 Options
% 2.24/0.99  
% 2.24/0.99  --bmc1_incremental                      false
% 2.24/0.99  --bmc1_axioms                           reachable_all
% 2.24/0.99  --bmc1_min_bound                        0
% 2.24/0.99  --bmc1_max_bound                        -1
% 2.24/0.99  --bmc1_max_bound_default                -1
% 2.24/0.99  --bmc1_symbol_reachability              true
% 2.24/0.99  --bmc1_property_lemmas                  false
% 2.24/0.99  --bmc1_k_induction                      false
% 2.24/0.99  --bmc1_non_equiv_states                 false
% 2.24/0.99  --bmc1_deadlock                         false
% 2.24/0.99  --bmc1_ucm                              false
% 2.24/0.99  --bmc1_add_unsat_core                   none
% 2.24/0.99  --bmc1_unsat_core_children              false
% 2.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/0.99  --bmc1_out_stat                         full
% 2.24/0.99  --bmc1_ground_init                      false
% 2.24/0.99  --bmc1_pre_inst_next_state              false
% 2.24/0.99  --bmc1_pre_inst_state                   false
% 2.24/0.99  --bmc1_pre_inst_reach_state             false
% 2.24/0.99  --bmc1_out_unsat_core                   false
% 2.24/0.99  --bmc1_aig_witness_out                  false
% 2.24/0.99  --bmc1_verbose                          false
% 2.24/0.99  --bmc1_dump_clauses_tptp                false
% 2.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.24/0.99  --bmc1_dump_file                        -
% 2.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.24/0.99  --bmc1_ucm_extend_mode                  1
% 2.24/0.99  --bmc1_ucm_init_mode                    2
% 2.24/0.99  --bmc1_ucm_cone_mode                    none
% 2.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.24/0.99  --bmc1_ucm_relax_model                  4
% 2.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/0.99  --bmc1_ucm_layered_model                none
% 2.24/0.99  --bmc1_ucm_max_lemma_size               10
% 2.24/0.99  
% 2.24/0.99  ------ AIG Options
% 2.24/0.99  
% 2.24/0.99  --aig_mode                              false
% 2.24/0.99  
% 2.24/0.99  ------ Instantiation Options
% 2.24/0.99  
% 2.24/0.99  --instantiation_flag                    true
% 2.24/0.99  --inst_sos_flag                         false
% 2.24/0.99  --inst_sos_phase                        true
% 2.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/0.99  --inst_lit_sel_side                     none
% 2.24/0.99  --inst_solver_per_active                1400
% 2.24/0.99  --inst_solver_calls_frac                1.
% 2.24/0.99  --inst_passive_queue_type               priority_queues
% 2.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/0.99  --inst_passive_queues_freq              [25;2]
% 2.24/0.99  --inst_dismatching                      true
% 2.24/0.99  --inst_eager_unprocessed_to_passive     true
% 2.24/0.99  --inst_prop_sim_given                   true
% 2.24/0.99  --inst_prop_sim_new                     false
% 2.24/0.99  --inst_subs_new                         false
% 2.24/0.99  --inst_eq_res_simp                      false
% 2.24/0.99  --inst_subs_given                       false
% 2.24/0.99  --inst_orphan_elimination               true
% 2.24/0.99  --inst_learning_loop_flag               true
% 2.24/0.99  --inst_learning_start                   3000
% 2.24/0.99  --inst_learning_factor                  2
% 2.24/0.99  --inst_start_prop_sim_after_learn       3
% 2.24/0.99  --inst_sel_renew                        solver
% 2.24/0.99  --inst_lit_activity_flag                true
% 2.24/0.99  --inst_restr_to_given                   false
% 2.24/0.99  --inst_activity_threshold               500
% 2.24/0.99  --inst_out_proof                        true
% 2.24/0.99  
% 2.24/0.99  ------ Resolution Options
% 2.24/0.99  
% 2.24/0.99  --resolution_flag                       false
% 2.24/0.99  --res_lit_sel                           adaptive
% 2.24/0.99  --res_lit_sel_side                      none
% 2.24/0.99  --res_ordering                          kbo
% 2.24/0.99  --res_to_prop_solver                    active
% 2.24/0.99  --res_prop_simpl_new                    false
% 2.24/0.99  --res_prop_simpl_given                  true
% 2.24/0.99  --res_passive_queue_type                priority_queues
% 2.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/0.99  --res_passive_queues_freq               [15;5]
% 2.24/0.99  --res_forward_subs                      full
% 2.24/0.99  --res_backward_subs                     full
% 2.24/0.99  --res_forward_subs_resolution           true
% 2.24/0.99  --res_backward_subs_resolution          true
% 2.24/0.99  --res_orphan_elimination                true
% 2.24/0.99  --res_time_limit                        2.
% 2.24/0.99  --res_out_proof                         true
% 2.24/0.99  
% 2.24/0.99  ------ Superposition Options
% 2.24/0.99  
% 2.24/0.99  --superposition_flag                    true
% 2.24/0.99  --sup_passive_queue_type                priority_queues
% 2.24/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.24/0.99  --demod_completeness_check              fast
% 2.24/0.99  --demod_use_ground                      true
% 2.24/0.99  --sup_to_prop_solver                    passive
% 2.24/0.99  --sup_prop_simpl_new                    true
% 2.24/0.99  --sup_prop_simpl_given                  true
% 2.24/0.99  --sup_fun_splitting                     false
% 2.24/0.99  --sup_smt_interval                      50000
% 2.24/0.99  
% 2.24/0.99  ------ Superposition Simplification Setup
% 2.24/0.99  
% 2.24/0.99  --sup_indices_passive                   []
% 2.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.99  --sup_full_bw                           [BwDemod]
% 2.24/0.99  --sup_immed_triv                        [TrivRules]
% 2.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.99  --sup_immed_bw_main                     []
% 2.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.99  
% 2.24/0.99  ------ Combination Options
% 2.24/0.99  
% 2.24/0.99  --comb_res_mult                         3
% 2.24/0.99  --comb_sup_mult                         2
% 2.24/0.99  --comb_inst_mult                        10
% 2.24/0.99  
% 2.24/0.99  ------ Debug Options
% 2.24/0.99  
% 2.24/0.99  --dbg_backtrace                         false
% 2.24/0.99  --dbg_dump_prop_clauses                 false
% 2.24/0.99  --dbg_dump_prop_clauses_file            -
% 2.24/0.99  --dbg_out_stat                          false
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  ------ Proving...
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  % SZS status Theorem for theBenchmark.p
% 2.24/0.99  
% 2.24/0.99   Resolution empty clause
% 2.24/0.99  
% 2.24/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.24/0.99  
% 2.24/0.99  fof(f9,axiom,(
% 2.24/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f44,plain,(
% 2.24/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f9])).
% 2.24/0.99  
% 2.24/0.99  fof(f6,axiom,(
% 2.24/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f41,plain,(
% 2.24/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.24/0.99    inference(cnf_transformation,[],[f6])).
% 2.24/0.99  
% 2.24/0.99  fof(f11,axiom,(
% 2.24/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f46,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.24/0.99    inference(cnf_transformation,[],[f11])).
% 2.24/0.99  
% 2.24/0.99  fof(f7,axiom,(
% 2.24/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f42,plain,(
% 2.24/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f7])).
% 2.24/0.99  
% 2.24/0.99  fof(f50,plain,(
% 2.24/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 2.24/0.99    inference(definition_unfolding,[],[f41,f46,f42])).
% 2.24/0.99  
% 2.24/0.99  fof(f61,plain,(
% 2.24/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 2.24/0.99    inference(definition_unfolding,[],[f44,f50])).
% 2.24/0.99  
% 2.24/0.99  fof(f13,axiom,(
% 2.24/0.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f48,plain,(
% 2.24/0.99    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.24/0.99    inference(cnf_transformation,[],[f13])).
% 2.24/0.99  
% 2.24/0.99  fof(f64,plain,(
% 2.24/0.99    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.24/0.99    inference(definition_unfolding,[],[f48,f42])).
% 2.24/0.99  
% 2.24/0.99  fof(f12,axiom,(
% 2.24/0.99    ! [X0,X1] : ~(k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f18,plain,(
% 2.24/0.99    ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.24/0.99    inference(ennf_transformation,[],[f12])).
% 2.24/0.99  
% 2.24/0.99  fof(f47,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.24/0.99    inference(cnf_transformation,[],[f18])).
% 2.24/0.99  
% 2.24/0.99  fof(f2,axiom,(
% 2.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f29,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.24/0.99    inference(cnf_transformation,[],[f2])).
% 2.24/0.99  
% 2.24/0.99  fof(f63,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.24/0.99    inference(definition_unfolding,[],[f47,f29,f46])).
% 2.24/0.99  
% 2.24/0.99  fof(f1,axiom,(
% 2.24/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f28,plain,(
% 2.24/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f1])).
% 2.24/0.99  
% 2.24/0.99  fof(f52,plain,(
% 2.24/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.24/0.99    inference(definition_unfolding,[],[f28,f29])).
% 2.24/0.99  
% 2.24/0.99  fof(f3,axiom,(
% 2.24/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f30,plain,(
% 2.24/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f3])).
% 2.24/0.99  
% 2.24/0.99  fof(f4,axiom,(
% 2.24/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f20,plain,(
% 2.24/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.24/0.99    inference(nnf_transformation,[],[f4])).
% 2.24/0.99  
% 2.24/0.99  fof(f31,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f20])).
% 2.24/0.99  
% 2.24/0.99  fof(f32,plain,(
% 2.24/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.24/0.99    inference(cnf_transformation,[],[f20])).
% 2.24/0.99  
% 2.24/0.99  fof(f10,axiom,(
% 2.24/0.99    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f17,plain,(
% 2.24/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.24/0.99    inference(ennf_transformation,[],[f10])).
% 2.24/0.99  
% 2.24/0.99  fof(f45,plain,(
% 2.24/0.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f17])).
% 2.24/0.99  
% 2.24/0.99  fof(f62,plain,(
% 2.24/0.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_tarski(X0,X0),X1)) )),
% 2.24/0.99    inference(definition_unfolding,[],[f45,f42])).
% 2.24/0.99  
% 2.24/0.99  fof(f8,axiom,(
% 2.24/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f43,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.24/0.99    inference(cnf_transformation,[],[f8])).
% 2.24/0.99  
% 2.24/0.99  fof(f51,plain,(
% 2.24/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 2.24/0.99    inference(definition_unfolding,[],[f43,f50])).
% 2.24/0.99  
% 2.24/0.99  fof(f5,axiom,(
% 2.24/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f16,plain,(
% 2.24/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.24/0.99    inference(ennf_transformation,[],[f5])).
% 2.24/0.99  
% 2.24/0.99  fof(f21,plain,(
% 2.24/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.99    inference(nnf_transformation,[],[f16])).
% 2.24/0.99  
% 2.24/0.99  fof(f22,plain,(
% 2.24/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.99    inference(flattening,[],[f21])).
% 2.24/0.99  
% 2.24/0.99  fof(f23,plain,(
% 2.24/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.99    inference(rectify,[],[f22])).
% 2.24/0.99  
% 2.24/0.99  fof(f24,plain,(
% 2.24/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.24/0.99    introduced(choice_axiom,[])).
% 2.24/0.99  
% 2.24/0.99  fof(f25,plain,(
% 2.24/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.24/0.99  
% 2.24/0.99  fof(f34,plain,(
% 2.24/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.24/0.99    inference(cnf_transformation,[],[f25])).
% 2.24/0.99  
% 2.24/0.99  fof(f59,plain,(
% 2.24/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) != X3) )),
% 2.24/0.99    inference(definition_unfolding,[],[f34,f50])).
% 2.24/0.99  
% 2.24/0.99  fof(f70,plain,(
% 2.24/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2))) != X3) )),
% 2.24/0.99    inference(equality_resolution,[],[f59])).
% 2.24/0.99  
% 2.24/0.99  fof(f71,plain,(
% 2.24/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_tarski(k2_tarski(k2_tarski(X5,X1),k2_tarski(X2,X2))))) )),
% 2.24/0.99    inference(equality_resolution,[],[f70])).
% 2.24/0.99  
% 2.24/0.99  fof(f14,conjecture,(
% 2.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/0.99  
% 2.24/0.99  fof(f15,negated_conjecture,(
% 2.24/0.99    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.24/0.99    inference(negated_conjecture,[],[f14])).
% 2.24/0.99  
% 2.24/0.99  fof(f19,plain,(
% 2.24/0.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 2.24/0.99    inference(ennf_transformation,[],[f15])).
% 2.24/0.99  
% 2.24/0.99  fof(f26,plain,(
% 2.24/0.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 2.24/0.99    introduced(choice_axiom,[])).
% 2.24/0.99  
% 2.24/0.99  fof(f27,plain,(
% 2.24/0.99    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 2.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f26])).
% 2.24/0.99  
% 2.24/0.99  fof(f49,plain,(
% 2.24/0.99    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 2.24/0.99    inference(cnf_transformation,[],[f27])).
% 2.24/0.99  
% 2.24/0.99  fof(f65,plain,(
% 2.24/0.99    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 2.24/0.99    inference(definition_unfolding,[],[f49,f29])).
% 2.24/0.99  
% 2.24/0.99  cnf(c_13,plain,
% 2.24/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) = k2_enumset1(X0,X0,X1,X2) ),
% 2.24/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_16,plain,
% 2.24/0.99      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 2.24/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_15,plain,
% 2.24/0.99      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1)))
% 2.24/0.99      | k1_xboole_0 = X1
% 2.24/0.99      | k1_xboole_0 = X0 ),
% 2.24/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1676,plain,
% 2.24/0.99      ( k2_tarski(X0,X0) = k1_xboole_0
% 2.24/0.99      | k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
% 2.24/0.99      | k1_xboole_0 = X1 ),
% 2.24/0.99      inference(superposition,[status(thm)],[c_16,c_15]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1,plain,
% 2.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.24/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2,plain,
% 2.24/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.24/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_4,plain,
% 2.24/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.24/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_104,plain,
% 2.24/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.24/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_185,plain,
% 2.24/0.99      ( X0 != X1 | k4_xboole_0(X0,X2) = X0 | k1_xboole_0 != X2 ),
% 2.24/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_104]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_186,plain,
% 2.24/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.24/0.99      inference(unflattening,[status(thm)],[c_185]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1041,plain,
% 2.24/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.24/0.99      inference(light_normalisation,[status(thm)],[c_1,c_186]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_3,plain,
% 2.24/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.24/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_102,plain,
% 2.24/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.24/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_14,plain,
% 2.24/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_tarski(X0,X0),X1) ),
% 2.24/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_200,plain,
% 2.24/0.99      ( ~ r2_hidden(X0,X1)
% 2.24/0.99      | X1 != X2
% 2.24/0.99      | k4_xboole_0(X3,X2) != X3
% 2.24/0.99      | k2_tarski(X0,X0) != X3 ),
% 2.24/0.99      inference(resolution_lifted,[status(thm)],[c_102,c_14]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_201,plain,
% 2.24/0.99      ( ~ r2_hidden(X0,X1)
% 2.24/0.99      | k4_xboole_0(k2_tarski(X0,X0),X1) != k2_tarski(X0,X0) ),
% 2.24/0.99      inference(unflattening,[status(thm)],[c_200]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1025,plain,
% 2.24/0.99      ( k4_xboole_0(k2_tarski(X0,X0),X1) != k2_tarski(X0,X0)
% 2.24/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.24/0.99      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1523,plain,
% 2.24/0.99      ( k2_tarski(X0,X0) != k1_xboole_0
% 2.24/0.99      | r2_hidden(X0,k2_tarski(X0,X0)) != iProver_top ),
% 2.24/0.99      inference(superposition,[status(thm)],[c_1041,c_1025]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_0,plain,
% 2.24/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 2.24/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_11,plain,
% 2.24/0.99      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) ),
% 2.24/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1028,plain,
% 2.24/0.99      ( r2_hidden(X0,k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) = iProver_top ),
% 2.24/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1352,plain,
% 2.24/0.99      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 2.24/0.99      inference(superposition,[status(thm)],[c_0,c_1028]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2296,plain,
% 2.24/0.99      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 2.24/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1523,c_1352]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2903,plain,
% 2.24/0.99      ( k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
% 2.24/0.99      | k1_xboole_0 = X1 ),
% 2.24/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1676,c_2296]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2908,plain,
% 2.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
% 2.24/0.99      | k2_tarski(X1,X1) = k1_xboole_0 ),
% 2.24/0.99      inference(superposition,[status(thm)],[c_13,c_2903]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_1532,plain,
% 2.24/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 2.24/0.99      inference(superposition,[status(thm)],[c_0,c_13]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2930,plain,
% 2.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1)))) = k1_setfam_1(k2_tarski(X0,X1))
% 2.24/0.99      | k2_tarski(X1,X1) = k1_xboole_0 ),
% 2.24/0.99      inference(light_normalisation,[status(thm)],[c_2908,c_1532]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2931,plain,
% 2.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))
% 2.24/0.99      | k2_tarski(X1,X1) = k1_xboole_0 ),
% 2.24/0.99      inference(demodulation,[status(thm)],[c_2930,c_16]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2940,plain,
% 2.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 2.24/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2931,c_2296]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_17,negated_conjecture,
% 2.24/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 2.24/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2942,plain,
% 2.24/0.99      ( k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 2.24/0.99      inference(demodulation,[status(thm)],[c_2940,c_17]) ).
% 2.24/0.99  
% 2.24/0.99  cnf(c_2948,plain,
% 2.24/0.99      ( $false ),
% 2.24/0.99      inference(equality_resolution_simp,[status(thm)],[c_2942]) ).
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.24/0.99  
% 2.24/0.99  ------                               Statistics
% 2.24/0.99  
% 2.24/0.99  ------ General
% 2.24/0.99  
% 2.24/0.99  abstr_ref_over_cycles:                  0
% 2.24/0.99  abstr_ref_under_cycles:                 0
% 2.24/0.99  gc_basic_clause_elim:                   0
% 2.24/0.99  forced_gc_time:                         0
% 2.24/0.99  parsing_time:                           0.01
% 2.24/0.99  unif_index_cands_time:                  0.
% 2.24/0.99  unif_index_add_time:                    0.
% 2.24/0.99  orderings_time:                         0.
% 2.24/0.99  out_proof_time:                         0.008
% 2.24/0.99  total_time:                             0.139
% 2.24/0.99  num_of_symbols:                         42
% 2.24/0.99  num_of_terms:                           4737
% 2.24/0.99  
% 2.24/0.99  ------ Preprocessing
% 2.24/0.99  
% 2.24/0.99  num_of_splits:                          0
% 2.24/0.99  num_of_split_atoms:                     0
% 2.24/0.99  num_of_reused_defs:                     0
% 2.24/0.99  num_eq_ax_congr_red:                    24
% 2.24/0.99  num_of_sem_filtered_clauses:            1
% 2.24/0.99  num_of_subtypes:                        0
% 2.24/0.99  monotx_restored_types:                  0
% 2.24/0.99  sat_num_of_epr_types:                   0
% 2.24/0.99  sat_num_of_non_cyclic_types:            0
% 2.24/0.99  sat_guarded_non_collapsed_types:        0
% 2.24/0.99  num_pure_diseq_elim:                    0
% 2.24/0.99  simp_replaced_by:                       0
% 2.24/0.99  res_preprocessed:                       84
% 2.24/0.99  prep_upred:                             0
% 2.24/0.99  prep_unflattend:                        60
% 2.24/0.99  smt_new_axioms:                         0
% 2.24/0.99  pred_elim_cands:                        1
% 2.24/0.99  pred_elim:                              1
% 2.24/0.99  pred_elim_cl:                           1
% 2.24/0.99  pred_elim_cycles:                       3
% 2.24/0.99  merged_defs:                            2
% 2.24/0.99  merged_defs_ncl:                        0
% 2.24/0.99  bin_hyper_res:                          2
% 2.24/0.99  prep_cycles:                            4
% 2.24/0.99  pred_elim_time:                         0.009
% 2.24/0.99  splitting_time:                         0.
% 2.24/0.99  sem_filter_time:                        0.
% 2.24/0.99  monotx_time:                            0.
% 2.24/0.99  subtype_inf_time:                       0.
% 2.24/0.99  
% 2.24/0.99  ------ Problem properties
% 2.24/0.99  
% 2.24/0.99  clauses:                                17
% 2.24/0.99  conjectures:                            1
% 2.24/0.99  epr:                                    1
% 2.24/0.99  horn:                                   14
% 2.24/0.99  ground:                                 1
% 2.24/0.99  unary:                                  10
% 2.24/0.99  binary:                                 1
% 2.24/0.99  lits:                                   33
% 2.24/0.99  lits_eq:                                23
% 2.24/0.99  fd_pure:                                0
% 2.24/0.99  fd_pseudo:                              0
% 2.24/0.99  fd_cond:                                1
% 2.24/0.99  fd_pseudo_cond:                         4
% 2.24/0.99  ac_symbols:                             0
% 2.24/0.99  
% 2.24/0.99  ------ Propositional Solver
% 2.24/0.99  
% 2.24/0.99  prop_solver_calls:                      26
% 2.24/0.99  prop_fast_solver_calls:                 518
% 2.24/0.99  smt_solver_calls:                       0
% 2.24/0.99  smt_fast_solver_calls:                  0
% 2.24/0.99  prop_num_of_clauses:                    946
% 2.24/0.99  prop_preprocess_simplified:             3820
% 2.24/0.99  prop_fo_subsumed:                       2
% 2.24/0.99  prop_solver_time:                       0.
% 2.24/0.99  smt_solver_time:                        0.
% 2.24/0.99  smt_fast_solver_time:                   0.
% 2.24/0.99  prop_fast_solver_time:                  0.
% 2.24/0.99  prop_unsat_core_time:                   0.
% 2.24/0.99  
% 2.24/0.99  ------ QBF
% 2.24/0.99  
% 2.24/0.99  qbf_q_res:                              0
% 2.24/0.99  qbf_num_tautologies:                    0
% 2.24/0.99  qbf_prep_cycles:                        0
% 2.24/0.99  
% 2.24/0.99  ------ BMC1
% 2.24/0.99  
% 2.24/0.99  bmc1_current_bound:                     -1
% 2.24/0.99  bmc1_last_solved_bound:                 -1
% 2.24/0.99  bmc1_unsat_core_size:                   -1
% 2.24/0.99  bmc1_unsat_core_parents_size:           -1
% 2.24/0.99  bmc1_merge_next_fun:                    0
% 2.24/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.24/0.99  
% 2.24/0.99  ------ Instantiation
% 2.24/0.99  
% 2.24/0.99  inst_num_of_clauses:                    333
% 2.24/0.99  inst_num_in_passive:                    96
% 2.24/0.99  inst_num_in_active:                     126
% 2.24/0.99  inst_num_in_unprocessed:                111
% 2.24/0.99  inst_num_of_loops:                      130
% 2.24/0.99  inst_num_of_learning_restarts:          0
% 2.24/0.99  inst_num_moves_active_passive:          3
% 2.24/0.99  inst_lit_activity:                      0
% 2.24/0.99  inst_lit_activity_moves:                0
% 2.24/0.99  inst_num_tautologies:                   0
% 2.24/0.99  inst_num_prop_implied:                  0
% 2.24/0.99  inst_num_existing_simplified:           0
% 2.24/0.99  inst_num_eq_res_simplified:             0
% 2.24/0.99  inst_num_child_elim:                    0
% 2.24/0.99  inst_num_of_dismatching_blockings:      170
% 2.24/0.99  inst_num_of_non_proper_insts:           340
% 2.24/0.99  inst_num_of_duplicates:                 0
% 2.24/0.99  inst_inst_num_from_inst_to_res:         0
% 2.24/0.99  inst_dismatching_checking_time:         0.
% 2.24/0.99  
% 2.24/0.99  ------ Resolution
% 2.24/0.99  
% 2.24/0.99  res_num_of_clauses:                     0
% 2.24/0.99  res_num_in_passive:                     0
% 2.24/0.99  res_num_in_active:                      0
% 2.24/0.99  res_num_of_loops:                       88
% 2.24/0.99  res_forward_subset_subsumed:            59
% 2.24/0.99  res_backward_subset_subsumed:           0
% 2.24/0.99  res_forward_subsumed:                   0
% 2.24/0.99  res_backward_subsumed:                  0
% 2.24/0.99  res_forward_subsumption_resolution:     0
% 2.24/0.99  res_backward_subsumption_resolution:    1
% 2.24/0.99  res_clause_to_clause_subsumption:       189
% 2.24/0.99  res_orphan_elimination:                 0
% 2.24/0.99  res_tautology_del:                      25
% 2.24/0.99  res_num_eq_res_simplified:              0
% 2.24/0.99  res_num_sel_changes:                    0
% 2.24/0.99  res_moves_from_active_to_pass:          0
% 2.24/0.99  
% 2.24/0.99  ------ Superposition
% 2.24/0.99  
% 2.24/0.99  sup_time_total:                         0.
% 2.24/0.99  sup_time_generating:                    0.
% 2.24/0.99  sup_time_sim_full:                      0.
% 2.24/0.99  sup_time_sim_immed:                     0.
% 2.24/0.99  
% 2.24/0.99  sup_num_of_clauses:                     31
% 2.24/0.99  sup_num_in_active:                      23
% 2.24/0.99  sup_num_in_passive:                     8
% 2.24/0.99  sup_num_of_loops:                       25
% 2.24/0.99  sup_fw_superposition:                   33
% 2.24/0.99  sup_bw_superposition:                   6
% 2.24/0.99  sup_immediate_simplified:               3
% 2.24/0.99  sup_given_eliminated:                   0
% 2.24/0.99  comparisons_done:                       0
% 2.24/0.99  comparisons_avoided:                    6
% 2.24/0.99  
% 2.24/0.99  ------ Simplifications
% 2.24/0.99  
% 2.24/0.99  
% 2.24/0.99  sim_fw_subset_subsumed:                 0
% 2.24/0.99  sim_bw_subset_subsumed:                 0
% 2.24/0.99  sim_fw_subsumed:                        0
% 2.24/0.99  sim_bw_subsumed:                        0
% 2.24/0.99  sim_fw_subsumption_res:                 2
% 2.24/0.99  sim_bw_subsumption_res:                 0
% 2.24/0.99  sim_tautology_del:                      0
% 2.24/0.99  sim_eq_tautology_del:                   6
% 2.24/0.99  sim_eq_res_simp:                        0
% 2.24/0.99  sim_fw_demodulated:                     3
% 2.24/0.99  sim_bw_demodulated:                     2
% 2.24/0.99  sim_light_normalised:                   2
% 2.24/0.99  sim_joinable_taut:                      0
% 2.24/0.99  sim_joinable_simp:                      0
% 2.24/0.99  sim_ac_normalised:                      0
% 2.24/0.99  sim_smt_subsumption:                    0
% 2.24/0.99  
%------------------------------------------------------------------------------
