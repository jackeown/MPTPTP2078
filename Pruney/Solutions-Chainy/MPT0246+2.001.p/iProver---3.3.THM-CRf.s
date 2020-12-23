%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:01 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 623 expanded)
%              Number of clauses        :   75 ( 187 expanded)
%              Number of leaves         :   17 ( 143 expanded)
%              Depth                    :   20
%              Number of atoms          :  304 (1788 expanded)
%              Number of equality atoms :  196 ( 765 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK2 = X2
          | ~ r2_hidden(X2,sK1) )
      & k1_xboole_0 != sK1
      & k1_tarski(sK2) != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ! [X2] :
        ( sK2 = X2
        | ~ r2_hidden(X2,sK1) )
    & k1_xboole_0 != sK1
    & k1_tarski(sK2) != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f44,plain,(
    ! [X2] :
      ( sK2 = X2
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f35,f34,f45,f45])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))) ),
    inference(definition_unfolding,[],[f39,f45,f46])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f36,f34,f45,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f42,plain,(
    k1_tarski(sK2) != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK1 ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_668,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | sK2 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_661,plain,
    ( sK2 = X0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1056,plain,
    ( sK0(sK1,X0) = sK2
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_661])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_665,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1212,plain,
    ( sK0(sK1,k4_xboole_0(X0,sK1)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1056,c_665])).

cnf(c_1310,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK2,sK1) = iProver_top
    | r1_tarski(sK1,k4_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_668])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_744,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(X0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_745,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k4_xboole_0(X0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1418,plain,
    ( r2_hidden(sK2,sK1) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1310,c_11,c_745])).

cnf(c_1419,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1418])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_663,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_667,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1207,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_667])).

cnf(c_1896,plain,
    ( sK0(X0,X1) = sK2
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_661])).

cnf(c_1933,plain,
    ( sK0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = sK2
    | r2_hidden(X0,sK1) != iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_1896])).

cnf(c_7,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_664,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_717,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X1,X1,X1,X1,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_664,c_0])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_662,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_941,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X1,X1,X1,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_662])).

cnf(c_1638,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X2,X2,X2,X2,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_667])).

cnf(c_2025,plain,
    ( sK0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = sK2
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_1638])).

cnf(c_2201,plain,
    ( sK0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),X0) = sK2
    | sK1 = k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_2025])).

cnf(c_2529,plain,
    ( sK0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),X0) = sK2
    | sK1 = k1_xboole_0
    | r2_hidden(sK2,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_667])).

cnf(c_12,negated_conjecture,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_380,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | k4_enumset1(X0,X2,X4,X6,X8,X10) = k4_enumset1(X1,X3,X5,X7,X9,X11) ),
    theory(equality)).

cnf(c_385,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_378,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_391,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_752,plain,
    ( ~ r1_tarski(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_753,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
    | r1_tarski(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_790,plain,
    ( ~ r2_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_791,plain,
    ( r2_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) != iProver_top
    | r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_926,plain,
    ( ~ r2_hidden(X0,sK1)
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_928,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_930,plain,
    ( r2_hidden(sK2,sK1) != iProver_top
    | r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_808,plain,
    ( ~ r1_tarski(X0,sK1)
    | r2_xboole_0(X0,sK1)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_927,plain,
    ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1)
    | r2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1)
    | sK1 = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_932,plain,
    ( sK1 = k4_enumset1(X0,X0,X0,X0,X0,X0)
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) != iProver_top
    | r2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_934,plain,
    ( sK1 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) != iProver_top
    | r2_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_943,plain,
    ( r2_hidden(sK2,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_379,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_757,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_2139,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(X0,X0,X0,X0,X0,X0)
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
    | sK1 != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_2142,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
    | sK1 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_1424,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_667])).

cnf(c_1500,plain,
    ( sK0(sK1,X0) = sK2
    | sK1 = k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1424])).

cnf(c_1895,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_667])).

cnf(c_2648,plain,
    ( sK0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1895])).

cnf(c_2923,plain,
    ( sK0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = sK2
    | sK0(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = sK2
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(sK0(sK1,X2),X1) = iProver_top
    | r1_tarski(sK1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_2648])).

cnf(c_3373,plain,
    ( sK0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),X0) = sK2
    | sK0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
    | sK0(sK1,sK1) = sK2
    | sK1 = k1_xboole_0
    | r2_hidden(sK0(sK1,X1),X0) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_2923])).

cnf(c_666,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1073,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = X1
    | r2_hidden(X0,X1) != iProver_top
    | r2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_666])).

cnf(c_1213,plain,
    ( sK0(sK1,X0) = sK2
    | sK1 = X0
    | r2_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_666])).

cnf(c_670,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1334,plain,
    ( sK0(sK1,X0) = sK2
    | sK1 = X0
    | r2_xboole_0(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_670])).

cnf(c_2753,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = sK1
    | sK0(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = sK2
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1334])).

cnf(c_2770,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
    | sK0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_3634,plain,
    ( sK0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_12,c_11,c_745,c_1310,c_2770])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_669,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3640,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK2,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3634,c_669])).

cnf(c_4257,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2529,c_12,c_385,c_391,c_753,c_791,c_930,c_934,c_943,c_1419,c_2142,c_3640])).

cnf(c_4286,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4257,c_11])).

cnf(c_4287,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4286])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.00/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.00/1.05  
% 1.00/1.05  ------  iProver source info
% 1.00/1.05  
% 1.00/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.00/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.00/1.05  git: non_committed_changes: false
% 1.00/1.05  git: last_make_outside_of_git: false
% 1.00/1.05  
% 1.00/1.05  ------ 
% 1.00/1.05  
% 1.00/1.05  ------ Input Options
% 1.00/1.05  
% 1.00/1.05  --out_options                           all
% 1.00/1.05  --tptp_safe_out                         true
% 1.00/1.05  --problem_path                          ""
% 1.00/1.05  --include_path                          ""
% 1.00/1.05  --clausifier                            res/vclausify_rel
% 1.00/1.05  --clausifier_options                    --mode clausify
% 1.00/1.05  --stdin                                 false
% 1.00/1.05  --stats_out                             all
% 1.00/1.05  
% 1.00/1.05  ------ General Options
% 1.00/1.05  
% 1.00/1.05  --fof                                   false
% 1.00/1.05  --time_out_real                         305.
% 1.00/1.05  --time_out_virtual                      -1.
% 1.00/1.05  --symbol_type_check                     false
% 1.00/1.05  --clausify_out                          false
% 1.00/1.05  --sig_cnt_out                           false
% 1.00/1.05  --trig_cnt_out                          false
% 1.00/1.05  --trig_cnt_out_tolerance                1.
% 1.00/1.05  --trig_cnt_out_sk_spl                   false
% 1.00/1.05  --abstr_cl_out                          false
% 1.00/1.05  
% 1.00/1.05  ------ Global Options
% 1.00/1.05  
% 1.00/1.05  --schedule                              default
% 1.00/1.05  --add_important_lit                     false
% 1.00/1.05  --prop_solver_per_cl                    1000
% 1.00/1.05  --min_unsat_core                        false
% 1.00/1.05  --soft_assumptions                      false
% 1.00/1.05  --soft_lemma_size                       3
% 1.00/1.05  --prop_impl_unit_size                   0
% 1.00/1.05  --prop_impl_unit                        []
% 1.00/1.05  --share_sel_clauses                     true
% 1.00/1.05  --reset_solvers                         false
% 1.00/1.05  --bc_imp_inh                            [conj_cone]
% 1.00/1.05  --conj_cone_tolerance                   3.
% 1.00/1.05  --extra_neg_conj                        none
% 1.00/1.05  --large_theory_mode                     true
% 1.00/1.05  --prolific_symb_bound                   200
% 1.00/1.05  --lt_threshold                          2000
% 1.00/1.05  --clause_weak_htbl                      true
% 1.00/1.05  --gc_record_bc_elim                     false
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing Options
% 1.00/1.05  
% 1.00/1.05  --preprocessing_flag                    true
% 1.00/1.05  --time_out_prep_mult                    0.1
% 1.00/1.05  --splitting_mode                        input
% 1.00/1.05  --splitting_grd                         true
% 1.00/1.05  --splitting_cvd                         false
% 1.00/1.05  --splitting_cvd_svl                     false
% 1.00/1.05  --splitting_nvd                         32
% 1.00/1.05  --sub_typing                            true
% 1.00/1.05  --prep_gs_sim                           true
% 1.00/1.05  --prep_unflatten                        true
% 1.00/1.05  --prep_res_sim                          true
% 1.00/1.05  --prep_upred                            true
% 1.00/1.05  --prep_sem_filter                       exhaustive
% 1.00/1.05  --prep_sem_filter_out                   false
% 1.00/1.05  --pred_elim                             true
% 1.00/1.05  --res_sim_input                         true
% 1.00/1.05  --eq_ax_congr_red                       true
% 1.00/1.05  --pure_diseq_elim                       true
% 1.00/1.05  --brand_transform                       false
% 1.00/1.05  --non_eq_to_eq                          false
% 1.00/1.05  --prep_def_merge                        true
% 1.00/1.05  --prep_def_merge_prop_impl              false
% 1.00/1.05  --prep_def_merge_mbd                    true
% 1.00/1.05  --prep_def_merge_tr_red                 false
% 1.00/1.05  --prep_def_merge_tr_cl                  false
% 1.00/1.05  --smt_preprocessing                     true
% 1.00/1.05  --smt_ac_axioms                         fast
% 1.00/1.05  --preprocessed_out                      false
% 1.00/1.05  --preprocessed_stats                    false
% 1.00/1.05  
% 1.00/1.05  ------ Abstraction refinement Options
% 1.00/1.05  
% 1.00/1.05  --abstr_ref                             []
% 1.00/1.05  --abstr_ref_prep                        false
% 1.00/1.05  --abstr_ref_until_sat                   false
% 1.00/1.05  --abstr_ref_sig_restrict                funpre
% 1.00/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.00/1.05  --abstr_ref_under                       []
% 1.00/1.05  
% 1.00/1.05  ------ SAT Options
% 1.00/1.05  
% 1.00/1.05  --sat_mode                              false
% 1.00/1.05  --sat_fm_restart_options                ""
% 1.00/1.05  --sat_gr_def                            false
% 1.00/1.05  --sat_epr_types                         true
% 1.00/1.05  --sat_non_cyclic_types                  false
% 1.00/1.05  --sat_finite_models                     false
% 1.00/1.05  --sat_fm_lemmas                         false
% 1.00/1.05  --sat_fm_prep                           false
% 1.00/1.05  --sat_fm_uc_incr                        true
% 1.00/1.05  --sat_out_model                         small
% 1.00/1.05  --sat_out_clauses                       false
% 1.00/1.05  
% 1.00/1.05  ------ QBF Options
% 1.00/1.05  
% 1.00/1.05  --qbf_mode                              false
% 1.00/1.05  --qbf_elim_univ                         false
% 1.00/1.05  --qbf_dom_inst                          none
% 1.00/1.05  --qbf_dom_pre_inst                      false
% 1.00/1.05  --qbf_sk_in                             false
% 1.00/1.05  --qbf_pred_elim                         true
% 1.00/1.05  --qbf_split                             512
% 1.00/1.05  
% 1.00/1.05  ------ BMC1 Options
% 1.00/1.05  
% 1.00/1.05  --bmc1_incremental                      false
% 1.00/1.05  --bmc1_axioms                           reachable_all
% 1.00/1.05  --bmc1_min_bound                        0
% 1.00/1.05  --bmc1_max_bound                        -1
% 1.00/1.05  --bmc1_max_bound_default                -1
% 1.00/1.05  --bmc1_symbol_reachability              true
% 1.00/1.05  --bmc1_property_lemmas                  false
% 1.00/1.05  --bmc1_k_induction                      false
% 1.00/1.05  --bmc1_non_equiv_states                 false
% 1.00/1.05  --bmc1_deadlock                         false
% 1.00/1.05  --bmc1_ucm                              false
% 1.00/1.05  --bmc1_add_unsat_core                   none
% 1.00/1.05  --bmc1_unsat_core_children              false
% 1.00/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.00/1.05  --bmc1_out_stat                         full
% 1.00/1.05  --bmc1_ground_init                      false
% 1.00/1.05  --bmc1_pre_inst_next_state              false
% 1.00/1.05  --bmc1_pre_inst_state                   false
% 1.00/1.05  --bmc1_pre_inst_reach_state             false
% 1.00/1.05  --bmc1_out_unsat_core                   false
% 1.00/1.05  --bmc1_aig_witness_out                  false
% 1.00/1.05  --bmc1_verbose                          false
% 1.00/1.05  --bmc1_dump_clauses_tptp                false
% 1.00/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.00/1.05  --bmc1_dump_file                        -
% 1.00/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.00/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.00/1.05  --bmc1_ucm_extend_mode                  1
% 1.00/1.05  --bmc1_ucm_init_mode                    2
% 1.00/1.05  --bmc1_ucm_cone_mode                    none
% 1.00/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.00/1.05  --bmc1_ucm_relax_model                  4
% 1.00/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.00/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.00/1.05  --bmc1_ucm_layered_model                none
% 1.00/1.05  --bmc1_ucm_max_lemma_size               10
% 1.00/1.05  
% 1.00/1.05  ------ AIG Options
% 1.00/1.05  
% 1.00/1.05  --aig_mode                              false
% 1.00/1.05  
% 1.00/1.05  ------ Instantiation Options
% 1.00/1.05  
% 1.00/1.05  --instantiation_flag                    true
% 1.00/1.05  --inst_sos_flag                         false
% 1.00/1.05  --inst_sos_phase                        true
% 1.00/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel_side                     num_symb
% 1.00/1.05  --inst_solver_per_active                1400
% 1.00/1.05  --inst_solver_calls_frac                1.
% 1.00/1.05  --inst_passive_queue_type               priority_queues
% 1.00/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.00/1.05  --inst_passive_queues_freq              [25;2]
% 1.00/1.05  --inst_dismatching                      true
% 1.00/1.05  --inst_eager_unprocessed_to_passive     true
% 1.00/1.05  --inst_prop_sim_given                   true
% 1.00/1.05  --inst_prop_sim_new                     false
% 1.00/1.05  --inst_subs_new                         false
% 1.00/1.05  --inst_eq_res_simp                      false
% 1.00/1.05  --inst_subs_given                       false
% 1.00/1.05  --inst_orphan_elimination               true
% 1.00/1.05  --inst_learning_loop_flag               true
% 1.00/1.05  --inst_learning_start                   3000
% 1.00/1.05  --inst_learning_factor                  2
% 1.00/1.05  --inst_start_prop_sim_after_learn       3
% 1.00/1.05  --inst_sel_renew                        solver
% 1.00/1.05  --inst_lit_activity_flag                true
% 1.00/1.05  --inst_restr_to_given                   false
% 1.00/1.05  --inst_activity_threshold               500
% 1.00/1.05  --inst_out_proof                        true
% 1.00/1.05  
% 1.00/1.05  ------ Resolution Options
% 1.00/1.05  
% 1.00/1.05  --resolution_flag                       true
% 1.00/1.05  --res_lit_sel                           adaptive
% 1.00/1.05  --res_lit_sel_side                      none
% 1.00/1.05  --res_ordering                          kbo
% 1.00/1.05  --res_to_prop_solver                    active
% 1.00/1.05  --res_prop_simpl_new                    false
% 1.00/1.05  --res_prop_simpl_given                  true
% 1.00/1.05  --res_passive_queue_type                priority_queues
% 1.00/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.00/1.05  --res_passive_queues_freq               [15;5]
% 1.00/1.05  --res_forward_subs                      full
% 1.00/1.05  --res_backward_subs                     full
% 1.00/1.05  --res_forward_subs_resolution           true
% 1.00/1.05  --res_backward_subs_resolution          true
% 1.00/1.05  --res_orphan_elimination                true
% 1.00/1.05  --res_time_limit                        2.
% 1.00/1.05  --res_out_proof                         true
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Options
% 1.00/1.05  
% 1.00/1.05  --superposition_flag                    true
% 1.00/1.05  --sup_passive_queue_type                priority_queues
% 1.00/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.00/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.00/1.05  --demod_completeness_check              fast
% 1.00/1.05  --demod_use_ground                      true
% 1.00/1.05  --sup_to_prop_solver                    passive
% 1.00/1.05  --sup_prop_simpl_new                    true
% 1.00/1.05  --sup_prop_simpl_given                  true
% 1.00/1.05  --sup_fun_splitting                     false
% 1.00/1.05  --sup_smt_interval                      50000
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Simplification Setup
% 1.00/1.05  
% 1.00/1.05  --sup_indices_passive                   []
% 1.00/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.00/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_full_bw                           [BwDemod]
% 1.00/1.05  --sup_immed_triv                        [TrivRules]
% 1.00/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.00/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_immed_bw_main                     []
% 1.00/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.00/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  
% 1.00/1.05  ------ Combination Options
% 1.00/1.05  
% 1.00/1.05  --comb_res_mult                         3
% 1.00/1.05  --comb_sup_mult                         2
% 1.00/1.05  --comb_inst_mult                        10
% 1.00/1.05  
% 1.00/1.05  ------ Debug Options
% 1.00/1.05  
% 1.00/1.05  --dbg_backtrace                         false
% 1.00/1.05  --dbg_dump_prop_clauses                 false
% 1.00/1.05  --dbg_dump_prop_clauses_file            -
% 1.00/1.05  --dbg_out_stat                          false
% 1.00/1.05  ------ Parsing...
% 1.00/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.00/1.05  ------ Proving...
% 1.00/1.05  ------ Problem Properties 
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  clauses                                 13
% 1.00/1.05  conjectures                             3
% 1.00/1.05  EPR                                     5
% 1.00/1.05  Horn                                    11
% 1.00/1.05  unary                                   4
% 1.00/1.05  binary                                  7
% 1.00/1.05  lits                                    24
% 1.00/1.05  lits eq                                 6
% 1.00/1.05  fd_pure                                 0
% 1.00/1.05  fd_pseudo                               0
% 1.00/1.05  fd_cond                                 2
% 1.00/1.05  fd_pseudo_cond                          1
% 1.00/1.05  AC symbols                              0
% 1.00/1.05  
% 1.00/1.05  ------ Schedule dynamic 5 is on 
% 1.00/1.05  
% 1.00/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  ------ 
% 1.00/1.05  Current options:
% 1.00/1.05  ------ 
% 1.00/1.05  
% 1.00/1.05  ------ Input Options
% 1.00/1.05  
% 1.00/1.05  --out_options                           all
% 1.00/1.05  --tptp_safe_out                         true
% 1.00/1.05  --problem_path                          ""
% 1.00/1.05  --include_path                          ""
% 1.00/1.05  --clausifier                            res/vclausify_rel
% 1.00/1.05  --clausifier_options                    --mode clausify
% 1.00/1.05  --stdin                                 false
% 1.00/1.05  --stats_out                             all
% 1.00/1.05  
% 1.00/1.05  ------ General Options
% 1.00/1.05  
% 1.00/1.05  --fof                                   false
% 1.00/1.05  --time_out_real                         305.
% 1.00/1.05  --time_out_virtual                      -1.
% 1.00/1.05  --symbol_type_check                     false
% 1.00/1.05  --clausify_out                          false
% 1.00/1.05  --sig_cnt_out                           false
% 1.00/1.05  --trig_cnt_out                          false
% 1.00/1.05  --trig_cnt_out_tolerance                1.
% 1.00/1.05  --trig_cnt_out_sk_spl                   false
% 1.00/1.05  --abstr_cl_out                          false
% 1.00/1.05  
% 1.00/1.05  ------ Global Options
% 1.00/1.05  
% 1.00/1.05  --schedule                              default
% 1.00/1.05  --add_important_lit                     false
% 1.00/1.05  --prop_solver_per_cl                    1000
% 1.00/1.05  --min_unsat_core                        false
% 1.00/1.05  --soft_assumptions                      false
% 1.00/1.05  --soft_lemma_size                       3
% 1.00/1.05  --prop_impl_unit_size                   0
% 1.00/1.05  --prop_impl_unit                        []
% 1.00/1.05  --share_sel_clauses                     true
% 1.00/1.05  --reset_solvers                         false
% 1.00/1.05  --bc_imp_inh                            [conj_cone]
% 1.00/1.05  --conj_cone_tolerance                   3.
% 1.00/1.05  --extra_neg_conj                        none
% 1.00/1.05  --large_theory_mode                     true
% 1.00/1.05  --prolific_symb_bound                   200
% 1.00/1.05  --lt_threshold                          2000
% 1.00/1.05  --clause_weak_htbl                      true
% 1.00/1.05  --gc_record_bc_elim                     false
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing Options
% 1.00/1.05  
% 1.00/1.05  --preprocessing_flag                    true
% 1.00/1.05  --time_out_prep_mult                    0.1
% 1.00/1.05  --splitting_mode                        input
% 1.00/1.05  --splitting_grd                         true
% 1.00/1.05  --splitting_cvd                         false
% 1.00/1.05  --splitting_cvd_svl                     false
% 1.00/1.05  --splitting_nvd                         32
% 1.00/1.05  --sub_typing                            true
% 1.00/1.05  --prep_gs_sim                           true
% 1.00/1.05  --prep_unflatten                        true
% 1.00/1.05  --prep_res_sim                          true
% 1.00/1.05  --prep_upred                            true
% 1.00/1.05  --prep_sem_filter                       exhaustive
% 1.00/1.05  --prep_sem_filter_out                   false
% 1.00/1.05  --pred_elim                             true
% 1.00/1.05  --res_sim_input                         true
% 1.00/1.05  --eq_ax_congr_red                       true
% 1.00/1.05  --pure_diseq_elim                       true
% 1.00/1.05  --brand_transform                       false
% 1.00/1.05  --non_eq_to_eq                          false
% 1.00/1.05  --prep_def_merge                        true
% 1.00/1.05  --prep_def_merge_prop_impl              false
% 1.00/1.05  --prep_def_merge_mbd                    true
% 1.00/1.05  --prep_def_merge_tr_red                 false
% 1.00/1.05  --prep_def_merge_tr_cl                  false
% 1.00/1.05  --smt_preprocessing                     true
% 1.00/1.05  --smt_ac_axioms                         fast
% 1.00/1.05  --preprocessed_out                      false
% 1.00/1.05  --preprocessed_stats                    false
% 1.00/1.05  
% 1.00/1.05  ------ Abstraction refinement Options
% 1.00/1.05  
% 1.00/1.05  --abstr_ref                             []
% 1.00/1.05  --abstr_ref_prep                        false
% 1.00/1.05  --abstr_ref_until_sat                   false
% 1.00/1.05  --abstr_ref_sig_restrict                funpre
% 1.00/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.00/1.05  --abstr_ref_under                       []
% 1.00/1.05  
% 1.00/1.05  ------ SAT Options
% 1.00/1.05  
% 1.00/1.05  --sat_mode                              false
% 1.00/1.05  --sat_fm_restart_options                ""
% 1.00/1.05  --sat_gr_def                            false
% 1.00/1.05  --sat_epr_types                         true
% 1.00/1.05  --sat_non_cyclic_types                  false
% 1.00/1.05  --sat_finite_models                     false
% 1.00/1.05  --sat_fm_lemmas                         false
% 1.00/1.05  --sat_fm_prep                           false
% 1.00/1.05  --sat_fm_uc_incr                        true
% 1.00/1.05  --sat_out_model                         small
% 1.00/1.05  --sat_out_clauses                       false
% 1.00/1.05  
% 1.00/1.05  ------ QBF Options
% 1.00/1.05  
% 1.00/1.05  --qbf_mode                              false
% 1.00/1.05  --qbf_elim_univ                         false
% 1.00/1.05  --qbf_dom_inst                          none
% 1.00/1.05  --qbf_dom_pre_inst                      false
% 1.00/1.05  --qbf_sk_in                             false
% 1.00/1.05  --qbf_pred_elim                         true
% 1.00/1.05  --qbf_split                             512
% 1.00/1.05  
% 1.00/1.05  ------ BMC1 Options
% 1.00/1.05  
% 1.00/1.05  --bmc1_incremental                      false
% 1.00/1.05  --bmc1_axioms                           reachable_all
% 1.00/1.05  --bmc1_min_bound                        0
% 1.00/1.05  --bmc1_max_bound                        -1
% 1.00/1.05  --bmc1_max_bound_default                -1
% 1.00/1.05  --bmc1_symbol_reachability              true
% 1.00/1.05  --bmc1_property_lemmas                  false
% 1.00/1.05  --bmc1_k_induction                      false
% 1.00/1.05  --bmc1_non_equiv_states                 false
% 1.00/1.05  --bmc1_deadlock                         false
% 1.00/1.05  --bmc1_ucm                              false
% 1.00/1.05  --bmc1_add_unsat_core                   none
% 1.00/1.05  --bmc1_unsat_core_children              false
% 1.00/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.00/1.05  --bmc1_out_stat                         full
% 1.00/1.05  --bmc1_ground_init                      false
% 1.00/1.05  --bmc1_pre_inst_next_state              false
% 1.00/1.05  --bmc1_pre_inst_state                   false
% 1.00/1.05  --bmc1_pre_inst_reach_state             false
% 1.00/1.05  --bmc1_out_unsat_core                   false
% 1.00/1.05  --bmc1_aig_witness_out                  false
% 1.00/1.05  --bmc1_verbose                          false
% 1.00/1.05  --bmc1_dump_clauses_tptp                false
% 1.00/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.00/1.05  --bmc1_dump_file                        -
% 1.00/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.00/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.00/1.05  --bmc1_ucm_extend_mode                  1
% 1.00/1.05  --bmc1_ucm_init_mode                    2
% 1.00/1.05  --bmc1_ucm_cone_mode                    none
% 1.00/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.00/1.05  --bmc1_ucm_relax_model                  4
% 1.00/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.00/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.00/1.05  --bmc1_ucm_layered_model                none
% 1.00/1.05  --bmc1_ucm_max_lemma_size               10
% 1.00/1.05  
% 1.00/1.05  ------ AIG Options
% 1.00/1.05  
% 1.00/1.05  --aig_mode                              false
% 1.00/1.05  
% 1.00/1.05  ------ Instantiation Options
% 1.00/1.05  
% 1.00/1.05  --instantiation_flag                    true
% 1.00/1.05  --inst_sos_flag                         false
% 1.00/1.05  --inst_sos_phase                        true
% 1.00/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel_side                     none
% 1.00/1.05  --inst_solver_per_active                1400
% 1.00/1.05  --inst_solver_calls_frac                1.
% 1.00/1.05  --inst_passive_queue_type               priority_queues
% 1.00/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.00/1.05  --inst_passive_queues_freq              [25;2]
% 1.00/1.05  --inst_dismatching                      true
% 1.00/1.05  --inst_eager_unprocessed_to_passive     true
% 1.00/1.05  --inst_prop_sim_given                   true
% 1.00/1.05  --inst_prop_sim_new                     false
% 1.00/1.05  --inst_subs_new                         false
% 1.00/1.05  --inst_eq_res_simp                      false
% 1.00/1.05  --inst_subs_given                       false
% 1.00/1.05  --inst_orphan_elimination               true
% 1.00/1.05  --inst_learning_loop_flag               true
% 1.00/1.05  --inst_learning_start                   3000
% 1.00/1.05  --inst_learning_factor                  2
% 1.00/1.05  --inst_start_prop_sim_after_learn       3
% 1.00/1.05  --inst_sel_renew                        solver
% 1.00/1.05  --inst_lit_activity_flag                true
% 1.00/1.05  --inst_restr_to_given                   false
% 1.00/1.05  --inst_activity_threshold               500
% 1.00/1.05  --inst_out_proof                        true
% 1.00/1.05  
% 1.00/1.05  ------ Resolution Options
% 1.00/1.05  
% 1.00/1.05  --resolution_flag                       false
% 1.00/1.05  --res_lit_sel                           adaptive
% 1.00/1.05  --res_lit_sel_side                      none
% 1.00/1.05  --res_ordering                          kbo
% 1.00/1.05  --res_to_prop_solver                    active
% 1.00/1.05  --res_prop_simpl_new                    false
% 1.00/1.05  --res_prop_simpl_given                  true
% 1.00/1.05  --res_passive_queue_type                priority_queues
% 1.00/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.00/1.05  --res_passive_queues_freq               [15;5]
% 1.00/1.05  --res_forward_subs                      full
% 1.00/1.05  --res_backward_subs                     full
% 1.00/1.05  --res_forward_subs_resolution           true
% 1.00/1.05  --res_backward_subs_resolution          true
% 1.00/1.05  --res_orphan_elimination                true
% 1.00/1.05  --res_time_limit                        2.
% 1.00/1.05  --res_out_proof                         true
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Options
% 1.00/1.05  
% 1.00/1.05  --superposition_flag                    true
% 1.00/1.05  --sup_passive_queue_type                priority_queues
% 1.00/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.00/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.00/1.05  --demod_completeness_check              fast
% 1.00/1.05  --demod_use_ground                      true
% 1.00/1.05  --sup_to_prop_solver                    passive
% 1.00/1.05  --sup_prop_simpl_new                    true
% 1.00/1.05  --sup_prop_simpl_given                  true
% 1.00/1.05  --sup_fun_splitting                     false
% 1.00/1.05  --sup_smt_interval                      50000
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Simplification Setup
% 1.00/1.05  
% 1.00/1.05  --sup_indices_passive                   []
% 1.00/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.00/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_full_bw                           [BwDemod]
% 1.00/1.05  --sup_immed_triv                        [TrivRules]
% 1.00/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.00/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_immed_bw_main                     []
% 1.00/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.00/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  
% 1.00/1.05  ------ Combination Options
% 1.00/1.05  
% 1.00/1.05  --comb_res_mult                         3
% 1.00/1.05  --comb_sup_mult                         2
% 1.00/1.05  --comb_inst_mult                        10
% 1.00/1.05  
% 1.00/1.05  ------ Debug Options
% 1.00/1.05  
% 1.00/1.05  --dbg_backtrace                         false
% 1.00/1.05  --dbg_dump_prop_clauses                 false
% 1.00/1.05  --dbg_dump_prop_clauses_file            -
% 1.00/1.05  --dbg_out_stat                          false
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  ------ Proving...
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  % SZS status Theorem for theBenchmark.p
% 1.00/1.05  
% 1.00/1.05   Resolution empty clause
% 1.00/1.05  
% 1.00/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  fof(f2,axiom,(
% 1.00/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f16,plain,(
% 1.00/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.00/1.05    inference(ennf_transformation,[],[f2])).
% 1.00/1.05  
% 1.00/1.05  fof(f21,plain,(
% 1.00/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.00/1.05    inference(nnf_transformation,[],[f16])).
% 1.00/1.05  
% 1.00/1.05  fof(f22,plain,(
% 1.00/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.00/1.05    inference(rectify,[],[f21])).
% 1.00/1.05  
% 1.00/1.05  fof(f23,plain,(
% 1.00/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.00/1.05    introduced(choice_axiom,[])).
% 1.00/1.05  
% 1.00/1.05  fof(f24,plain,(
% 1.00/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.00/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 1.00/1.05  
% 1.00/1.05  fof(f30,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f24])).
% 1.00/1.05  
% 1.00/1.05  fof(f12,conjecture,(
% 1.00/1.05    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f13,negated_conjecture,(
% 1.00/1.05    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.00/1.05    inference(negated_conjecture,[],[f12])).
% 1.00/1.05  
% 1.00/1.05  fof(f20,plain,(
% 1.00/1.05    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.00/1.05    inference(ennf_transformation,[],[f13])).
% 1.00/1.05  
% 1.00/1.05  fof(f26,plain,(
% 1.00/1.05    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK2 = X2 | ~r2_hidden(X2,sK1)) & k1_xboole_0 != sK1 & k1_tarski(sK2) != sK1)),
% 1.00/1.05    introduced(choice_axiom,[])).
% 1.00/1.05  
% 1.00/1.05  fof(f27,plain,(
% 1.00/1.05    ! [X2] : (sK2 = X2 | ~r2_hidden(X2,sK1)) & k1_xboole_0 != sK1 & k1_tarski(sK2) != sK1),
% 1.00/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 1.00/1.05  
% 1.00/1.05  fof(f44,plain,(
% 1.00/1.05    ( ! [X2] : (sK2 = X2 | ~r2_hidden(X2,sK1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f27])).
% 1.00/1.05  
% 1.00/1.05  fof(f4,axiom,(
% 1.00/1.05    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f19,plain,(
% 1.00/1.05    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.00/1.05    inference(ennf_transformation,[],[f4])).
% 1.00/1.05  
% 1.00/1.05  fof(f33,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f19])).
% 1.00/1.05  
% 1.00/1.05  fof(f43,plain,(
% 1.00/1.05    k1_xboole_0 != sK1),
% 1.00/1.05    inference(cnf_transformation,[],[f27])).
% 1.00/1.05  
% 1.00/1.05  fof(f11,axiom,(
% 1.00/1.05    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f25,plain,(
% 1.00/1.05    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.00/1.05    inference(nnf_transformation,[],[f11])).
% 1.00/1.05  
% 1.00/1.05  fof(f41,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f25])).
% 1.00/1.05  
% 1.00/1.05  fof(f9,axiom,(
% 1.00/1.05    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f38,plain,(
% 1.00/1.05    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f9])).
% 1.00/1.05  
% 1.00/1.05  fof(f8,axiom,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f37,plain,(
% 1.00/1.05    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f8])).
% 1.00/1.05  
% 1.00/1.05  fof(f45,plain,(
% 1.00/1.05    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f38,f37])).
% 1.00/1.05  
% 1.00/1.05  fof(f49,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f41,f45])).
% 1.00/1.05  
% 1.00/1.05  fof(f29,plain,(
% 1.00/1.05    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f24])).
% 1.00/1.05  
% 1.00/1.05  fof(f10,axiom,(
% 1.00/1.05    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f39,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f10])).
% 1.00/1.05  
% 1.00/1.05  fof(f6,axiom,(
% 1.00/1.05    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f35,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f6])).
% 1.00/1.05  
% 1.00/1.05  fof(f5,axiom,(
% 1.00/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f34,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f5])).
% 1.00/1.05  
% 1.00/1.05  fof(f46,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k2_tarski(X0,X1)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f35,f34,f45,f45])).
% 1.00/1.05  
% 1.00/1.05  fof(f48,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))))) )),
% 1.00/1.05    inference(definition_unfolding,[],[f39,f45,f46])).
% 1.00/1.05  
% 1.00/1.05  fof(f7,axiom,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f36,plain,(
% 1.00/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f7])).
% 1.00/1.05  
% 1.00/1.05  fof(f47,plain,(
% 1.00/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f36,f34,f45,f37])).
% 1.00/1.05  
% 1.00/1.05  fof(f40,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f25])).
% 1.00/1.05  
% 1.00/1.05  fof(f50,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f40,f45])).
% 1.00/1.05  
% 1.00/1.05  fof(f42,plain,(
% 1.00/1.05    k1_tarski(sK2) != sK1),
% 1.00/1.05    inference(cnf_transformation,[],[f27])).
% 1.00/1.05  
% 1.00/1.05  fof(f51,plain,(
% 1.00/1.05    k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK1),
% 1.00/1.05    inference(definition_unfolding,[],[f42,f45])).
% 1.00/1.05  
% 1.00/1.05  fof(f3,axiom,(
% 1.00/1.05    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f14,plain,(
% 1.00/1.05    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.00/1.05    inference(unused_predicate_definition_removal,[],[f3])).
% 1.00/1.05  
% 1.00/1.05  fof(f17,plain,(
% 1.00/1.05    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.00/1.05    inference(ennf_transformation,[],[f14])).
% 1.00/1.05  
% 1.00/1.05  fof(f18,plain,(
% 1.00/1.05    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.00/1.05    inference(flattening,[],[f17])).
% 1.00/1.05  
% 1.00/1.05  fof(f32,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f18])).
% 1.00/1.05  
% 1.00/1.05  fof(f1,axiom,(
% 1.00/1.05    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 1.00/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f15,plain,(
% 1.00/1.05    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 1.00/1.05    inference(ennf_transformation,[],[f1])).
% 1.00/1.05  
% 1.00/1.05  fof(f28,plain,(
% 1.00/1.05    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f15])).
% 1.00/1.05  
% 1.00/1.05  fof(f31,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f24])).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3,plain,
% 1.00/1.05      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.00/1.05      inference(cnf_transformation,[],[f30]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_668,plain,
% 1.00/1.05      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.00/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_10,negated_conjecture,
% 1.00/1.05      ( ~ r2_hidden(X0,sK1) | sK2 = X0 ),
% 1.00/1.05      inference(cnf_transformation,[],[f44]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_661,plain,
% 1.00/1.05      ( sK2 = X0 | r2_hidden(X0,sK1) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1056,plain,
% 1.00/1.05      ( sK0(sK1,X0) = sK2 | r1_tarski(sK1,X0) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_668,c_661]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_6,plain,
% 1.00/1.05      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 1.00/1.05      inference(cnf_transformation,[],[f33]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_665,plain,
% 1.00/1.05      ( k1_xboole_0 = X0 | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1212,plain,
% 1.00/1.05      ( sK0(sK1,k4_xboole_0(X0,sK1)) = sK2 | sK1 = k1_xboole_0 ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1056,c_665]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1310,plain,
% 1.00/1.05      ( sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK2,sK1) = iProver_top
% 1.00/1.05      | r1_tarski(sK1,k4_xboole_0(X0,sK1)) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1212,c_668]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_11,negated_conjecture,
% 1.00/1.05      ( k1_xboole_0 != sK1 ),
% 1.00/1.05      inference(cnf_transformation,[],[f43]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_744,plain,
% 1.00/1.05      ( ~ r1_tarski(sK1,k4_xboole_0(X0,sK1)) | k1_xboole_0 = sK1 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_745,plain,
% 1.00/1.05      ( k1_xboole_0 = sK1 | r1_tarski(sK1,k4_xboole_0(X0,sK1)) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1418,plain,
% 1.00/1.05      ( r2_hidden(sK2,sK1) = iProver_top | sK1 = k1_xboole_0 ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_1310,c_11,c_745]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1419,plain,
% 1.00/1.05      ( sK1 = k1_xboole_0 | r2_hidden(sK2,sK1) = iProver_top ),
% 1.00/1.05      inference(renaming,[status(thm)],[c_1418]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_8,plain,
% 1.00/1.05      ( ~ r2_hidden(X0,X1) | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
% 1.00/1.05      inference(cnf_transformation,[],[f49]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_663,plain,
% 1.00/1.05      ( r2_hidden(X0,X1) != iProver_top
% 1.00/1.05      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4,plain,
% 1.00/1.05      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.00/1.05      inference(cnf_transformation,[],[f29]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_667,plain,
% 1.00/1.05      ( r2_hidden(X0,X1) != iProver_top
% 1.00/1.05      | r2_hidden(X0,X2) = iProver_top
% 1.00/1.05      | r1_tarski(X1,X2) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1207,plain,
% 1.00/1.05      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 1.00/1.05      | r1_tarski(X0,X2) != iProver_top
% 1.00/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_668,c_667]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1896,plain,
% 1.00/1.05      ( sK0(X0,X1) = sK2
% 1.00/1.05      | r1_tarski(X0,X1) = iProver_top
% 1.00/1.05      | r1_tarski(X0,sK1) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1207,c_661]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1933,plain,
% 1.00/1.05      ( sK0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = sK2
% 1.00/1.05      | r2_hidden(X0,sK1) != iProver_top
% 1.00/1.05      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_663,c_1896]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_7,plain,
% 1.00/1.05      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))) ),
% 1.00/1.05      inference(cnf_transformation,[],[f48]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_664,plain,
% 1.00/1.05      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_0,plain,
% 1.00/1.05      ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 1.00/1.05      inference(cnf_transformation,[],[f47]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_717,plain,
% 1.00/1.05      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X1,X1,X1,X1,X1)) = iProver_top ),
% 1.00/1.05      inference(demodulation,[status(thm)],[c_664,c_0]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_9,plain,
% 1.00/1.05      ( r2_hidden(X0,X1) | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
% 1.00/1.05      inference(cnf_transformation,[],[f50]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_662,plain,
% 1.00/1.05      ( r2_hidden(X0,X1) = iProver_top
% 1.00/1.05      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_941,plain,
% 1.00/1.05      ( r2_hidden(X0,k4_enumset1(X0,X1,X1,X1,X1,X1)) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_717,c_662]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1638,plain,
% 1.00/1.05      ( r2_hidden(X0,X1) = iProver_top
% 1.00/1.05      | r1_tarski(k4_enumset1(X0,X2,X2,X2,X2,X2),X1) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_941,c_667]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2025,plain,
% 1.00/1.05      ( sK0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = sK2
% 1.00/1.05      | r2_hidden(X0,X1) = iProver_top
% 1.00/1.05      | r2_hidden(X0,sK1) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1933,c_1638]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2201,plain,
% 1.00/1.05      ( sK0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),X0) = sK2
% 1.00/1.05      | sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK2,X0) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1419,c_2025]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2529,plain,
% 1.00/1.05      ( sK0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),X0) = sK2
% 1.00/1.05      | sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK2,X1) = iProver_top
% 1.00/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_2201,c_667]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_12,negated_conjecture,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK1 ),
% 1.00/1.05      inference(cnf_transformation,[],[f51]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_380,plain,
% 1.00/1.05      ( X0 != X1
% 1.00/1.05      | X2 != X3
% 1.00/1.05      | X4 != X5
% 1.00/1.05      | X6 != X7
% 1.00/1.05      | X8 != X9
% 1.00/1.05      | X10 != X11
% 1.00/1.05      | k4_enumset1(X0,X2,X4,X6,X8,X10) = k4_enumset1(X1,X3,X5,X7,X9,X11) ),
% 1.00/1.05      theory(equality) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_385,plain,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 1.00/1.05      | sK2 != sK2 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_380]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_378,plain,( X0 = X0 ),theory(equality) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_391,plain,
% 1.00/1.05      ( sK2 = sK2 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_378]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_5,plain,
% 1.00/1.05      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 1.00/1.05      inference(cnf_transformation,[],[f32]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_752,plain,
% 1.00/1.05      ( ~ r1_tarski(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 1.00/1.05      | r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 1.00/1.05      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_5]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_753,plain,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
% 1.00/1.05      | r1_tarski(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 1.00/1.05      | r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1,plain,
% 1.00/1.05      ( ~ r2_xboole_0(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 1.00/1.05      inference(cnf_transformation,[],[f28]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_790,plain,
% 1.00/1.05      ( ~ r2_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1)
% 1.00/1.05      | ~ r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_791,plain,
% 1.00/1.05      ( r2_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) != iProver_top
% 1.00/1.05      | r2_xboole_0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_926,plain,
% 1.00/1.05      ( ~ r2_hidden(X0,sK1) | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_928,plain,
% 1.00/1.05      ( r2_hidden(X0,sK1) != iProver_top
% 1.00/1.05      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_930,plain,
% 1.00/1.05      ( r2_hidden(sK2,sK1) != iProver_top
% 1.00/1.05      | r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) = iProver_top ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_928]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_808,plain,
% 1.00/1.05      ( ~ r1_tarski(X0,sK1) | r2_xboole_0(X0,sK1) | sK1 = X0 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_5]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_927,plain,
% 1.00/1.05      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1)
% 1.00/1.05      | r2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1)
% 1.00/1.05      | sK1 = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_808]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_932,plain,
% 1.00/1.05      ( sK1 = k4_enumset1(X0,X0,X0,X0,X0,X0)
% 1.00/1.05      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) != iProver_top
% 1.00/1.05      | r2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),sK1) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_934,plain,
% 1.00/1.05      ( sK1 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 1.00/1.05      | r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) != iProver_top
% 1.00/1.05      | r2_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) = iProver_top ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_932]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_943,plain,
% 1.00/1.05      ( r2_hidden(sK2,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_941]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_379,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_757,plain,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 1.00/1.05      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
% 1.00/1.05      | sK1 != X0 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_379]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2139,plain,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(X0,X0,X0,X0,X0,X0)
% 1.00/1.05      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
% 1.00/1.05      | sK1 != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_757]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2142,plain,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 1.00/1.05      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
% 1.00/1.05      | sK1 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_2139]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1424,plain,
% 1.00/1.05      ( sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK2,X0) = iProver_top
% 1.00/1.05      | r1_tarski(sK1,X0) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1419,c_667]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1500,plain,
% 1.00/1.05      ( sK0(sK1,X0) = sK2
% 1.00/1.05      | sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK2,X0) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1056,c_1424]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1895,plain,
% 1.00/1.05      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 1.00/1.05      | r1_tarski(X0,X3) != iProver_top
% 1.00/1.05      | r1_tarski(X3,X2) != iProver_top
% 1.00/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1207,c_667]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2648,plain,
% 1.00/1.05      ( sK0(sK1,X0) = sK2
% 1.00/1.05      | r2_hidden(sK0(sK1,X1),X2) = iProver_top
% 1.00/1.05      | r1_tarski(X0,X2) != iProver_top
% 1.00/1.05      | r1_tarski(sK1,X1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1056,c_1895]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2923,plain,
% 1.00/1.05      ( sK0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = sK2
% 1.00/1.05      | sK0(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = sK2
% 1.00/1.05      | r2_hidden(X0,sK1) != iProver_top
% 1.00/1.05      | r2_hidden(sK0(sK1,X2),X1) = iProver_top
% 1.00/1.05      | r1_tarski(sK1,X2) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1933,c_2648]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3373,plain,
% 1.00/1.05      ( sK0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),X0) = sK2
% 1.00/1.05      | sK0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
% 1.00/1.05      | sK0(sK1,sK1) = sK2
% 1.00/1.05      | sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK0(sK1,X1),X0) = iProver_top
% 1.00/1.05      | r1_tarski(sK1,X1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1500,c_2923]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_666,plain,
% 1.00/1.05      ( X0 = X1
% 1.00/1.05      | r1_tarski(X1,X0) != iProver_top
% 1.00/1.05      | r2_xboole_0(X1,X0) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1073,plain,
% 1.00/1.05      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = X1
% 1.00/1.05      | r2_hidden(X0,X1) != iProver_top
% 1.00/1.05      | r2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_663,c_666]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1213,plain,
% 1.00/1.05      ( sK0(sK1,X0) = sK2 | sK1 = X0 | r2_xboole_0(sK1,X0) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1056,c_666]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_670,plain,
% 1.00/1.05      ( r2_xboole_0(X0,X1) != iProver_top | r2_xboole_0(X1,X0) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1334,plain,
% 1.00/1.05      ( sK0(sK1,X0) = sK2 | sK1 = X0 | r2_xboole_0(X0,sK1) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1213,c_670]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2753,plain,
% 1.00/1.05      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = sK1
% 1.00/1.05      | sK0(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = sK2
% 1.00/1.05      | r2_hidden(X0,sK1) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1073,c_1334]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2770,plain,
% 1.00/1.05      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK1
% 1.00/1.05      | sK0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
% 1.00/1.05      | r2_hidden(sK2,sK1) != iProver_top ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_2753]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3634,plain,
% 1.00/1.05      ( sK0(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
% 1.00/1.05      | sK1 = k1_xboole_0 ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_3373,c_12,c_11,c_745,c_1310,c_2770]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2,plain,
% 1.00/1.05      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.00/1.05      inference(cnf_transformation,[],[f31]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_669,plain,
% 1.00/1.05      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 1.00/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3640,plain,
% 1.00/1.05      ( sK1 = k1_xboole_0
% 1.00/1.05      | r2_hidden(sK2,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 1.00/1.05      | r1_tarski(sK1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_3634,c_669]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4257,plain,
% 1.00/1.05      ( sK1 = k1_xboole_0 ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_2529,c_12,c_385,c_391,c_753,c_791,c_930,c_934,c_943,
% 1.00/1.05                 c_1419,c_2142,c_3640]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4286,plain,
% 1.00/1.05      ( k1_xboole_0 != k1_xboole_0 ),
% 1.00/1.05      inference(demodulation,[status(thm)],[c_4257,c_11]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4287,plain,
% 1.00/1.05      ( $false ),
% 1.00/1.05      inference(equality_resolution_simp,[status(thm)],[c_4286]) ).
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  ------                               Statistics
% 1.00/1.05  
% 1.00/1.05  ------ General
% 1.00/1.05  
% 1.00/1.05  abstr_ref_over_cycles:                  0
% 1.00/1.05  abstr_ref_under_cycles:                 0
% 1.00/1.05  gc_basic_clause_elim:                   0
% 1.00/1.05  forced_gc_time:                         0
% 1.00/1.05  parsing_time:                           0.023
% 1.00/1.05  unif_index_cands_time:                  0.
% 1.00/1.05  unif_index_add_time:                    0.
% 1.00/1.05  orderings_time:                         0.
% 1.00/1.05  out_proof_time:                         0.008
% 1.00/1.05  total_time:                             0.188
% 1.00/1.05  num_of_symbols:                         42
% 1.00/1.05  num_of_terms:                           3833
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing
% 1.00/1.05  
% 1.00/1.05  num_of_splits:                          0
% 1.00/1.05  num_of_split_atoms:                     0
% 1.00/1.05  num_of_reused_defs:                     0
% 1.00/1.05  num_eq_ax_congr_red:                    12
% 1.00/1.05  num_of_sem_filtered_clauses:            1
% 1.00/1.05  num_of_subtypes:                        0
% 1.00/1.05  monotx_restored_types:                  0
% 1.00/1.05  sat_num_of_epr_types:                   0
% 1.00/1.05  sat_num_of_non_cyclic_types:            0
% 1.00/1.05  sat_guarded_non_collapsed_types:        0
% 1.00/1.05  num_pure_diseq_elim:                    0
% 1.00/1.05  simp_replaced_by:                       0
% 1.00/1.05  res_preprocessed:                       54
% 1.00/1.05  prep_upred:                             0
% 1.00/1.05  prep_unflattend:                        24
% 1.00/1.05  smt_new_axioms:                         0
% 1.00/1.05  pred_elim_cands:                        3
% 1.00/1.05  pred_elim:                              0
% 1.00/1.05  pred_elim_cl:                           0
% 1.00/1.05  pred_elim_cycles:                       1
% 1.00/1.05  merged_defs:                            6
% 1.00/1.05  merged_defs_ncl:                        0
% 1.00/1.05  bin_hyper_res:                          6
% 1.00/1.05  prep_cycles:                            3
% 1.00/1.05  pred_elim_time:                         0.004
% 1.00/1.05  splitting_time:                         0.
% 1.00/1.05  sem_filter_time:                        0.
% 1.00/1.05  monotx_time:                            0.
% 1.00/1.05  subtype_inf_time:                       0.
% 1.00/1.05  
% 1.00/1.05  ------ Problem properties
% 1.00/1.05  
% 1.00/1.05  clauses:                                13
% 1.00/1.05  conjectures:                            3
% 1.00/1.05  epr:                                    5
% 1.00/1.05  horn:                                   11
% 1.00/1.05  ground:                                 2
% 1.00/1.05  unary:                                  4
% 1.00/1.05  binary:                                 7
% 1.00/1.05  lits:                                   24
% 1.00/1.05  lits_eq:                                6
% 1.00/1.05  fd_pure:                                0
% 1.00/1.05  fd_pseudo:                              0
% 1.00/1.05  fd_cond:                                2
% 1.00/1.05  fd_pseudo_cond:                         1
% 1.00/1.05  ac_symbols:                             0
% 1.00/1.05  
% 1.00/1.05  ------ Propositional Solver
% 1.00/1.05  
% 1.00/1.05  prop_solver_calls:                      25
% 1.00/1.05  prop_fast_solver_calls:                 427
% 1.00/1.05  smt_solver_calls:                       0
% 1.00/1.05  smt_fast_solver_calls:                  0
% 1.00/1.05  prop_num_of_clauses:                    1505
% 1.00/1.05  prop_preprocess_simplified:             4107
% 1.00/1.05  prop_fo_subsumed:                       9
% 1.00/1.05  prop_solver_time:                       0.
% 1.00/1.05  smt_solver_time:                        0.
% 1.00/1.05  smt_fast_solver_time:                   0.
% 1.00/1.05  prop_fast_solver_time:                  0.
% 1.00/1.05  prop_unsat_core_time:                   0.
% 1.00/1.05  
% 1.00/1.05  ------ QBF
% 1.00/1.05  
% 1.00/1.05  qbf_q_res:                              0
% 1.00/1.05  qbf_num_tautologies:                    0
% 1.00/1.05  qbf_prep_cycles:                        0
% 1.00/1.05  
% 1.00/1.05  ------ BMC1
% 1.00/1.05  
% 1.00/1.05  bmc1_current_bound:                     -1
% 1.00/1.05  bmc1_last_solved_bound:                 -1
% 1.00/1.05  bmc1_unsat_core_size:                   -1
% 1.00/1.05  bmc1_unsat_core_parents_size:           -1
% 1.00/1.05  bmc1_merge_next_fun:                    0
% 1.00/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.00/1.05  
% 1.00/1.05  ------ Instantiation
% 1.00/1.05  
% 1.00/1.05  inst_num_of_clauses:                    392
% 1.00/1.05  inst_num_in_passive:                    212
% 1.00/1.05  inst_num_in_active:                     178
% 1.00/1.05  inst_num_in_unprocessed:                2
% 1.00/1.05  inst_num_of_loops:                      250
% 1.00/1.05  inst_num_of_learning_restarts:          0
% 1.00/1.05  inst_num_moves_active_passive:          69
% 1.00/1.05  inst_lit_activity:                      0
% 1.00/1.05  inst_lit_activity_moves:                0
% 1.00/1.05  inst_num_tautologies:                   0
% 1.00/1.05  inst_num_prop_implied:                  0
% 1.00/1.05  inst_num_existing_simplified:           0
% 1.00/1.05  inst_num_eq_res_simplified:             0
% 1.00/1.05  inst_num_child_elim:                    0
% 1.00/1.05  inst_num_of_dismatching_blockings:      121
% 1.00/1.05  inst_num_of_non_proper_insts:           434
% 1.00/1.05  inst_num_of_duplicates:                 0
% 1.00/1.05  inst_inst_num_from_inst_to_res:         0
% 1.00/1.05  inst_dismatching_checking_time:         0.
% 1.00/1.05  
% 1.00/1.05  ------ Resolution
% 1.00/1.05  
% 1.00/1.05  res_num_of_clauses:                     0
% 1.00/1.05  res_num_in_passive:                     0
% 1.00/1.05  res_num_in_active:                      0
% 1.00/1.05  res_num_of_loops:                       57
% 1.00/1.05  res_forward_subset_subsumed:            24
% 1.00/1.05  res_backward_subset_subsumed:           0
% 1.00/1.05  res_forward_subsumed:                   0
% 1.00/1.05  res_backward_subsumed:                  0
% 1.00/1.05  res_forward_subsumption_resolution:     0
% 1.00/1.05  res_backward_subsumption_resolution:    0
% 1.00/1.05  res_clause_to_clause_subsumption:       757
% 1.00/1.05  res_orphan_elimination:                 0
% 1.00/1.05  res_tautology_del:                      29
% 1.00/1.05  res_num_eq_res_simplified:              0
% 1.00/1.05  res_num_sel_changes:                    0
% 1.00/1.05  res_moves_from_active_to_pass:          0
% 1.00/1.05  
% 1.00/1.05  ------ Superposition
% 1.00/1.05  
% 1.00/1.05  sup_time_total:                         0.
% 1.00/1.05  sup_time_generating:                    0.
% 1.00/1.05  sup_time_sim_full:                      0.
% 1.00/1.05  sup_time_sim_immed:                     0.
% 1.00/1.05  
% 1.00/1.05  sup_num_of_clauses:                     59
% 1.00/1.05  sup_num_in_active:                      18
% 1.00/1.05  sup_num_in_passive:                     41
% 1.00/1.05  sup_num_of_loops:                       48
% 1.00/1.05  sup_fw_superposition:                   73
% 1.00/1.05  sup_bw_superposition:                   64
% 1.00/1.05  sup_immediate_simplified:               35
% 1.00/1.05  sup_given_eliminated:                   0
% 1.00/1.05  comparisons_done:                       0
% 1.00/1.05  comparisons_avoided:                    36
% 1.00/1.05  
% 1.00/1.05  ------ Simplifications
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  sim_fw_subset_subsumed:                 12
% 1.00/1.05  sim_bw_subset_subsumed:                 4
% 1.00/1.05  sim_fw_subsumed:                        19
% 1.00/1.05  sim_bw_subsumed:                        4
% 1.00/1.05  sim_fw_subsumption_res:                 0
% 1.00/1.05  sim_bw_subsumption_res:                 0
% 1.00/1.05  sim_tautology_del:                      3
% 1.00/1.05  sim_eq_tautology_del:                   5
% 1.00/1.05  sim_eq_res_simp:                        0
% 1.00/1.05  sim_fw_demodulated:                     1
% 1.00/1.05  sim_bw_demodulated:                     27
% 1.00/1.05  sim_light_normalised:                   0
% 1.00/1.05  sim_joinable_taut:                      0
% 1.00/1.05  sim_joinable_simp:                      0
% 1.00/1.05  sim_ac_normalised:                      0
% 1.00/1.05  sim_smt_subsumption:                    0
% 1.00/1.05  
%------------------------------------------------------------------------------
