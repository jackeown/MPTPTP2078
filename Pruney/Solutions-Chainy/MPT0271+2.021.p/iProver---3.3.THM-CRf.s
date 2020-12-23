%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:09 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 695 expanded)
%              Number of clauses        :   45 ( 276 expanded)
%              Number of leaves         :   12 ( 147 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 (1308 expanded)
%              Number of equality atoms :  100 ( 768 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f34,f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f40,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f34,f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_467,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_468,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2549,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
    | k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_467,c_468])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_463,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1331,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = k1_xboole_0
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_463,c_468])).

cnf(c_9343,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2549,c_1331])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_469,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_471,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2127,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_471])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_473,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2364,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_473])).

cnf(c_5,plain,
    ( ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2092,plain,
    ( ~ r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2097,plain,
    ( r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2092])).

cnf(c_6801,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_2097])).

cnf(c_6802,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6801])).

cnf(c_6809,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_6802])).

cnf(c_9757,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9343,c_6809])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_464,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10114,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9757,c_464])).

cnf(c_10126,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
    | k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = k1_enumset1(sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_467,c_10114])).

cnf(c_10345,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10126,c_9757])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_465,plain,
    ( X0 = X1
    | r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10369,plain,
    ( sK0 = X0
    | r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10345,c_465])).

cnf(c_687,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_469])).

cnf(c_6811,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_687,c_6802])).

cnf(c_2119,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_469,c_471])).

cnf(c_7183,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6811,c_2119])).

cnf(c_12064,plain,
    ( sK0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10369,c_7183])).

cnf(c_12115,plain,
    ( r1_tarski(X0,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12064,c_469])).

cnf(c_12120,plain,
    ( X0 = X1
    | r1_tarski(k1_enumset1(X0,X0,X0),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12064,c_465])).

cnf(c_12169,plain,
    ( X0 = X1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12115,c_12120])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_861,plain,
    ( k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_12121,plain,
    ( sK0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12064,c_861])).

cnf(c_12179,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12169,c_12121])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.92/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/0.98  
% 3.92/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.98  
% 3.92/0.98  ------  iProver source info
% 3.92/0.98  
% 3.92/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.98  git: non_committed_changes: false
% 3.92/0.98  git: last_make_outside_of_git: false
% 3.92/0.98  
% 3.92/0.98  ------ 
% 3.92/0.98  ------ Parsing...
% 3.92/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.98  
% 3.92/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.92/0.98  
% 3.92/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.98  
% 3.92/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.98  ------ Proving...
% 3.92/0.98  ------ Problem Properties 
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  clauses                                 14
% 3.92/0.98  conjectures                             2
% 3.92/0.98  EPR                                     2
% 3.92/0.98  Horn                                    11
% 3.92/0.98  unary                                   5
% 3.92/0.98  binary                                  8
% 3.92/0.98  lits                                    24
% 3.92/0.98  lits eq                                 10
% 3.92/0.98  fd_pure                                 0
% 3.92/0.98  fd_pseudo                               0
% 3.92/0.98  fd_cond                                 0
% 3.92/0.98  fd_pseudo_cond                          2
% 3.92/0.98  AC symbols                              0
% 3.92/0.98  
% 3.92/0.98  ------ Input Options Time Limit: Unbounded
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  ------ 
% 3.92/0.98  Current options:
% 3.92/0.98  ------ 
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  ------ Proving...
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  % SZS status Theorem for theBenchmark.p
% 3.92/0.98  
% 3.92/0.98   Resolution empty clause
% 3.92/0.98  
% 3.92/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/0.98  
% 3.92/0.98  fof(f11,axiom,(
% 3.92/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f23,plain,(
% 3.92/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 3.92/0.98    inference(nnf_transformation,[],[f11])).
% 3.92/0.98  
% 3.92/0.98  fof(f38,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f23])).
% 3.92/0.98  
% 3.92/0.98  fof(f8,axiom,(
% 3.92/0.98    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f34,plain,(
% 3.92/0.98    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f8])).
% 3.92/0.98  
% 3.92/0.98  fof(f43,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0) | r2_hidden(X0,X1)) )),
% 3.92/0.98    inference(definition_unfolding,[],[f38,f34,f34])).
% 3.92/0.98  
% 3.92/0.98  fof(f9,axiom,(
% 3.92/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f20,plain,(
% 3.92/0.98    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.92/0.98    inference(ennf_transformation,[],[f9])).
% 3.92/0.98  
% 3.92/0.98  fof(f35,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f20])).
% 3.92/0.98  
% 3.92/0.98  fof(f42,plain,(
% 3.92/0.98    ( ! [X0,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.92/0.98    inference(definition_unfolding,[],[f35,f34])).
% 3.92/0.98  
% 3.92/0.98  fof(f13,conjecture,(
% 3.92/0.98    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f14,negated_conjecture,(
% 3.92/0.98    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.92/0.98    inference(negated_conjecture,[],[f13])).
% 3.92/0.98  
% 3.92/0.98  fof(f22,plain,(
% 3.92/0.98    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 3.92/0.98    inference(ennf_transformation,[],[f14])).
% 3.92/0.98  
% 3.92/0.98  fof(f24,plain,(
% 3.92/0.98    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 3.92/0.98    inference(nnf_transformation,[],[f22])).
% 3.92/0.98  
% 3.92/0.98  fof(f25,plain,(
% 3.92/0.98    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 3.92/0.98    introduced(choice_axiom,[])).
% 3.92/0.98  
% 3.92/0.98  fof(f26,plain,(
% 3.92/0.98    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 3.92/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 3.92/0.98  
% 3.92/0.98  fof(f40,plain,(
% 3.92/0.98    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.92/0.98    inference(cnf_transformation,[],[f26])).
% 3.92/0.98  
% 3.92/0.98  fof(f47,plain,(
% 3.92/0.98    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 3.92/0.98    inference(definition_unfolding,[],[f40,f34])).
% 3.92/0.98  
% 3.92/0.98  fof(f7,axiom,(
% 3.92/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f33,plain,(
% 3.92/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f7])).
% 3.92/0.98  
% 3.92/0.98  fof(f4,axiom,(
% 3.92/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f30,plain,(
% 3.92/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.92/0.98    inference(cnf_transformation,[],[f4])).
% 3.92/0.98  
% 3.92/0.98  fof(f5,axiom,(
% 3.92/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f19,plain,(
% 3.92/0.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.92/0.98    inference(ennf_transformation,[],[f5])).
% 3.92/0.98  
% 3.92/0.98  fof(f31,plain,(
% 3.92/0.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f19])).
% 3.92/0.98  
% 3.92/0.98  fof(f2,axiom,(
% 3.92/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f15,plain,(
% 3.92/0.98    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.92/0.98    inference(unused_predicate_definition_removal,[],[f2])).
% 3.92/0.98  
% 3.92/0.98  fof(f16,plain,(
% 3.92/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.92/0.98    inference(ennf_transformation,[],[f15])).
% 3.92/0.98  
% 3.92/0.98  fof(f17,plain,(
% 3.92/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.92/0.98    inference(flattening,[],[f16])).
% 3.92/0.98  
% 3.92/0.98  fof(f28,plain,(
% 3.92/0.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f17])).
% 3.92/0.98  
% 3.92/0.98  fof(f6,axiom,(
% 3.92/0.98    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f32,plain,(
% 3.92/0.98    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f6])).
% 3.92/0.98  
% 3.92/0.98  fof(f41,plain,(
% 3.92/0.98    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.92/0.98    inference(cnf_transformation,[],[f26])).
% 3.92/0.98  
% 3.92/0.98  fof(f46,plain,(
% 3.92/0.98    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 3.92/0.98    inference(definition_unfolding,[],[f41,f34])).
% 3.92/0.98  
% 3.92/0.98  fof(f12,axiom,(
% 3.92/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f21,plain,(
% 3.92/0.98    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.92/0.98    inference(ennf_transformation,[],[f12])).
% 3.92/0.98  
% 3.92/0.98  fof(f39,plain,(
% 3.92/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 3.92/0.98    inference(cnf_transformation,[],[f21])).
% 3.92/0.98  
% 3.92/0.98  fof(f45,plain,(
% 3.92/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 3.92/0.98    inference(definition_unfolding,[],[f39,f34,f34])).
% 3.92/0.98  
% 3.92/0.98  fof(f10,axiom,(
% 3.92/0.98    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.92/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/0.98  
% 3.92/0.98  fof(f36,plain,(
% 3.92/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.92/0.98    inference(cnf_transformation,[],[f10])).
% 3.92/0.98  
% 3.92/0.98  cnf(c_9,plain,
% 3.92/0.98      ( r2_hidden(X0,X1)
% 3.92/0.98      | k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0) ),
% 3.92/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_467,plain,
% 3.92/0.98      ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
% 3.92/0.98      | r2_hidden(X0,X1) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7,plain,
% 3.92/0.98      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1 ),
% 3.92/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_468,plain,
% 3.92/0.98      ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1
% 3.92/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2549,plain,
% 3.92/0.98      ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
% 3.92/0.98      | k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_467,c_468]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_13,negated_conjecture,
% 3.92/0.98      ( r2_hidden(sK0,sK1)
% 3.92/0.98      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
% 3.92/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_463,plain,
% 3.92/0.98      ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
% 3.92/0.98      | r2_hidden(sK0,sK1) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1331,plain,
% 3.92/0.98      ( k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = k1_xboole_0
% 3.92/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = sK1 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_463,c_468]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_9343,plain,
% 3.92/0.98      ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
% 3.92/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = sK1 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_2549,c_1331]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_6,plain,
% 3.92/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.92/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_469,plain,
% 3.92/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_3,plain,
% 3.92/0.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_4,plain,
% 3.92/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.92/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_471,plain,
% 3.92/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 3.92/0.98      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2127,plain,
% 3.92/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.92/0.98      | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_3,c_471]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_1,plain,
% 3.92/0.98      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_473,plain,
% 3.92/0.98      ( X0 = X1
% 3.92/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.92/0.98      | r2_xboole_0(X1,X0) = iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2364,plain,
% 3.92/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.92/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.92/0.98      | r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_2127,c_473]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_5,plain,
% 3.92/0.98      ( ~ r2_xboole_0(X0,k1_xboole_0) ),
% 3.92/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2092,plain,
% 3.92/0.98      ( ~ r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 3.92/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2097,plain,
% 3.92/0.98      ( r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_2092]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_6801,plain,
% 3.92/0.98      ( r1_tarski(X0,X1) != iProver_top | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.92/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2364,c_2097]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_6802,plain,
% 3.92/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 3.92/0.98      inference(renaming,[status(thm)],[c_6801]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_6809,plain,
% 3.92/0.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_469,c_6802]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_9757,plain,
% 3.92/0.98      ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
% 3.92/0.98      | k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_9343,c_6809]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12,negated_conjecture,
% 3.92/0.98      ( ~ r2_hidden(sK0,sK1)
% 3.92/0.98      | k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
% 3.92/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_464,plain,
% 3.92/0.98      ( k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
% 3.92/0.98      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_10114,plain,
% 3.92/0.98      ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
% 3.92/0.98      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_9757,c_464]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_10126,plain,
% 3.92/0.98      ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0
% 3.92/0.98      | k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) = k1_enumset1(sK0,sK0,sK0) ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_467,c_10114]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_10345,plain,
% 3.92/0.98      ( k1_enumset1(sK0,sK0,sK0) = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_10126,c_9757]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_11,plain,
% 3.92/0.98      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X1 = X0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_465,plain,
% 3.92/0.98      ( X0 = X1
% 3.92/0.98      | r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.92/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_10369,plain,
% 3.92/0.98      ( sK0 = X0
% 3.92/0.98      | r1_tarski(k1_xboole_0,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_10345,c_465]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_687,plain,
% 3.92/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_3,c_469]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_6811,plain,
% 3.92/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_687,c_6802]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_2119,plain,
% 3.92/0.98      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_469,c_471]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_7183,plain,
% 3.92/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_6811,c_2119]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12064,plain,
% 3.92/0.98      ( sK0 = X0 ),
% 3.92/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_10369,c_7183]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12115,plain,
% 3.92/0.98      ( r1_tarski(X0,sK0) = iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_12064,c_469]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12120,plain,
% 3.92/0.98      ( X0 = X1 | r1_tarski(k1_enumset1(X0,X0,X0),sK0) != iProver_top ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_12064,c_465]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12169,plain,
% 3.92/0.98      ( X0 = X1 ),
% 3.92/0.98      inference(backward_subsumption_resolution,
% 3.92/0.98                [status(thm)],
% 3.92/0.98                [c_12115,c_12120]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_8,plain,
% 3.92/0.98      ( k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
% 3.92/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_861,plain,
% 3.92/0.98      ( k2_tarski(X0,X1) != k1_xboole_0 ),
% 3.92/0.98      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12121,plain,
% 3.92/0.98      ( sK0 != k1_xboole_0 ),
% 3.92/0.98      inference(demodulation,[status(thm)],[c_12064,c_861]) ).
% 3.92/0.98  
% 3.92/0.98  cnf(c_12179,plain,
% 3.92/0.98      ( $false ),
% 3.92/0.98      inference(backward_subsumption_resolution,
% 3.92/0.98                [status(thm)],
% 3.92/0.98                [c_12169,c_12121]) ).
% 3.92/0.98  
% 3.92/0.98  
% 3.92/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/0.98  
% 3.92/0.98  ------                               Statistics
% 3.92/0.98  
% 3.92/0.98  ------ Selected
% 3.92/0.98  
% 3.92/0.98  total_time:                             0.346
% 3.92/0.98  
%------------------------------------------------------------------------------
