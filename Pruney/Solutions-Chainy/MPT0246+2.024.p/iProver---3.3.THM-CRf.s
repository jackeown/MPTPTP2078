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
% DateTime   : Thu Dec  3 11:32:05 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 329 expanded)
%              Number of clauses        :   55 ( 112 expanded)
%              Number of leaves         :   15 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  217 ( 845 expanded)
%              Number of equality atoms :  139 ( 525 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK3 = X2
          | ~ r2_hidden(X2,sK2) )
      & k1_xboole_0 != sK2
      & k1_tarski(sK3) != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ! [X2] :
        ( sK3 = X2
        | ~ r2_hidden(X2,sK2) )
    & k1_xboole_0 != sK2
    & k1_tarski(sK3) != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f23])).

fof(f39,plain,(
    ! [X2] :
      ( sK3 = X2
      | ~ r2_hidden(X2,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f37,plain,(
    k1_tarski(sK3) != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) != sK2 ),
    inference(definition_unfolding,[],[f37,f41])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_484,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_485,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_743,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_485])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_481,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1353,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_743,c_481])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_478,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1811,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_478])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | sK3 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_477,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_744,plain,
    ( sK0(sK2,X0) = sK3
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_477])).

cnf(c_858,plain,
    ( k4_xboole_0(sK2,X0) = k1_xboole_0
    | sK0(sK2,X0) = sK3 ),
    inference(superposition,[status(thm)],[c_744,c_481])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_482,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_739,plain,
    ( sK1(sK2) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_482,c_477])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_223,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_232,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_224,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_558,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_559,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_850,plain,
    ( sK1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_10,c_232,c_559])).

cnf(c_853,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_482])).

cnf(c_551,plain,
    ( r2_hidden(sK1(sK2),sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_552,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK1(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_581,plain,
    ( ~ r2_hidden(sK1(sK2),sK2)
    | sK3 = sK1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_596,plain,
    ( k4_xboole_0(sK2,X0) != k4_xboole_0(X0,sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_687,plain,
    ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_688,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_570,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK2),sK2)
    | X0 != sK1(sK2)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_692,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1(sK2),sK2)
    | X0 != sK1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_733,plain,
    ( ~ r2_hidden(sK1(sK2),sK2)
    | r2_hidden(sK3,sK2)
    | sK2 != sK2
    | sK3 != sK1(sK2) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_734,plain,
    ( sK2 != sK2
    | sK3 != sK1(sK2)
    | r2_hidden(sK1(sK2),sK2) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_937,plain,
    ( r2_hidden(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_10,c_551,c_552,c_581,c_687,c_688,c_734])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_479,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_943,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_937,c_479])).

cnf(c_1049,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK2
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_943,c_6])).

cnf(c_11,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_557,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK2
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_594,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != X0
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_595,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != k1_xboole_0
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_701,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1307,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_11,c_10,c_551,c_557,c_581,c_595,c_687,c_688,c_701,c_733])).

cnf(c_1310,plain,
    ( sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_858,c_1307])).

cnf(c_1360,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r1_tarski(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_485])).

cnf(c_860,plain,
    ( ~ r1_tarski(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_861,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | r1_tarski(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_1490,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_11,c_10,c_551,c_557,c_581,c_595,c_687,c_688,c_701,c_733,c_861])).

cnf(c_1823,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1811,c_1490])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:15:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.71/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/0.99  
% 1.71/0.99  ------  iProver source info
% 1.71/0.99  
% 1.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/0.99  git: non_committed_changes: false
% 1.71/0.99  git: last_make_outside_of_git: false
% 1.71/0.99  
% 1.71/0.99  ------ 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options
% 1.71/0.99  
% 1.71/0.99  --out_options                           all
% 1.71/0.99  --tptp_safe_out                         true
% 1.71/0.99  --problem_path                          ""
% 1.71/0.99  --include_path                          ""
% 1.71/0.99  --clausifier                            res/vclausify_rel
% 1.71/0.99  --clausifier_options                    --mode clausify
% 1.71/0.99  --stdin                                 false
% 1.71/0.99  --stats_out                             all
% 1.71/0.99  
% 1.71/0.99  ------ General Options
% 1.71/0.99  
% 1.71/0.99  --fof                                   false
% 1.71/0.99  --time_out_real                         305.
% 1.71/0.99  --time_out_virtual                      -1.
% 1.71/0.99  --symbol_type_check                     false
% 1.71/0.99  --clausify_out                          false
% 1.71/0.99  --sig_cnt_out                           false
% 1.71/0.99  --trig_cnt_out                          false
% 1.71/0.99  --trig_cnt_out_tolerance                1.
% 1.71/0.99  --trig_cnt_out_sk_spl                   false
% 1.71/0.99  --abstr_cl_out                          false
% 1.71/0.99  
% 1.71/0.99  ------ Global Options
% 1.71/0.99  
% 1.71/0.99  --schedule                              default
% 1.71/0.99  --add_important_lit                     false
% 1.71/0.99  --prop_solver_per_cl                    1000
% 1.71/0.99  --min_unsat_core                        false
% 1.71/0.99  --soft_assumptions                      false
% 1.71/0.99  --soft_lemma_size                       3
% 1.71/0.99  --prop_impl_unit_size                   0
% 1.71/0.99  --prop_impl_unit                        []
% 1.71/0.99  --share_sel_clauses                     true
% 1.71/0.99  --reset_solvers                         false
% 1.71/0.99  --bc_imp_inh                            [conj_cone]
% 1.71/0.99  --conj_cone_tolerance                   3.
% 1.71/0.99  --extra_neg_conj                        none
% 1.71/0.99  --large_theory_mode                     true
% 1.71/0.99  --prolific_symb_bound                   200
% 1.71/0.99  --lt_threshold                          2000
% 1.71/0.99  --clause_weak_htbl                      true
% 1.71/0.99  --gc_record_bc_elim                     false
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing Options
% 1.71/0.99  
% 1.71/0.99  --preprocessing_flag                    true
% 1.71/0.99  --time_out_prep_mult                    0.1
% 1.71/0.99  --splitting_mode                        input
% 1.71/0.99  --splitting_grd                         true
% 1.71/0.99  --splitting_cvd                         false
% 1.71/0.99  --splitting_cvd_svl                     false
% 1.71/0.99  --splitting_nvd                         32
% 1.71/0.99  --sub_typing                            true
% 1.71/0.99  --prep_gs_sim                           true
% 1.71/0.99  --prep_unflatten                        true
% 1.71/0.99  --prep_res_sim                          true
% 1.71/0.99  --prep_upred                            true
% 1.71/0.99  --prep_sem_filter                       exhaustive
% 1.71/0.99  --prep_sem_filter_out                   false
% 1.71/0.99  --pred_elim                             true
% 1.71/0.99  --res_sim_input                         true
% 1.71/0.99  --eq_ax_congr_red                       true
% 1.71/0.99  --pure_diseq_elim                       true
% 1.71/0.99  --brand_transform                       false
% 1.71/0.99  --non_eq_to_eq                          false
% 1.71/0.99  --prep_def_merge                        true
% 1.71/0.99  --prep_def_merge_prop_impl              false
% 1.71/0.99  --prep_def_merge_mbd                    true
% 1.71/0.99  --prep_def_merge_tr_red                 false
% 1.71/0.99  --prep_def_merge_tr_cl                  false
% 1.71/0.99  --smt_preprocessing                     true
% 1.71/0.99  --smt_ac_axioms                         fast
% 1.71/0.99  --preprocessed_out                      false
% 1.71/0.99  --preprocessed_stats                    false
% 1.71/0.99  
% 1.71/0.99  ------ Abstraction refinement Options
% 1.71/0.99  
% 1.71/0.99  --abstr_ref                             []
% 1.71/0.99  --abstr_ref_prep                        false
% 1.71/0.99  --abstr_ref_until_sat                   false
% 1.71/0.99  --abstr_ref_sig_restrict                funpre
% 1.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.99  --abstr_ref_under                       []
% 1.71/0.99  
% 1.71/0.99  ------ SAT Options
% 1.71/0.99  
% 1.71/0.99  --sat_mode                              false
% 1.71/0.99  --sat_fm_restart_options                ""
% 1.71/0.99  --sat_gr_def                            false
% 1.71/0.99  --sat_epr_types                         true
% 1.71/0.99  --sat_non_cyclic_types                  false
% 1.71/0.99  --sat_finite_models                     false
% 1.71/0.99  --sat_fm_lemmas                         false
% 1.71/0.99  --sat_fm_prep                           false
% 1.71/0.99  --sat_fm_uc_incr                        true
% 1.71/0.99  --sat_out_model                         small
% 1.71/0.99  --sat_out_clauses                       false
% 1.71/0.99  
% 1.71/0.99  ------ QBF Options
% 1.71/0.99  
% 1.71/0.99  --qbf_mode                              false
% 1.71/0.99  --qbf_elim_univ                         false
% 1.71/0.99  --qbf_dom_inst                          none
% 1.71/0.99  --qbf_dom_pre_inst                      false
% 1.71/0.99  --qbf_sk_in                             false
% 1.71/0.99  --qbf_pred_elim                         true
% 1.71/0.99  --qbf_split                             512
% 1.71/0.99  
% 1.71/0.99  ------ BMC1 Options
% 1.71/0.99  
% 1.71/0.99  --bmc1_incremental                      false
% 1.71/0.99  --bmc1_axioms                           reachable_all
% 1.71/0.99  --bmc1_min_bound                        0
% 1.71/0.99  --bmc1_max_bound                        -1
% 1.71/0.99  --bmc1_max_bound_default                -1
% 1.71/0.99  --bmc1_symbol_reachability              true
% 1.71/0.99  --bmc1_property_lemmas                  false
% 1.71/0.99  --bmc1_k_induction                      false
% 1.71/0.99  --bmc1_non_equiv_states                 false
% 1.71/0.99  --bmc1_deadlock                         false
% 1.71/0.99  --bmc1_ucm                              false
% 1.71/0.99  --bmc1_add_unsat_core                   none
% 1.71/0.99  --bmc1_unsat_core_children              false
% 1.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.99  --bmc1_out_stat                         full
% 1.71/0.99  --bmc1_ground_init                      false
% 1.71/0.99  --bmc1_pre_inst_next_state              false
% 1.71/0.99  --bmc1_pre_inst_state                   false
% 1.71/0.99  --bmc1_pre_inst_reach_state             false
% 1.71/0.99  --bmc1_out_unsat_core                   false
% 1.71/0.99  --bmc1_aig_witness_out                  false
% 1.71/0.99  --bmc1_verbose                          false
% 1.71/0.99  --bmc1_dump_clauses_tptp                false
% 1.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.99  --bmc1_dump_file                        -
% 1.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.99  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     num_symb
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       true
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  ------ Parsing...
% 1.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.71/0.99  ------ Proving...
% 1.71/0.99  ------ Problem Properties 
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  clauses                                 12
% 1.71/0.99  conjectures                             3
% 1.71/0.99  EPR                                     3
% 1.71/0.99  Horn                                    10
% 1.71/0.99  unary                                   2
% 1.71/0.99  binary                                  9
% 1.71/0.99  lits                                    23
% 1.71/0.99  lits eq                                 10
% 1.71/0.99  fd_pure                                 0
% 1.71/0.99  fd_pseudo                               0
% 1.71/0.99  fd_cond                                 2
% 1.71/0.99  fd_pseudo_cond                          1
% 1.71/0.99  AC symbols                              0
% 1.71/0.99  
% 1.71/0.99  ------ Schedule dynamic 5 is on 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ 
% 1.71/0.99  Current options:
% 1.71/0.99  ------ 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options
% 1.71/0.99  
% 1.71/0.99  --out_options                           all
% 1.71/0.99  --tptp_safe_out                         true
% 1.71/0.99  --problem_path                          ""
% 1.71/0.99  --include_path                          ""
% 1.71/0.99  --clausifier                            res/vclausify_rel
% 1.71/0.99  --clausifier_options                    --mode clausify
% 1.71/0.99  --stdin                                 false
% 1.71/0.99  --stats_out                             all
% 1.71/0.99  
% 1.71/0.99  ------ General Options
% 1.71/0.99  
% 1.71/0.99  --fof                                   false
% 1.71/0.99  --time_out_real                         305.
% 1.71/0.99  --time_out_virtual                      -1.
% 1.71/0.99  --symbol_type_check                     false
% 1.71/0.99  --clausify_out                          false
% 1.71/0.99  --sig_cnt_out                           false
% 1.71/0.99  --trig_cnt_out                          false
% 1.71/0.99  --trig_cnt_out_tolerance                1.
% 1.71/0.99  --trig_cnt_out_sk_spl                   false
% 1.71/0.99  --abstr_cl_out                          false
% 1.71/0.99  
% 1.71/0.99  ------ Global Options
% 1.71/0.99  
% 1.71/0.99  --schedule                              default
% 1.71/0.99  --add_important_lit                     false
% 1.71/0.99  --prop_solver_per_cl                    1000
% 1.71/0.99  --min_unsat_core                        false
% 1.71/0.99  --soft_assumptions                      false
% 1.71/0.99  --soft_lemma_size                       3
% 1.71/0.99  --prop_impl_unit_size                   0
% 1.71/0.99  --prop_impl_unit                        []
% 1.71/0.99  --share_sel_clauses                     true
% 1.71/0.99  --reset_solvers                         false
% 1.71/0.99  --bc_imp_inh                            [conj_cone]
% 1.71/0.99  --conj_cone_tolerance                   3.
% 1.71/0.99  --extra_neg_conj                        none
% 1.71/0.99  --large_theory_mode                     true
% 1.71/0.99  --prolific_symb_bound                   200
% 1.71/0.99  --lt_threshold                          2000
% 1.71/0.99  --clause_weak_htbl                      true
% 1.71/0.99  --gc_record_bc_elim                     false
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing Options
% 1.71/0.99  
% 1.71/0.99  --preprocessing_flag                    true
% 1.71/0.99  --time_out_prep_mult                    0.1
% 1.71/0.99  --splitting_mode                        input
% 1.71/0.99  --splitting_grd                         true
% 1.71/0.99  --splitting_cvd                         false
% 1.71/0.99  --splitting_cvd_svl                     false
% 1.71/0.99  --splitting_nvd                         32
% 1.71/0.99  --sub_typing                            true
% 1.71/0.99  --prep_gs_sim                           true
% 1.71/0.99  --prep_unflatten                        true
% 1.71/0.99  --prep_res_sim                          true
% 1.71/0.99  --prep_upred                            true
% 1.71/0.99  --prep_sem_filter                       exhaustive
% 1.71/0.99  --prep_sem_filter_out                   false
% 1.71/0.99  --pred_elim                             true
% 1.71/0.99  --res_sim_input                         true
% 1.71/0.99  --eq_ax_congr_red                       true
% 1.71/0.99  --pure_diseq_elim                       true
% 1.71/0.99  --brand_transform                       false
% 1.71/0.99  --non_eq_to_eq                          false
% 1.71/0.99  --prep_def_merge                        true
% 1.71/0.99  --prep_def_merge_prop_impl              false
% 1.71/0.99  --prep_def_merge_mbd                    true
% 1.71/0.99  --prep_def_merge_tr_red                 false
% 1.71/0.99  --prep_def_merge_tr_cl                  false
% 1.71/0.99  --smt_preprocessing                     true
% 1.71/0.99  --smt_ac_axioms                         fast
% 1.71/0.99  --preprocessed_out                      false
% 1.71/0.99  --preprocessed_stats                    false
% 1.71/0.99  
% 1.71/0.99  ------ Abstraction refinement Options
% 1.71/0.99  
% 1.71/0.99  --abstr_ref                             []
% 1.71/0.99  --abstr_ref_prep                        false
% 1.71/0.99  --abstr_ref_until_sat                   false
% 1.71/0.99  --abstr_ref_sig_restrict                funpre
% 1.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.99  --abstr_ref_under                       []
% 1.71/0.99  
% 1.71/0.99  ------ SAT Options
% 1.71/0.99  
% 1.71/0.99  --sat_mode                              false
% 1.71/0.99  --sat_fm_restart_options                ""
% 1.71/0.99  --sat_gr_def                            false
% 1.71/0.99  --sat_epr_types                         true
% 1.71/0.99  --sat_non_cyclic_types                  false
% 1.71/0.99  --sat_finite_models                     false
% 1.71/0.99  --sat_fm_lemmas                         false
% 1.71/0.99  --sat_fm_prep                           false
% 1.71/0.99  --sat_fm_uc_incr                        true
% 1.71/0.99  --sat_out_model                         small
% 1.71/0.99  --sat_out_clauses                       false
% 1.71/0.99  
% 1.71/0.99  ------ QBF Options
% 1.71/0.99  
% 1.71/0.99  --qbf_mode                              false
% 1.71/0.99  --qbf_elim_univ                         false
% 1.71/0.99  --qbf_dom_inst                          none
% 1.71/0.99  --qbf_dom_pre_inst                      false
% 1.71/0.99  --qbf_sk_in                             false
% 1.71/0.99  --qbf_pred_elim                         true
% 1.71/0.99  --qbf_split                             512
% 1.71/0.99  
% 1.71/0.99  ------ BMC1 Options
% 1.71/0.99  
% 1.71/0.99  --bmc1_incremental                      false
% 1.71/0.99  --bmc1_axioms                           reachable_all
% 1.71/0.99  --bmc1_min_bound                        0
% 1.71/0.99  --bmc1_max_bound                        -1
% 1.71/0.99  --bmc1_max_bound_default                -1
% 1.71/0.99  --bmc1_symbol_reachability              true
% 1.71/0.99  --bmc1_property_lemmas                  false
% 1.71/0.99  --bmc1_k_induction                      false
% 1.71/0.99  --bmc1_non_equiv_states                 false
% 1.71/0.99  --bmc1_deadlock                         false
% 1.71/0.99  --bmc1_ucm                              false
% 1.71/0.99  --bmc1_add_unsat_core                   none
% 1.71/0.99  --bmc1_unsat_core_children              false
% 1.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.99  --bmc1_out_stat                         full
% 1.71/0.99  --bmc1_ground_init                      false
% 1.71/0.99  --bmc1_pre_inst_next_state              false
% 1.71/0.99  --bmc1_pre_inst_state                   false
% 1.71/0.99  --bmc1_pre_inst_reach_state             false
% 1.71/0.99  --bmc1_out_unsat_core                   false
% 1.71/0.99  --bmc1_aig_witness_out                  false
% 1.71/0.99  --bmc1_verbose                          false
% 1.71/0.99  --bmc1_dump_clauses_tptp                false
% 1.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.99  --bmc1_dump_file                        -
% 1.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.99  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     none
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       false
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ Proving...
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS status Theorem for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99   Resolution empty clause
% 1.71/0.99  
% 1.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  fof(f1,axiom,(
% 1.71/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f11,plain,(
% 1.71/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f1])).
% 1.71/0.99  
% 1.71/0.99  fof(f15,plain,(
% 1.71/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.71/0.99    inference(nnf_transformation,[],[f11])).
% 1.71/0.99  
% 1.71/0.99  fof(f16,plain,(
% 1.71/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.71/0.99    inference(rectify,[],[f15])).
% 1.71/0.99  
% 1.71/0.99  fof(f17,plain,(
% 1.71/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f18,plain,(
% 1.71/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 1.71/0.99  
% 1.71/0.99  fof(f26,plain,(
% 1.71/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f18])).
% 1.71/0.99  
% 1.71/0.99  fof(f27,plain,(
% 1.71/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f18])).
% 1.71/0.99  
% 1.71/0.99  fof(f3,axiom,(
% 1.71/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f21,plain,(
% 1.71/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.71/0.99    inference(nnf_transformation,[],[f3])).
% 1.71/0.99  
% 1.71/0.99  fof(f30,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f21])).
% 1.71/0.99  
% 1.71/0.99  fof(f8,axiom,(
% 1.71/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f22,plain,(
% 1.71/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.71/0.99    inference(nnf_transformation,[],[f8])).
% 1.71/0.99  
% 1.71/0.99  fof(f35,plain,(
% 1.71/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f22])).
% 1.71/0.99  
% 1.71/0.99  fof(f5,axiom,(
% 1.71/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f32,plain,(
% 1.71/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f5])).
% 1.71/0.99  
% 1.71/0.99  fof(f6,axiom,(
% 1.71/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f33,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f6])).
% 1.71/0.99  
% 1.71/0.99  fof(f7,axiom,(
% 1.71/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f34,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f7])).
% 1.71/0.99  
% 1.71/0.99  fof(f40,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.71/0.99    inference(definition_unfolding,[],[f33,f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f41,plain,(
% 1.71/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.71/0.99    inference(definition_unfolding,[],[f32,f40])).
% 1.71/0.99  
% 1.71/0.99  fof(f43,plain,(
% 1.71/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.71/0.99    inference(definition_unfolding,[],[f35,f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f9,conjecture,(
% 1.71/0.99    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f10,negated_conjecture,(
% 1.71/0.99    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.71/0.99    inference(negated_conjecture,[],[f9])).
% 1.71/0.99  
% 1.71/0.99  fof(f14,plain,(
% 1.71/0.99    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.71/0.99    inference(ennf_transformation,[],[f10])).
% 1.71/0.99  
% 1.71/0.99  fof(f23,plain,(
% 1.71/0.99    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK3 = X2 | ~r2_hidden(X2,sK2)) & k1_xboole_0 != sK2 & k1_tarski(sK3) != sK2)),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f24,plain,(
% 1.71/0.99    ! [X2] : (sK3 = X2 | ~r2_hidden(X2,sK2)) & k1_xboole_0 != sK2 & k1_tarski(sK3) != sK2),
% 1.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f23])).
% 1.71/0.99  
% 1.71/0.99  fof(f39,plain,(
% 1.71/0.99    ( ! [X2] : (sK3 = X2 | ~r2_hidden(X2,sK2)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f24])).
% 1.71/0.99  
% 1.71/0.99  fof(f2,axiom,(
% 1.71/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f12,plain,(
% 1.71/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.71/0.99    inference(ennf_transformation,[],[f2])).
% 1.71/0.99  
% 1.71/0.99  fof(f19,plain,(
% 1.71/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f20,plain,(
% 1.71/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).
% 1.71/0.99  
% 1.71/0.99  fof(f28,plain,(
% 1.71/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.71/0.99    inference(cnf_transformation,[],[f20])).
% 1.71/0.99  
% 1.71/0.99  fof(f38,plain,(
% 1.71/0.99    k1_xboole_0 != sK2),
% 1.71/0.99    inference(cnf_transformation,[],[f24])).
% 1.71/0.99  
% 1.71/0.99  fof(f4,axiom,(
% 1.71/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.71/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f13,plain,(
% 1.71/0.99    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f4])).
% 1.71/0.99  
% 1.71/0.99  fof(f31,plain,(
% 1.71/0.99    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f13])).
% 1.71/0.99  
% 1.71/0.99  fof(f36,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f22])).
% 1.71/0.99  
% 1.71/0.99  fof(f42,plain,(
% 1.71/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.71/0.99    inference(definition_unfolding,[],[f36,f41])).
% 1.71/0.99  
% 1.71/0.99  fof(f37,plain,(
% 1.71/0.99    k1_tarski(sK3) != sK2),
% 1.71/0.99    inference(cnf_transformation,[],[f24])).
% 1.71/0.99  
% 1.71/0.99  fof(f44,plain,(
% 1.71/0.99    k2_enumset1(sK3,sK3,sK3,sK3) != sK2),
% 1.71/0.99    inference(definition_unfolding,[],[f37,f41])).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1,plain,
% 1.71/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f26]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_484,plain,
% 1.71/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.71/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_0,plain,
% 1.71/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_485,plain,
% 1.71/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 1.71/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_743,plain,
% 1.71/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_484,c_485]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_4,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_481,plain,
% 1.71/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1353,plain,
% 1.71/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_743,c_481]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_8,plain,
% 1.71/0.99      ( r2_hidden(X0,X1)
% 1.71/0.99      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_478,plain,
% 1.71/0.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0
% 1.71/0.99      | r2_hidden(X0,X1) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1811,plain,
% 1.71/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1353,c_478]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_9,negated_conjecture,
% 1.71/0.99      ( ~ r2_hidden(X0,sK2) | sK3 = X0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_477,plain,
% 1.71/0.99      ( sK3 = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_744,plain,
% 1.71/0.99      ( sK0(sK2,X0) = sK3 | r1_tarski(sK2,X0) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_484,c_477]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_858,plain,
% 1.71/0.99      ( k4_xboole_0(sK2,X0) = k1_xboole_0 | sK0(sK2,X0) = sK3 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_744,c_481]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_3,plain,
% 1.71/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_482,plain,
% 1.71/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_739,plain,
% 1.71/0.99      ( sK1(sK2) = sK3 | sK2 = k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_482,c_477]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_10,negated_conjecture,
% 1.71/0.99      ( k1_xboole_0 != sK2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_223,plain,( X0 = X0 ),theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_232,plain,
% 1.71/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_223]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_224,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_558,plain,
% 1.71/0.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_224]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_559,plain,
% 1.71/0.99      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_558]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_850,plain,
% 1.71/0.99      ( sK1(sK2) = sK3 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_739,c_10,c_232,c_559]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_853,plain,
% 1.71/0.99      ( sK2 = k1_xboole_0 | r2_hidden(sK3,sK2) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_850,c_482]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_551,plain,
% 1.71/0.99      ( r2_hidden(sK1(sK2),sK2) | k1_xboole_0 = sK2 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_552,plain,
% 1.71/0.99      ( k1_xboole_0 = sK2 | r2_hidden(sK1(sK2),sK2) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_581,plain,
% 1.71/0.99      ( ~ r2_hidden(sK1(sK2),sK2) | sK3 = sK1(sK2) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_6,plain,
% 1.71/0.99      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_596,plain,
% 1.71/0.99      ( k4_xboole_0(sK2,X0) != k4_xboole_0(X0,sK2) | sK2 = X0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_687,plain,
% 1.71/0.99      ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,sK2) | sK2 = sK2 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_596]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_688,plain,
% 1.71/0.99      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_223]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_225,plain,
% 1.71/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_570,plain,
% 1.71/0.99      ( r2_hidden(X0,X1)
% 1.71/0.99      | ~ r2_hidden(sK1(sK2),sK2)
% 1.71/0.99      | X0 != sK1(sK2)
% 1.71/0.99      | X1 != sK2 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_225]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_692,plain,
% 1.71/0.99      ( r2_hidden(X0,sK2)
% 1.71/0.99      | ~ r2_hidden(sK1(sK2),sK2)
% 1.71/0.99      | X0 != sK1(sK2)
% 1.71/0.99      | sK2 != sK2 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_570]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_733,plain,
% 1.71/0.99      ( ~ r2_hidden(sK1(sK2),sK2)
% 1.71/0.99      | r2_hidden(sK3,sK2)
% 1.71/0.99      | sK2 != sK2
% 1.71/0.99      | sK3 != sK1(sK2) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_734,plain,
% 1.71/0.99      ( sK2 != sK2
% 1.71/0.99      | sK3 != sK1(sK2)
% 1.71/0.99      | r2_hidden(sK1(sK2),sK2) != iProver_top
% 1.71/0.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_937,plain,
% 1.71/0.99      ( r2_hidden(sK3,sK2) = iProver_top ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_853,c_10,c_551,c_552,c_581,c_687,c_688,c_734]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_7,plain,
% 1.71/0.99      ( ~ r2_hidden(X0,X1)
% 1.71/0.99      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_479,plain,
% 1.71/0.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
% 1.71/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_943,plain,
% 1.71/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_937,c_479]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1049,plain,
% 1.71/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK2
% 1.71/0.99      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_943,c_6]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_11,negated_conjecture,
% 1.71/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) != sK2 ),
% 1.71/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_557,plain,
% 1.71/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK2
% 1.71/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_594,plain,
% 1.71/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != X0
% 1.71/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.71/0.99      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_224]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_595,plain,
% 1.71/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.71/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != k1_xboole_0
% 1.71/0.99      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_594]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_701,plain,
% 1.71/0.99      ( ~ r2_hidden(sK3,sK2)
% 1.71/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) = k1_xboole_0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1307,plain,
% 1.71/0.99      ( k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1049,c_11,c_10,c_551,c_557,c_581,c_595,c_687,c_688,c_701,
% 1.71/0.99                 c_733]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1310,plain,
% 1.71/0.99      ( sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_858,c_1307]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1360,plain,
% 1.71/0.99      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 1.71/0.99      | r1_tarski(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1310,c_485]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_860,plain,
% 1.71/0.99      ( ~ r1_tarski(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.71/0.99      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_861,plain,
% 1.71/0.99      ( k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 1.71/0.99      | r1_tarski(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1490,plain,
% 1.71/0.99      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1360,c_11,c_10,c_551,c_557,c_581,c_595,c_687,c_688,c_701,
% 1.71/0.99                 c_733,c_861]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1823,plain,
% 1.71/0.99      ( $false ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1811,c_1490]) ).
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  ------                               Statistics
% 1.71/0.99  
% 1.71/0.99  ------ General
% 1.71/0.99  
% 1.71/0.99  abstr_ref_over_cycles:                  0
% 1.71/0.99  abstr_ref_under_cycles:                 0
% 1.71/0.99  gc_basic_clause_elim:                   0
% 1.71/0.99  forced_gc_time:                         0
% 1.71/0.99  parsing_time:                           0.007
% 1.71/0.99  unif_index_cands_time:                  0.
% 1.71/0.99  unif_index_add_time:                    0.
% 1.71/0.99  orderings_time:                         0.
% 1.71/0.99  out_proof_time:                         0.008
% 1.71/0.99  total_time:                             0.086
% 1.71/0.99  num_of_symbols:                         40
% 1.71/0.99  num_of_terms:                           1635
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing
% 1.71/0.99  
% 1.71/0.99  num_of_splits:                          0
% 1.71/0.99  num_of_split_atoms:                     0
% 1.71/0.99  num_of_reused_defs:                     0
% 1.71/0.99  num_eq_ax_congr_red:                    12
% 1.71/0.99  num_of_sem_filtered_clauses:            1
% 1.71/0.99  num_of_subtypes:                        0
% 1.71/0.99  monotx_restored_types:                  0
% 1.71/0.99  sat_num_of_epr_types:                   0
% 1.71/0.99  sat_num_of_non_cyclic_types:            0
% 1.71/0.99  sat_guarded_non_collapsed_types:        0
% 1.71/0.99  num_pure_diseq_elim:                    0
% 1.71/0.99  simp_replaced_by:                       0
% 1.71/0.99  res_preprocessed:                       47
% 1.71/0.99  prep_upred:                             0
% 1.71/0.99  prep_unflattend:                        6
% 1.71/0.99  smt_new_axioms:                         0
% 1.71/0.99  pred_elim_cands:                        2
% 1.71/0.99  pred_elim:                              0
% 1.71/0.99  pred_elim_cl:                           0
% 1.71/0.99  pred_elim_cycles:                       1
% 1.71/0.99  merged_defs:                            12
% 1.71/0.99  merged_defs_ncl:                        0
% 1.71/0.99  bin_hyper_res:                          12
% 1.71/0.99  prep_cycles:                            3
% 1.71/0.99  pred_elim_time:                         0.001
% 1.71/0.99  splitting_time:                         0.
% 1.71/0.99  sem_filter_time:                        0.
% 1.71/0.99  monotx_time:                            0.
% 1.71/0.99  subtype_inf_time:                       0.
% 1.71/0.99  
% 1.71/0.99  ------ Problem properties
% 1.71/0.99  
% 1.71/0.99  clauses:                                12
% 1.71/0.99  conjectures:                            3
% 1.71/0.99  epr:                                    3
% 1.71/0.99  horn:                                   10
% 1.71/0.99  ground:                                 2
% 1.71/0.99  unary:                                  2
% 1.71/0.99  binary:                                 9
% 1.71/0.99  lits:                                   23
% 1.71/0.99  lits_eq:                                10
% 1.71/0.99  fd_pure:                                0
% 1.71/0.99  fd_pseudo:                              0
% 1.71/0.99  fd_cond:                                2
% 1.71/0.99  fd_pseudo_cond:                         1
% 1.71/0.99  ac_symbols:                             0
% 1.71/0.99  
% 1.71/0.99  ------ Propositional Solver
% 1.71/0.99  
% 1.71/0.99  prop_solver_calls:                      23
% 1.71/0.99  prop_fast_solver_calls:                 290
% 1.71/0.99  smt_solver_calls:                       0
% 1.71/0.99  smt_fast_solver_calls:                  0
% 1.71/0.99  prop_num_of_clauses:                    586
% 1.71/0.99  prop_preprocess_simplified:             2135
% 1.71/0.99  prop_fo_subsumed:                       5
% 1.71/0.99  prop_solver_time:                       0.
% 1.71/0.99  smt_solver_time:                        0.
% 1.71/0.99  smt_fast_solver_time:                   0.
% 1.71/0.99  prop_fast_solver_time:                  0.
% 1.71/0.99  prop_unsat_core_time:                   0.
% 1.71/0.99  
% 1.71/0.99  ------ QBF
% 1.71/0.99  
% 1.71/0.99  qbf_q_res:                              0
% 1.71/0.99  qbf_num_tautologies:                    0
% 1.71/0.99  qbf_prep_cycles:                        0
% 1.71/0.99  
% 1.71/0.99  ------ BMC1
% 1.71/0.99  
% 1.71/0.99  bmc1_current_bound:                     -1
% 1.71/0.99  bmc1_last_solved_bound:                 -1
% 1.71/0.99  bmc1_unsat_core_size:                   -1
% 1.71/0.99  bmc1_unsat_core_parents_size:           -1
% 1.71/0.99  bmc1_merge_next_fun:                    0
% 1.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation
% 1.71/0.99  
% 1.71/0.99  inst_num_of_clauses:                    271
% 1.71/0.99  inst_num_in_passive:                    12
% 1.71/0.99  inst_num_in_active:                     153
% 1.71/0.99  inst_num_in_unprocessed:                109
% 1.71/0.99  inst_num_of_loops:                      180
% 1.71/0.99  inst_num_of_learning_restarts:          0
% 1.71/0.99  inst_num_moves_active_passive:          25
% 1.71/0.99  inst_lit_activity:                      0
% 1.71/0.99  inst_lit_activity_moves:                0
% 1.71/0.99  inst_num_tautologies:                   0
% 1.71/0.99  inst_num_prop_implied:                  0
% 1.71/0.99  inst_num_existing_simplified:           0
% 1.71/0.99  inst_num_eq_res_simplified:             0
% 1.71/0.99  inst_num_child_elim:                    0
% 1.71/0.99  inst_num_of_dismatching_blockings:      87
% 1.71/0.99  inst_num_of_non_proper_insts:           294
% 1.71/0.99  inst_num_of_duplicates:                 0
% 1.71/0.99  inst_inst_num_from_inst_to_res:         0
% 1.71/0.99  inst_dismatching_checking_time:         0.
% 1.71/0.99  
% 1.71/0.99  ------ Resolution
% 1.71/0.99  
% 1.71/0.99  res_num_of_clauses:                     0
% 1.71/0.99  res_num_in_passive:                     0
% 1.71/0.99  res_num_in_active:                      0
% 1.71/0.99  res_num_of_loops:                       50
% 1.71/0.99  res_forward_subset_subsumed:            31
% 1.71/0.99  res_backward_subset_subsumed:           8
% 1.71/0.99  res_forward_subsumed:                   0
% 1.71/0.99  res_backward_subsumed:                  0
% 1.71/0.99  res_forward_subsumption_resolution:     0
% 1.71/0.99  res_backward_subsumption_resolution:    0
% 1.71/0.99  res_clause_to_clause_subsumption:       120
% 1.71/0.99  res_orphan_elimination:                 0
% 1.71/0.99  res_tautology_del:                      47
% 1.71/0.99  res_num_eq_res_simplified:              0
% 1.71/0.99  res_num_sel_changes:                    0
% 1.71/0.99  res_moves_from_active_to_pass:          0
% 1.71/0.99  
% 1.71/0.99  ------ Superposition
% 1.71/0.99  
% 1.71/0.99  sup_time_total:                         0.
% 1.71/0.99  sup_time_generating:                    0.
% 1.71/0.99  sup_time_sim_full:                      0.
% 1.71/0.99  sup_time_sim_immed:                     0.
% 1.71/0.99  
% 1.71/0.99  sup_num_of_clauses:                     47
% 1.71/0.99  sup_num_in_active:                      36
% 1.71/0.99  sup_num_in_passive:                     11
% 1.71/0.99  sup_num_of_loops:                       35
% 1.71/0.99  sup_fw_superposition:                   25
% 1.71/0.99  sup_bw_superposition:                   52
% 1.71/0.99  sup_immediate_simplified:               9
% 1.71/0.99  sup_given_eliminated:                   0
% 1.71/0.99  comparisons_done:                       0
% 1.71/0.99  comparisons_avoided:                    9
% 1.71/0.99  
% 1.71/0.99  ------ Simplifications
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  sim_fw_subset_subsumed:                 5
% 1.71/0.99  sim_bw_subset_subsumed:                 1
% 1.71/0.99  sim_fw_subsumed:                        1
% 1.71/0.99  sim_bw_subsumed:                        0
% 1.71/0.99  sim_fw_subsumption_res:                 0
% 1.71/0.99  sim_bw_subsumption_res:                 0
% 1.71/0.99  sim_tautology_del:                      0
% 1.71/0.99  sim_eq_tautology_del:                   11
% 1.71/0.99  sim_eq_res_simp:                        0
% 1.71/0.99  sim_fw_demodulated:                     0
% 1.71/0.99  sim_bw_demodulated:                     0
% 1.71/0.99  sim_light_normalised:                   2
% 1.71/0.99  sim_joinable_taut:                      0
% 1.71/0.99  sim_joinable_simp:                      0
% 1.71/0.99  sim_ac_normalised:                      0
% 1.71/0.99  sim_smt_subsumption:                    0
% 1.71/0.99  
%------------------------------------------------------------------------------
