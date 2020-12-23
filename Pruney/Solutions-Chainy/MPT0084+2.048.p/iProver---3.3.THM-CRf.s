%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:20 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 598 expanded)
%              Number of clauses        :   90 ( 199 expanded)
%              Number of leaves         :   18 ( 168 expanded)
%              Depth                    :   21
%              Number of atoms          :  220 ( 783 expanded)
%              Number of equality atoms :  131 ( 550 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))
      & r1_tarski(sK2,sK4)
      & ~ r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))
    & r1_tarski(sK2,sK4)
    & ~ r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f25])).

fof(f40,plain,(
    r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f36,f35,f35])).

fof(f41,plain,(
    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f23])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f21])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f37,f35,f35,f35])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_284,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_6])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_268,plain,
    ( r1_tarski(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_271,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_768,plain,
    ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_268,c_271])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24845,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_768,c_8])).

cnf(c_24909,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_24845,c_6])).

cnf(c_30276,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK4,X0),X1))) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_24909,c_8])).

cnf(c_50261,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK4,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_284,c_30276])).

cnf(c_51419,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK4,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50261,c_6,c_284])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_269,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_275,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_852,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_269,c_275])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_272,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_274,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1846,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_272,c_274])).

cnf(c_83316,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_852,c_1846])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_428,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_7,c_9])).

cnf(c_387,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_7100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_428,c_387])).

cnf(c_7161,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_7100,c_9])).

cnf(c_83388,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_83316,c_9,c_7161])).

cnf(c_684,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_284,c_8])).

cnf(c_1110,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_684,c_7])).

cnf(c_1141,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1110,c_6])).

cnf(c_1445,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1141])).

cnf(c_83497,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,k1_xboole_0)))) = sK3 ),
    inference(superposition,[status(thm)],[c_83388,c_1445])).

cnf(c_83554,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_83497,c_6])).

cnf(c_444,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_8794,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_444,c_7])).

cnf(c_8906,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8794,c_7])).

cnf(c_83786,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))) = k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_83554,c_8906])).

cnf(c_83876,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_83786,c_6,c_284])).

cnf(c_98087,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK4,sK2))) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_51419,c_83876])).

cnf(c_24842,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,k1_xboole_0))) = sK2 ),
    inference(superposition,[status(thm)],[c_768,c_1141])).

cnf(c_24920,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK4,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_24842,c_6])).

cnf(c_98465,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_98087,c_24920])).

cnf(c_98466,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_98465,c_6])).

cnf(c_7136,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1141,c_7100])).

cnf(c_7273,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7136,c_284])).

cnf(c_7274,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7273,c_6])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_273,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1460,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,X0)) = iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_273])).

cnf(c_1511,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1460,c_284])).

cnf(c_1109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_684,c_8])).

cnf(c_2445,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_284,c_1109])).

cnf(c_2736,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2445,c_6,c_284])).

cnf(c_24821,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK4,k4_xboole_0(sK2,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_768,c_2736])).

cnf(c_24978,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24821,c_6])).

cnf(c_25386,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24978,c_274])).

cnf(c_25520,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25386,c_6])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_270,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_851,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_270,c_275])).

cnf(c_39713,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25520,c_851])).

cnf(c_58904,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1511,c_39713])).

cnf(c_59003,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7274,c_58904])).

cnf(c_59214,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_59003,c_6,c_284])).

cnf(c_98916,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_98466,c_59214])).

cnf(c_99047,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,X0),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_98916,c_6,c_284])).

cnf(c_99187,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_99047])).

cnf(c_40338,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK2)
    | r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_40339,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK2) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40338])).

cnf(c_94,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_374,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_542,plain,
    ( ~ r1_xboole_0(sK2,X0)
    | r1_xboole_0(sK2,sK3)
    | sK3 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_30633,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0))
    | r1_xboole_0(sK2,sK3)
    | sK3 != k4_xboole_0(sK3,k1_xboole_0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_30634,plain,
    ( sK3 != k4_xboole_0(sK3,k1_xboole_0)
    | sK2 != sK2
    | r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0)) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30633])).

cnf(c_1620,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_93,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_608,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_753,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1619,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) != sK3
    | sK3 = k4_xboole_0(sK3,k1_xboole_0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_92,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_617,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_543,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,plain,
    ( r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99187,c_40339,c_30634,c_1620,c_1619,c_617,c_543,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.77/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.77/2.99  
% 19.77/2.99  ------  iProver source info
% 19.77/2.99  
% 19.77/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.77/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.77/2.99  git: non_committed_changes: false
% 19.77/2.99  git: last_make_outside_of_git: false
% 19.77/2.99  
% 19.77/2.99  ------ 
% 19.77/2.99  
% 19.77/2.99  ------ Input Options
% 19.77/2.99  
% 19.77/2.99  --out_options                           all
% 19.77/2.99  --tptp_safe_out                         true
% 19.77/2.99  --problem_path                          ""
% 19.77/2.99  --include_path                          ""
% 19.77/2.99  --clausifier                            res/vclausify_rel
% 19.77/2.99  --clausifier_options                    --mode clausify
% 19.77/2.99  --stdin                                 false
% 19.77/2.99  --stats_out                             sel
% 19.77/2.99  
% 19.77/2.99  ------ General Options
% 19.77/2.99  
% 19.77/2.99  --fof                                   false
% 19.77/2.99  --time_out_real                         604.99
% 19.77/2.99  --time_out_virtual                      -1.
% 19.77/2.99  --symbol_type_check                     false
% 19.77/2.99  --clausify_out                          false
% 19.77/2.99  --sig_cnt_out                           false
% 19.77/2.99  --trig_cnt_out                          false
% 19.77/2.99  --trig_cnt_out_tolerance                1.
% 19.77/2.99  --trig_cnt_out_sk_spl                   false
% 19.77/2.99  --abstr_cl_out                          false
% 19.77/2.99  
% 19.77/2.99  ------ Global Options
% 19.77/2.99  
% 19.77/2.99  --schedule                              none
% 19.77/2.99  --add_important_lit                     false
% 19.77/2.99  --prop_solver_per_cl                    1000
% 19.77/2.99  --min_unsat_core                        false
% 19.77/2.99  --soft_assumptions                      false
% 19.77/2.99  --soft_lemma_size                       3
% 19.77/2.99  --prop_impl_unit_size                   0
% 19.77/2.99  --prop_impl_unit                        []
% 19.77/2.99  --share_sel_clauses                     true
% 19.77/2.99  --reset_solvers                         false
% 19.77/2.99  --bc_imp_inh                            [conj_cone]
% 19.77/2.99  --conj_cone_tolerance                   3.
% 19.77/2.99  --extra_neg_conj                        none
% 19.77/2.99  --large_theory_mode                     true
% 19.77/2.99  --prolific_symb_bound                   200
% 19.77/2.99  --lt_threshold                          2000
% 19.77/2.99  --clause_weak_htbl                      true
% 19.77/2.99  --gc_record_bc_elim                     false
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing Options
% 19.77/2.99  
% 19.77/2.99  --preprocessing_flag                    true
% 19.77/2.99  --time_out_prep_mult                    0.1
% 19.77/2.99  --splitting_mode                        input
% 19.77/2.99  --splitting_grd                         true
% 19.77/2.99  --splitting_cvd                         false
% 19.77/2.99  --splitting_cvd_svl                     false
% 19.77/2.99  --splitting_nvd                         32
% 19.77/2.99  --sub_typing                            true
% 19.77/2.99  --prep_gs_sim                           false
% 19.77/2.99  --prep_unflatten                        true
% 19.77/2.99  --prep_res_sim                          true
% 19.77/2.99  --prep_upred                            true
% 19.77/2.99  --prep_sem_filter                       exhaustive
% 19.77/2.99  --prep_sem_filter_out                   false
% 19.77/2.99  --pred_elim                             false
% 19.77/2.99  --res_sim_input                         true
% 19.77/2.99  --eq_ax_congr_red                       true
% 19.77/2.99  --pure_diseq_elim                       true
% 19.77/2.99  --brand_transform                       false
% 19.77/2.99  --non_eq_to_eq                          false
% 19.77/2.99  --prep_def_merge                        true
% 19.77/2.99  --prep_def_merge_prop_impl              false
% 19.77/2.99  --prep_def_merge_mbd                    true
% 19.77/2.99  --prep_def_merge_tr_red                 false
% 19.77/2.99  --prep_def_merge_tr_cl                  false
% 19.77/2.99  --smt_preprocessing                     true
% 19.77/2.99  --smt_ac_axioms                         fast
% 19.77/2.99  --preprocessed_out                      false
% 19.77/2.99  --preprocessed_stats                    false
% 19.77/2.99  
% 19.77/2.99  ------ Abstraction refinement Options
% 19.77/2.99  
% 19.77/2.99  --abstr_ref                             []
% 19.77/2.99  --abstr_ref_prep                        false
% 19.77/2.99  --abstr_ref_until_sat                   false
% 19.77/2.99  --abstr_ref_sig_restrict                funpre
% 19.77/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/2.99  --abstr_ref_under                       []
% 19.77/2.99  
% 19.77/2.99  ------ SAT Options
% 19.77/2.99  
% 19.77/2.99  --sat_mode                              false
% 19.77/2.99  --sat_fm_restart_options                ""
% 19.77/2.99  --sat_gr_def                            false
% 19.77/2.99  --sat_epr_types                         true
% 19.77/2.99  --sat_non_cyclic_types                  false
% 19.77/2.99  --sat_finite_models                     false
% 19.77/2.99  --sat_fm_lemmas                         false
% 19.77/2.99  --sat_fm_prep                           false
% 19.77/2.99  --sat_fm_uc_incr                        true
% 19.77/2.99  --sat_out_model                         small
% 19.77/2.99  --sat_out_clauses                       false
% 19.77/2.99  
% 19.77/2.99  ------ QBF Options
% 19.77/2.99  
% 19.77/2.99  --qbf_mode                              false
% 19.77/2.99  --qbf_elim_univ                         false
% 19.77/2.99  --qbf_dom_inst                          none
% 19.77/2.99  --qbf_dom_pre_inst                      false
% 19.77/2.99  --qbf_sk_in                             false
% 19.77/2.99  --qbf_pred_elim                         true
% 19.77/2.99  --qbf_split                             512
% 19.77/2.99  
% 19.77/2.99  ------ BMC1 Options
% 19.77/2.99  
% 19.77/2.99  --bmc1_incremental                      false
% 19.77/2.99  --bmc1_axioms                           reachable_all
% 19.77/2.99  --bmc1_min_bound                        0
% 19.77/2.99  --bmc1_max_bound                        -1
% 19.77/2.99  --bmc1_max_bound_default                -1
% 19.77/2.99  --bmc1_symbol_reachability              true
% 19.77/2.99  --bmc1_property_lemmas                  false
% 19.77/2.99  --bmc1_k_induction                      false
% 19.77/2.99  --bmc1_non_equiv_states                 false
% 19.77/2.99  --bmc1_deadlock                         false
% 19.77/2.99  --bmc1_ucm                              false
% 19.77/2.99  --bmc1_add_unsat_core                   none
% 19.77/2.99  --bmc1_unsat_core_children              false
% 19.77/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/2.99  --bmc1_out_stat                         full
% 19.77/2.99  --bmc1_ground_init                      false
% 19.77/2.99  --bmc1_pre_inst_next_state              false
% 19.77/2.99  --bmc1_pre_inst_state                   false
% 19.77/2.99  --bmc1_pre_inst_reach_state             false
% 19.77/2.99  --bmc1_out_unsat_core                   false
% 19.77/2.99  --bmc1_aig_witness_out                  false
% 19.77/2.99  --bmc1_verbose                          false
% 19.77/2.99  --bmc1_dump_clauses_tptp                false
% 19.77/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.77/2.99  --bmc1_dump_file                        -
% 19.77/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.77/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.77/2.99  --bmc1_ucm_extend_mode                  1
% 19.77/2.99  --bmc1_ucm_init_mode                    2
% 19.77/2.99  --bmc1_ucm_cone_mode                    none
% 19.77/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.77/2.99  --bmc1_ucm_relax_model                  4
% 19.77/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.77/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/2.99  --bmc1_ucm_layered_model                none
% 19.77/2.99  --bmc1_ucm_max_lemma_size               10
% 19.77/2.99  
% 19.77/2.99  ------ AIG Options
% 19.77/2.99  
% 19.77/2.99  --aig_mode                              false
% 19.77/2.99  
% 19.77/2.99  ------ Instantiation Options
% 19.77/2.99  
% 19.77/2.99  --instantiation_flag                    true
% 19.77/2.99  --inst_sos_flag                         false
% 19.77/2.99  --inst_sos_phase                        true
% 19.77/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel_side                     num_symb
% 19.77/2.99  --inst_solver_per_active                1400
% 19.77/2.99  --inst_solver_calls_frac                1.
% 19.77/2.99  --inst_passive_queue_type               priority_queues
% 19.77/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/2.99  --inst_passive_queues_freq              [25;2]
% 19.77/2.99  --inst_dismatching                      true
% 19.77/2.99  --inst_eager_unprocessed_to_passive     true
% 19.77/2.99  --inst_prop_sim_given                   true
% 19.77/2.99  --inst_prop_sim_new                     false
% 19.77/2.99  --inst_subs_new                         false
% 19.77/2.99  --inst_eq_res_simp                      false
% 19.77/2.99  --inst_subs_given                       false
% 19.77/2.99  --inst_orphan_elimination               true
% 19.77/2.99  --inst_learning_loop_flag               true
% 19.77/2.99  --inst_learning_start                   3000
% 19.77/2.99  --inst_learning_factor                  2
% 19.77/2.99  --inst_start_prop_sim_after_learn       3
% 19.77/2.99  --inst_sel_renew                        solver
% 19.77/2.99  --inst_lit_activity_flag                true
% 19.77/2.99  --inst_restr_to_given                   false
% 19.77/2.99  --inst_activity_threshold               500
% 19.77/2.99  --inst_out_proof                        true
% 19.77/2.99  
% 19.77/2.99  ------ Resolution Options
% 19.77/2.99  
% 19.77/2.99  --resolution_flag                       true
% 19.77/2.99  --res_lit_sel                           adaptive
% 19.77/2.99  --res_lit_sel_side                      none
% 19.77/2.99  --res_ordering                          kbo
% 19.77/2.99  --res_to_prop_solver                    active
% 19.77/2.99  --res_prop_simpl_new                    false
% 19.77/2.99  --res_prop_simpl_given                  true
% 19.77/2.99  --res_passive_queue_type                priority_queues
% 19.77/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/2.99  --res_passive_queues_freq               [15;5]
% 19.77/2.99  --res_forward_subs                      full
% 19.77/2.99  --res_backward_subs                     full
% 19.77/2.99  --res_forward_subs_resolution           true
% 19.77/2.99  --res_backward_subs_resolution          true
% 19.77/2.99  --res_orphan_elimination                true
% 19.77/2.99  --res_time_limit                        2.
% 19.77/2.99  --res_out_proof                         true
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Options
% 19.77/2.99  
% 19.77/2.99  --superposition_flag                    true
% 19.77/2.99  --sup_passive_queue_type                priority_queues
% 19.77/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/2.99  --sup_passive_queues_freq               [1;4]
% 19.77/2.99  --demod_completeness_check              fast
% 19.77/2.99  --demod_use_ground                      true
% 19.77/2.99  --sup_to_prop_solver                    passive
% 19.77/2.99  --sup_prop_simpl_new                    true
% 19.77/2.99  --sup_prop_simpl_given                  true
% 19.77/2.99  --sup_fun_splitting                     false
% 19.77/2.99  --sup_smt_interval                      50000
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Simplification Setup
% 19.77/2.99  
% 19.77/2.99  --sup_indices_passive                   []
% 19.77/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_full_bw                           [BwDemod]
% 19.77/2.99  --sup_immed_triv                        [TrivRules]
% 19.77/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_immed_bw_main                     []
% 19.77/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  
% 19.77/2.99  ------ Combination Options
% 19.77/2.99  
% 19.77/2.99  --comb_res_mult                         3
% 19.77/2.99  --comb_sup_mult                         2
% 19.77/2.99  --comb_inst_mult                        10
% 19.77/2.99  
% 19.77/2.99  ------ Debug Options
% 19.77/2.99  
% 19.77/2.99  --dbg_backtrace                         false
% 19.77/2.99  --dbg_dump_prop_clauses                 false
% 19.77/2.99  --dbg_dump_prop_clauses_file            -
% 19.77/2.99  --dbg_out_stat                          false
% 19.77/2.99  ------ Parsing...
% 19.77/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.77/2.99  ------ Proving...
% 19.77/2.99  ------ Problem Properties 
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  clauses                                 14
% 19.77/2.99  conjectures                             3
% 19.77/2.99  EPR                                     4
% 19.77/2.99  Horn                                    12
% 19.77/2.99  unary                                   9
% 19.77/2.99  binary                                  5
% 19.77/2.99  lits                                    19
% 19.77/2.99  lits eq                                 7
% 19.77/2.99  fd_pure                                 0
% 19.77/2.99  fd_pseudo                               0
% 19.77/2.99  fd_cond                                 1
% 19.77/2.99  fd_pseudo_cond                          0
% 19.77/2.99  AC symbols                              0
% 19.77/2.99  
% 19.77/2.99  ------ Input Options Time Limit: Unbounded
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  ------ 
% 19.77/2.99  Current options:
% 19.77/2.99  ------ 
% 19.77/2.99  
% 19.77/2.99  ------ Input Options
% 19.77/2.99  
% 19.77/2.99  --out_options                           all
% 19.77/2.99  --tptp_safe_out                         true
% 19.77/2.99  --problem_path                          ""
% 19.77/2.99  --include_path                          ""
% 19.77/2.99  --clausifier                            res/vclausify_rel
% 19.77/2.99  --clausifier_options                    --mode clausify
% 19.77/2.99  --stdin                                 false
% 19.77/2.99  --stats_out                             sel
% 19.77/2.99  
% 19.77/2.99  ------ General Options
% 19.77/2.99  
% 19.77/2.99  --fof                                   false
% 19.77/2.99  --time_out_real                         604.99
% 19.77/2.99  --time_out_virtual                      -1.
% 19.77/2.99  --symbol_type_check                     false
% 19.77/2.99  --clausify_out                          false
% 19.77/2.99  --sig_cnt_out                           false
% 19.77/2.99  --trig_cnt_out                          false
% 19.77/2.99  --trig_cnt_out_tolerance                1.
% 19.77/2.99  --trig_cnt_out_sk_spl                   false
% 19.77/2.99  --abstr_cl_out                          false
% 19.77/2.99  
% 19.77/2.99  ------ Global Options
% 19.77/2.99  
% 19.77/2.99  --schedule                              none
% 19.77/2.99  --add_important_lit                     false
% 19.77/2.99  --prop_solver_per_cl                    1000
% 19.77/2.99  --min_unsat_core                        false
% 19.77/2.99  --soft_assumptions                      false
% 19.77/2.99  --soft_lemma_size                       3
% 19.77/2.99  --prop_impl_unit_size                   0
% 19.77/2.99  --prop_impl_unit                        []
% 19.77/2.99  --share_sel_clauses                     true
% 19.77/2.99  --reset_solvers                         false
% 19.77/2.99  --bc_imp_inh                            [conj_cone]
% 19.77/2.99  --conj_cone_tolerance                   3.
% 19.77/2.99  --extra_neg_conj                        none
% 19.77/2.99  --large_theory_mode                     true
% 19.77/2.99  --prolific_symb_bound                   200
% 19.77/2.99  --lt_threshold                          2000
% 19.77/2.99  --clause_weak_htbl                      true
% 19.77/2.99  --gc_record_bc_elim                     false
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing Options
% 19.77/2.99  
% 19.77/2.99  --preprocessing_flag                    true
% 19.77/2.99  --time_out_prep_mult                    0.1
% 19.77/2.99  --splitting_mode                        input
% 19.77/2.99  --splitting_grd                         true
% 19.77/2.99  --splitting_cvd                         false
% 19.77/2.99  --splitting_cvd_svl                     false
% 19.77/2.99  --splitting_nvd                         32
% 19.77/2.99  --sub_typing                            true
% 19.77/2.99  --prep_gs_sim                           false
% 19.77/2.99  --prep_unflatten                        true
% 19.77/2.99  --prep_res_sim                          true
% 19.77/2.99  --prep_upred                            true
% 19.77/2.99  --prep_sem_filter                       exhaustive
% 19.77/2.99  --prep_sem_filter_out                   false
% 19.77/2.99  --pred_elim                             false
% 19.77/2.99  --res_sim_input                         true
% 19.77/2.99  --eq_ax_congr_red                       true
% 19.77/2.99  --pure_diseq_elim                       true
% 19.77/2.99  --brand_transform                       false
% 19.77/2.99  --non_eq_to_eq                          false
% 19.77/2.99  --prep_def_merge                        true
% 19.77/2.99  --prep_def_merge_prop_impl              false
% 19.77/2.99  --prep_def_merge_mbd                    true
% 19.77/2.99  --prep_def_merge_tr_red                 false
% 19.77/2.99  --prep_def_merge_tr_cl                  false
% 19.77/2.99  --smt_preprocessing                     true
% 19.77/2.99  --smt_ac_axioms                         fast
% 19.77/2.99  --preprocessed_out                      false
% 19.77/2.99  --preprocessed_stats                    false
% 19.77/2.99  
% 19.77/2.99  ------ Abstraction refinement Options
% 19.77/2.99  
% 19.77/2.99  --abstr_ref                             []
% 19.77/2.99  --abstr_ref_prep                        false
% 19.77/2.99  --abstr_ref_until_sat                   false
% 19.77/2.99  --abstr_ref_sig_restrict                funpre
% 19.77/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/2.99  --abstr_ref_under                       []
% 19.77/2.99  
% 19.77/2.99  ------ SAT Options
% 19.77/2.99  
% 19.77/2.99  --sat_mode                              false
% 19.77/2.99  --sat_fm_restart_options                ""
% 19.77/2.99  --sat_gr_def                            false
% 19.77/2.99  --sat_epr_types                         true
% 19.77/2.99  --sat_non_cyclic_types                  false
% 19.77/2.99  --sat_finite_models                     false
% 19.77/2.99  --sat_fm_lemmas                         false
% 19.77/2.99  --sat_fm_prep                           false
% 19.77/2.99  --sat_fm_uc_incr                        true
% 19.77/2.99  --sat_out_model                         small
% 19.77/2.99  --sat_out_clauses                       false
% 19.77/2.99  
% 19.77/2.99  ------ QBF Options
% 19.77/2.99  
% 19.77/2.99  --qbf_mode                              false
% 19.77/2.99  --qbf_elim_univ                         false
% 19.77/2.99  --qbf_dom_inst                          none
% 19.77/2.99  --qbf_dom_pre_inst                      false
% 19.77/2.99  --qbf_sk_in                             false
% 19.77/2.99  --qbf_pred_elim                         true
% 19.77/2.99  --qbf_split                             512
% 19.77/2.99  
% 19.77/2.99  ------ BMC1 Options
% 19.77/2.99  
% 19.77/2.99  --bmc1_incremental                      false
% 19.77/2.99  --bmc1_axioms                           reachable_all
% 19.77/2.99  --bmc1_min_bound                        0
% 19.77/2.99  --bmc1_max_bound                        -1
% 19.77/2.99  --bmc1_max_bound_default                -1
% 19.77/2.99  --bmc1_symbol_reachability              true
% 19.77/2.99  --bmc1_property_lemmas                  false
% 19.77/2.99  --bmc1_k_induction                      false
% 19.77/2.99  --bmc1_non_equiv_states                 false
% 19.77/2.99  --bmc1_deadlock                         false
% 19.77/2.99  --bmc1_ucm                              false
% 19.77/2.99  --bmc1_add_unsat_core                   none
% 19.77/2.99  --bmc1_unsat_core_children              false
% 19.77/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/2.99  --bmc1_out_stat                         full
% 19.77/2.99  --bmc1_ground_init                      false
% 19.77/2.99  --bmc1_pre_inst_next_state              false
% 19.77/2.99  --bmc1_pre_inst_state                   false
% 19.77/2.99  --bmc1_pre_inst_reach_state             false
% 19.77/2.99  --bmc1_out_unsat_core                   false
% 19.77/2.99  --bmc1_aig_witness_out                  false
% 19.77/2.99  --bmc1_verbose                          false
% 19.77/2.99  --bmc1_dump_clauses_tptp                false
% 19.77/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.77/2.99  --bmc1_dump_file                        -
% 19.77/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.77/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.77/2.99  --bmc1_ucm_extend_mode                  1
% 19.77/2.99  --bmc1_ucm_init_mode                    2
% 19.77/2.99  --bmc1_ucm_cone_mode                    none
% 19.77/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.77/2.99  --bmc1_ucm_relax_model                  4
% 19.77/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.77/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/2.99  --bmc1_ucm_layered_model                none
% 19.77/2.99  --bmc1_ucm_max_lemma_size               10
% 19.77/2.99  
% 19.77/2.99  ------ AIG Options
% 19.77/2.99  
% 19.77/2.99  --aig_mode                              false
% 19.77/2.99  
% 19.77/2.99  ------ Instantiation Options
% 19.77/2.99  
% 19.77/2.99  --instantiation_flag                    true
% 19.77/2.99  --inst_sos_flag                         false
% 19.77/2.99  --inst_sos_phase                        true
% 19.77/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel_side                     num_symb
% 19.77/2.99  --inst_solver_per_active                1400
% 19.77/2.99  --inst_solver_calls_frac                1.
% 19.77/2.99  --inst_passive_queue_type               priority_queues
% 19.77/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/2.99  --inst_passive_queues_freq              [25;2]
% 19.77/2.99  --inst_dismatching                      true
% 19.77/2.99  --inst_eager_unprocessed_to_passive     true
% 19.77/2.99  --inst_prop_sim_given                   true
% 19.77/2.99  --inst_prop_sim_new                     false
% 19.77/2.99  --inst_subs_new                         false
% 19.77/2.99  --inst_eq_res_simp                      false
% 19.77/2.99  --inst_subs_given                       false
% 19.77/2.99  --inst_orphan_elimination               true
% 19.77/2.99  --inst_learning_loop_flag               true
% 19.77/2.99  --inst_learning_start                   3000
% 19.77/2.99  --inst_learning_factor                  2
% 19.77/2.99  --inst_start_prop_sim_after_learn       3
% 19.77/2.99  --inst_sel_renew                        solver
% 19.77/2.99  --inst_lit_activity_flag                true
% 19.77/2.99  --inst_restr_to_given                   false
% 19.77/2.99  --inst_activity_threshold               500
% 19.77/2.99  --inst_out_proof                        true
% 19.77/2.99  
% 19.77/2.99  ------ Resolution Options
% 19.77/2.99  
% 19.77/2.99  --resolution_flag                       true
% 19.77/2.99  --res_lit_sel                           adaptive
% 19.77/2.99  --res_lit_sel_side                      none
% 19.77/2.99  --res_ordering                          kbo
% 19.77/2.99  --res_to_prop_solver                    active
% 19.77/2.99  --res_prop_simpl_new                    false
% 19.77/2.99  --res_prop_simpl_given                  true
% 19.77/2.99  --res_passive_queue_type                priority_queues
% 19.77/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/2.99  --res_passive_queues_freq               [15;5]
% 19.77/2.99  --res_forward_subs                      full
% 19.77/2.99  --res_backward_subs                     full
% 19.77/2.99  --res_forward_subs_resolution           true
% 19.77/2.99  --res_backward_subs_resolution          true
% 19.77/2.99  --res_orphan_elimination                true
% 19.77/2.99  --res_time_limit                        2.
% 19.77/2.99  --res_out_proof                         true
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Options
% 19.77/2.99  
% 19.77/2.99  --superposition_flag                    true
% 19.77/2.99  --sup_passive_queue_type                priority_queues
% 19.77/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/2.99  --sup_passive_queues_freq               [1;4]
% 19.77/2.99  --demod_completeness_check              fast
% 19.77/2.99  --demod_use_ground                      true
% 19.77/2.99  --sup_to_prop_solver                    passive
% 19.77/2.99  --sup_prop_simpl_new                    true
% 19.77/2.99  --sup_prop_simpl_given                  true
% 19.77/2.99  --sup_fun_splitting                     false
% 19.77/2.99  --sup_smt_interval                      50000
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Simplification Setup
% 19.77/2.99  
% 19.77/2.99  --sup_indices_passive                   []
% 19.77/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_full_bw                           [BwDemod]
% 19.77/2.99  --sup_immed_triv                        [TrivRules]
% 19.77/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_immed_bw_main                     []
% 19.77/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  
% 19.77/2.99  ------ Combination Options
% 19.77/2.99  
% 19.77/2.99  --comb_res_mult                         3
% 19.77/2.99  --comb_sup_mult                         2
% 19.77/2.99  --comb_inst_mult                        10
% 19.77/2.99  
% 19.77/2.99  ------ Debug Options
% 19.77/2.99  
% 19.77/2.99  --dbg_backtrace                         false
% 19.77/2.99  --dbg_dump_prop_clauses                 false
% 19.77/2.99  --dbg_dump_prop_clauses_file            -
% 19.77/2.99  --dbg_out_stat                          false
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  ------ Proving...
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  % SZS status Theorem for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  fof(f5,axiom,(
% 19.77/2.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f32,plain,(
% 19.77/2.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.77/2.99    inference(cnf_transformation,[],[f5])).
% 19.77/2.99  
% 19.77/2.99  fof(f8,axiom,(
% 19.77/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f35,plain,(
% 19.77/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f8])).
% 19.77/2.99  
% 19.77/2.99  fof(f44,plain,(
% 19.77/2.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 19.77/2.99    inference(definition_unfolding,[],[f32,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f6,axiom,(
% 19.77/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f33,plain,(
% 19.77/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.77/2.99    inference(cnf_transformation,[],[f6])).
% 19.77/2.99  
% 19.77/2.99  fof(f12,conjecture,(
% 19.77/2.99    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f13,negated_conjecture,(
% 19.77/2.99    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 19.77/2.99    inference(negated_conjecture,[],[f12])).
% 19.77/2.99  
% 19.77/2.99  fof(f20,plain,(
% 19.77/2.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 19.77/2.99    inference(ennf_transformation,[],[f13])).
% 19.77/2.99  
% 19.77/2.99  fof(f25,plain,(
% 19.77/2.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) & r1_tarski(sK2,sK4) & ~r1_xboole_0(sK2,sK3))),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f26,plain,(
% 19.77/2.99    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) & r1_tarski(sK2,sK4) & ~r1_xboole_0(sK2,sK3)),
% 19.77/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f25])).
% 19.77/2.99  
% 19.77/2.99  fof(f40,plain,(
% 19.77/2.99    r1_tarski(sK2,sK4)),
% 19.77/2.99    inference(cnf_transformation,[],[f26])).
% 19.77/2.99  
% 19.77/2.99  fof(f4,axiom,(
% 19.77/2.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f15,plain,(
% 19.77/2.99    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 19.77/2.99    inference(unused_predicate_definition_removal,[],[f4])).
% 19.77/2.99  
% 19.77/2.99  fof(f19,plain,(
% 19.77/2.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 19.77/2.99    inference(ennf_transformation,[],[f15])).
% 19.77/2.99  
% 19.77/2.99  fof(f31,plain,(
% 19.77/2.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f19])).
% 19.77/2.99  
% 19.77/2.99  fof(f9,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f36,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f9])).
% 19.77/2.99  
% 19.77/2.99  fof(f46,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 19.77/2.99    inference(definition_unfolding,[],[f36,f35,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f41,plain,(
% 19.77/2.99    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))),
% 19.77/2.99    inference(cnf_transformation,[],[f26])).
% 19.77/2.99  
% 19.77/2.99  fof(f48,plain,(
% 19.77/2.99    r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))),
% 19.77/2.99    inference(definition_unfolding,[],[f41,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f1,axiom,(
% 19.77/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f16,plain,(
% 19.77/2.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.77/2.99    inference(ennf_transformation,[],[f1])).
% 19.77/2.99  
% 19.77/2.99  fof(f27,plain,(
% 19.77/2.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f16])).
% 19.77/2.99  
% 19.77/2.99  fof(f3,axiom,(
% 19.77/2.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f18,plain,(
% 19.77/2.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 19.77/2.99    inference(ennf_transformation,[],[f3])).
% 19.77/2.99  
% 19.77/2.99  fof(f23,plain,(
% 19.77/2.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f24,plain,(
% 19.77/2.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 19.77/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f23])).
% 19.77/2.99  
% 19.77/2.99  fof(f30,plain,(
% 19.77/2.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 19.77/2.99    inference(cnf_transformation,[],[f24])).
% 19.77/2.99  
% 19.77/2.99  fof(f2,axiom,(
% 19.77/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f14,plain,(
% 19.77/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.77/2.99    inference(rectify,[],[f2])).
% 19.77/2.99  
% 19.77/2.99  fof(f17,plain,(
% 19.77/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.77/2.99    inference(ennf_transformation,[],[f14])).
% 19.77/2.99  
% 19.77/2.99  fof(f21,plain,(
% 19.77/2.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f22,plain,(
% 19.77/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.77/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f21])).
% 19.77/2.99  
% 19.77/2.99  fof(f29,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f22])).
% 19.77/2.99  
% 19.77/2.99  fof(f42,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.77/2.99    inference(definition_unfolding,[],[f29,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f10,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f37,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f10])).
% 19.77/2.99  
% 19.77/2.99  fof(f47,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 19.77/2.99    inference(definition_unfolding,[],[f37,f35,f35,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f7,axiom,(
% 19.77/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f34,plain,(
% 19.77/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f7])).
% 19.77/2.99  
% 19.77/2.99  fof(f45,plain,(
% 19.77/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.77/2.99    inference(definition_unfolding,[],[f34,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f28,plain,(
% 19.77/2.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f22])).
% 19.77/2.99  
% 19.77/2.99  fof(f43,plain,(
% 19.77/2.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 19.77/2.99    inference(definition_unfolding,[],[f28,f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f11,axiom,(
% 19.77/2.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f38,plain,(
% 19.77/2.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f11])).
% 19.77/2.99  
% 19.77/2.99  fof(f39,plain,(
% 19.77/2.99    ~r1_xboole_0(sK2,sK3)),
% 19.77/2.99    inference(cnf_transformation,[],[f26])).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f33]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_284,plain,
% 19.77/2.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_5,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_12,negated_conjecture,
% 19.77/2.99      ( r1_tarski(sK2,sK4) ),
% 19.77/2.99      inference(cnf_transformation,[],[f40]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_268,plain,
% 19.77/2.99      ( r1_tarski(sK2,sK4) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_4,plain,
% 19.77/2.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f31]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_271,plain,
% 19.77/2.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 19.77/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_768,plain,
% 19.77/2.99      ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_268,c_271]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.77/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24845,plain,
% 19.77/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_768,c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24909,plain,
% 19.77/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k4_xboole_0(sK2,X0) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_24845,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_30276,plain,
% 19.77/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK4,X0),X1))) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_24909,c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_50261,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK4,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_284,c_30276]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51419,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK4,X0)) = k1_xboole_0 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_50261,c_6,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_11,negated_conjecture,
% 19.77/2.99      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
% 19.77/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_269,plain,
% 19.77/2.99      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_0,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f27]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_275,plain,
% 19.77/2.99      ( r1_xboole_0(X0,X1) != iProver_top
% 19.77/2.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_852,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),sK2) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_269,c_275]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3,plain,
% 19.77/2.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f30]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_272,plain,
% 19.77/2.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1,plain,
% 19.77/2.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.77/2.99      | ~ r1_xboole_0(X1,X2) ),
% 19.77/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_274,plain,
% 19.77/2.99      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 19.77/2.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1846,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 19.77/2.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_272,c_274]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_83316,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),sK2)) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_852,c_1846]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.77/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_428,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_7,c_9]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_387,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7100,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_428,c_387]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7161,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_7100,c_9]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_83388,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))) = k1_xboole_0 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_83316,c_9,c_7161]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_684,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_284,c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1110,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_684,c_7]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1141,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_1110,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1445,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))) = X0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_8,c_1141]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_83497,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,k1_xboole_0)))) = sK3 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_83388,c_1445]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_83554,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = sK3 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_83497,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_444,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8794,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_444,c_7]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8906,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_8794,c_7]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_83786,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))) = k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_83554,c_8906]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_83876,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))) = k4_xboole_0(sK3,X0) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_83786,c_6,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_98087,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK4,sK2))) = k4_xboole_0(sK3,k1_xboole_0) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_51419,c_83876]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24842,plain,
% 19.77/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,k1_xboole_0))) = sK2 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_768,c_1141]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24920,plain,
% 19.77/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK4,sK2)) = sK2 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_24842,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_98465,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK2) ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_98087,c_24920]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_98466,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_98465,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7136,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1141,c_7100]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7273,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_7136,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7274,plain,
% 19.77/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,X1) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_7273,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2,plain,
% 19.77/2.99      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 19.77/2.99      | r1_xboole_0(X0,X1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_273,plain,
% 19.77/2.99      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
% 19.77/2.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1460,plain,
% 19.77/2.99      ( r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,X0)) = iProver_top
% 19.77/2.99      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1141,c_273]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1511,plain,
% 19.77/2.99      ( r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k1_xboole_0) = iProver_top
% 19.77/2.99      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_1460,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1109,plain,
% 19.77/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2))) = k4_xboole_0(k1_xboole_0,X2) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_684,c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2445,plain,
% 19.77/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_284,c_1109]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2736,plain,
% 19.77/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_2445,c_6,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24821,plain,
% 19.77/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK4,k4_xboole_0(sK2,k1_xboole_0))) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_768,c_2736]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24978,plain,
% 19.77/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_24821,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_25386,plain,
% 19.77/2.99      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 19.77/2.99      | r1_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK2)) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_24978,c_274]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_25520,plain,
% 19.77/2.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 19.77/2.99      | r1_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK2)) != iProver_top ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_25386,c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_10,plain,
% 19.77/2.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_270,plain,
% 19.77/2.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_851,plain,
% 19.77/2.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_270,c_275]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_39713,plain,
% 19.77/2.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.77/2.99      inference(forward_subsumption_resolution,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_25520,c_851]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_58904,plain,
% 19.77/2.99      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
% 19.77/2.99      inference(forward_subsumption_resolution,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_1511,c_39713]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_59003,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_7274,c_58904]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_59214,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = iProver_top ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_59003,c_6,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_98916,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_98466,c_59214]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_99047,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(sK3,X0),sK2) = iProver_top ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_98916,c_6,c_284]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_99187,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK2) = iProver_top ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_99047]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_40338,plain,
% 19.77/2.99      ( ~ r1_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK2)
% 19.77/2.99      | r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0)) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_0]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_40339,plain,
% 19.77/2.99      ( r1_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK2) != iProver_top
% 19.77/2.99      | r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0)) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_40338]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_94,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.77/2.99      theory(equality) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_374,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0,X1)
% 19.77/2.99      | r1_xboole_0(sK2,sK3)
% 19.77/2.99      | sK3 != X1
% 19.77/2.99      | sK2 != X0 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_94]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_542,plain,
% 19.77/2.99      ( ~ r1_xboole_0(sK2,X0)
% 19.77/2.99      | r1_xboole_0(sK2,sK3)
% 19.77/2.99      | sK3 != X0
% 19.77/2.99      | sK2 != sK2 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_374]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_30633,plain,
% 19.77/2.99      ( ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0))
% 19.77/2.99      | r1_xboole_0(sK2,sK3)
% 19.77/2.99      | sK3 != k4_xboole_0(sK3,k1_xboole_0)
% 19.77/2.99      | sK2 != sK2 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_542]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_30634,plain,
% 19.77/2.99      ( sK3 != k4_xboole_0(sK3,k1_xboole_0)
% 19.77/2.99      | sK2 != sK2
% 19.77/2.99      | r1_xboole_0(sK2,k4_xboole_0(sK3,k1_xboole_0)) != iProver_top
% 19.77/2.99      | r1_xboole_0(sK2,sK3) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_30633]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1620,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_6]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_93,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_608,plain,
% 19.77/2.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_93]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_753,plain,
% 19.77/2.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_608]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1619,plain,
% 19.77/2.99      ( k4_xboole_0(sK3,k1_xboole_0) != sK3
% 19.77/2.99      | sK3 = k4_xboole_0(sK3,k1_xboole_0)
% 19.77/2.99      | sK3 != sK3 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_753]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_92,plain,( X0 = X0 ),theory(equality) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_617,plain,
% 19.77/2.99      ( sK3 = sK3 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_92]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_543,plain,
% 19.77/2.99      ( sK2 = sK2 ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_92]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_13,negated_conjecture,
% 19.77/2.99      ( ~ r1_xboole_0(sK2,sK3) ),
% 19.77/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_14,plain,
% 19.77/2.99      ( r1_xboole_0(sK2,sK3) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(contradiction,plain,
% 19.77/2.99      ( $false ),
% 19.77/2.99      inference(minisat,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_99187,c_40339,c_30634,c_1620,c_1619,c_617,c_543,c_14]) ).
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  ------                               Statistics
% 19.77/2.99  
% 19.77/2.99  ------ Selected
% 19.77/2.99  
% 19.77/2.99  total_time:                             2.349
% 19.77/2.99  
%------------------------------------------------------------------------------
