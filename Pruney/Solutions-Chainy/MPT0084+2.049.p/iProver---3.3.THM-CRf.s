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

% Result     : Theorem 16.09s
% Output     : CNFRefutation 16.09s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 227 expanded)
%              Number of clauses        :   58 (  78 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  187 ( 373 expanded)
%              Number of equality atoms :   90 ( 191 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))
      & r1_tarski(sK2,sK4)
      & ~ r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))
    & r1_tarski(sK2,sK4)
    & ~ r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f24])).

fof(f40,plain,(
    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f22])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
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
    inference(rectify,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f39,plain,(
    r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f36,f34,f34,f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f35,f34,f34])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_268,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_272,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_274,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1860,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_272,c_274])).

cnf(c_87522,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_268,c_1860])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_267,plain,
    ( r1_tarski(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_271,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1027,plain,
    ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_267,c_271])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_436,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5919,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_436,c_7])).

cnf(c_6013,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_5919,c_7])).

cnf(c_24137,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_1027,c_6013])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_270,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1026,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_270,c_271])).

cnf(c_22128,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1026,c_8])).

cnf(c_22490,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22128,c_7])).

cnf(c_22752,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_22490,c_6])).

cnf(c_24203,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_24137,c_6,c_22752])).

cnf(c_24923,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,sK4))) = k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_24203,c_6013])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_285,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_6])).

cnf(c_25029,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,sK4))) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_24923,c_6,c_285])).

cnf(c_87524,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_87522,c_25029])).

cnf(c_97,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_968,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK2,sK3),X2)
    | X1 != X2
    | X0 != sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_3174,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),X0)
    | r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),X1)
    | X1 != X0
    | k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) != sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_7170,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),X0)
    | r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != X0
    | k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) != sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3174])).

cnf(c_7172,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),k1_xboole_0)
    | r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) != sK0(sK2,sK3)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7170])).

cnf(c_94,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_586,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_1440,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_1441,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_944,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ r1_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_950,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_93,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_654,plain,
    ( sK0(sK2,sK3) = sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_523,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != sK0(sK2,sK3)
    | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_653,plain,
    ( r2_hidden(sK0(sK2,sK3),X0)
    | ~ r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK2,sK3) != sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_656,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK2,sK3),k1_xboole_0)
    | sK0(sK2,sK3) != sK0(sK2,sK3)
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_648,plain,
    ( k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) = sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_359,plain,
    ( r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_104,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_27,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87524,c_7172,c_1441,c_950,c_654,c_656,c_648,c_359,c_104,c_27,c_18,c_13])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 16.09/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.09/2.50  
% 16.09/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 16.09/2.50  
% 16.09/2.50  ------  iProver source info
% 16.09/2.50  
% 16.09/2.50  git: date: 2020-06-30 10:37:57 +0100
% 16.09/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 16.09/2.50  git: non_committed_changes: false
% 16.09/2.50  git: last_make_outside_of_git: false
% 16.09/2.50  
% 16.09/2.50  ------ 
% 16.09/2.50  
% 16.09/2.50  ------ Input Options
% 16.09/2.50  
% 16.09/2.50  --out_options                           all
% 16.09/2.50  --tptp_safe_out                         true
% 16.09/2.50  --problem_path                          ""
% 16.09/2.50  --include_path                          ""
% 16.09/2.50  --clausifier                            res/vclausify_rel
% 16.09/2.50  --clausifier_options                    --mode clausify
% 16.09/2.50  --stdin                                 false
% 16.09/2.50  --stats_out                             sel
% 16.09/2.50  
% 16.09/2.50  ------ General Options
% 16.09/2.50  
% 16.09/2.50  --fof                                   false
% 16.09/2.50  --time_out_real                         604.99
% 16.09/2.50  --time_out_virtual                      -1.
% 16.09/2.50  --symbol_type_check                     false
% 16.09/2.50  --clausify_out                          false
% 16.09/2.50  --sig_cnt_out                           false
% 16.09/2.50  --trig_cnt_out                          false
% 16.09/2.50  --trig_cnt_out_tolerance                1.
% 16.09/2.50  --trig_cnt_out_sk_spl                   false
% 16.09/2.50  --abstr_cl_out                          false
% 16.09/2.50  
% 16.09/2.50  ------ Global Options
% 16.09/2.50  
% 16.09/2.50  --schedule                              none
% 16.09/2.50  --add_important_lit                     false
% 16.09/2.50  --prop_solver_per_cl                    1000
% 16.09/2.50  --min_unsat_core                        false
% 16.09/2.50  --soft_assumptions                      false
% 16.09/2.50  --soft_lemma_size                       3
% 16.09/2.50  --prop_impl_unit_size                   0
% 16.09/2.50  --prop_impl_unit                        []
% 16.09/2.50  --share_sel_clauses                     true
% 16.09/2.50  --reset_solvers                         false
% 16.09/2.50  --bc_imp_inh                            [conj_cone]
% 16.09/2.50  --conj_cone_tolerance                   3.
% 16.09/2.50  --extra_neg_conj                        none
% 16.09/2.50  --large_theory_mode                     true
% 16.09/2.50  --prolific_symb_bound                   200
% 16.09/2.50  --lt_threshold                          2000
% 16.09/2.50  --clause_weak_htbl                      true
% 16.09/2.50  --gc_record_bc_elim                     false
% 16.09/2.50  
% 16.09/2.50  ------ Preprocessing Options
% 16.09/2.50  
% 16.09/2.50  --preprocessing_flag                    true
% 16.09/2.50  --time_out_prep_mult                    0.1
% 16.09/2.50  --splitting_mode                        input
% 16.09/2.50  --splitting_grd                         true
% 16.09/2.50  --splitting_cvd                         false
% 16.09/2.50  --splitting_cvd_svl                     false
% 16.09/2.50  --splitting_nvd                         32
% 16.09/2.50  --sub_typing                            true
% 16.09/2.50  --prep_gs_sim                           false
% 16.09/2.50  --prep_unflatten                        true
% 16.09/2.50  --prep_res_sim                          true
% 16.09/2.50  --prep_upred                            true
% 16.09/2.50  --prep_sem_filter                       exhaustive
% 16.09/2.50  --prep_sem_filter_out                   false
% 16.09/2.50  --pred_elim                             false
% 16.09/2.50  --res_sim_input                         true
% 16.09/2.50  --eq_ax_congr_red                       true
% 16.09/2.50  --pure_diseq_elim                       true
% 16.09/2.50  --brand_transform                       false
% 16.09/2.50  --non_eq_to_eq                          false
% 16.09/2.50  --prep_def_merge                        true
% 16.09/2.50  --prep_def_merge_prop_impl              false
% 16.09/2.50  --prep_def_merge_mbd                    true
% 16.09/2.50  --prep_def_merge_tr_red                 false
% 16.09/2.50  --prep_def_merge_tr_cl                  false
% 16.09/2.50  --smt_preprocessing                     true
% 16.09/2.50  --smt_ac_axioms                         fast
% 16.09/2.50  --preprocessed_out                      false
% 16.09/2.50  --preprocessed_stats                    false
% 16.09/2.50  
% 16.09/2.50  ------ Abstraction refinement Options
% 16.09/2.50  
% 16.09/2.50  --abstr_ref                             []
% 16.09/2.50  --abstr_ref_prep                        false
% 16.09/2.50  --abstr_ref_until_sat                   false
% 16.09/2.50  --abstr_ref_sig_restrict                funpre
% 16.09/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 16.09/2.50  --abstr_ref_under                       []
% 16.09/2.50  
% 16.09/2.50  ------ SAT Options
% 16.09/2.50  
% 16.09/2.50  --sat_mode                              false
% 16.09/2.50  --sat_fm_restart_options                ""
% 16.09/2.50  --sat_gr_def                            false
% 16.09/2.50  --sat_epr_types                         true
% 16.09/2.50  --sat_non_cyclic_types                  false
% 16.09/2.50  --sat_finite_models                     false
% 16.09/2.50  --sat_fm_lemmas                         false
% 16.09/2.50  --sat_fm_prep                           false
% 16.09/2.50  --sat_fm_uc_incr                        true
% 16.09/2.50  --sat_out_model                         small
% 16.09/2.50  --sat_out_clauses                       false
% 16.09/2.50  
% 16.09/2.50  ------ QBF Options
% 16.09/2.50  
% 16.09/2.50  --qbf_mode                              false
% 16.09/2.50  --qbf_elim_univ                         false
% 16.09/2.50  --qbf_dom_inst                          none
% 16.09/2.50  --qbf_dom_pre_inst                      false
% 16.09/2.50  --qbf_sk_in                             false
% 16.09/2.50  --qbf_pred_elim                         true
% 16.09/2.50  --qbf_split                             512
% 16.09/2.50  
% 16.09/2.50  ------ BMC1 Options
% 16.09/2.50  
% 16.09/2.50  --bmc1_incremental                      false
% 16.09/2.50  --bmc1_axioms                           reachable_all
% 16.09/2.50  --bmc1_min_bound                        0
% 16.09/2.50  --bmc1_max_bound                        -1
% 16.09/2.50  --bmc1_max_bound_default                -1
% 16.09/2.50  --bmc1_symbol_reachability              true
% 16.09/2.50  --bmc1_property_lemmas                  false
% 16.09/2.50  --bmc1_k_induction                      false
% 16.09/2.50  --bmc1_non_equiv_states                 false
% 16.09/2.50  --bmc1_deadlock                         false
% 16.09/2.50  --bmc1_ucm                              false
% 16.09/2.50  --bmc1_add_unsat_core                   none
% 16.09/2.50  --bmc1_unsat_core_children              false
% 16.09/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 16.09/2.50  --bmc1_out_stat                         full
% 16.09/2.50  --bmc1_ground_init                      false
% 16.09/2.50  --bmc1_pre_inst_next_state              false
% 16.09/2.50  --bmc1_pre_inst_state                   false
% 16.09/2.50  --bmc1_pre_inst_reach_state             false
% 16.09/2.50  --bmc1_out_unsat_core                   false
% 16.09/2.50  --bmc1_aig_witness_out                  false
% 16.09/2.50  --bmc1_verbose                          false
% 16.09/2.50  --bmc1_dump_clauses_tptp                false
% 16.09/2.50  --bmc1_dump_unsat_core_tptp             false
% 16.09/2.50  --bmc1_dump_file                        -
% 16.09/2.50  --bmc1_ucm_expand_uc_limit              128
% 16.09/2.50  --bmc1_ucm_n_expand_iterations          6
% 16.09/2.50  --bmc1_ucm_extend_mode                  1
% 16.09/2.50  --bmc1_ucm_init_mode                    2
% 16.09/2.50  --bmc1_ucm_cone_mode                    none
% 16.09/2.50  --bmc1_ucm_reduced_relation_type        0
% 16.09/2.50  --bmc1_ucm_relax_model                  4
% 16.09/2.50  --bmc1_ucm_full_tr_after_sat            true
% 16.09/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 16.09/2.50  --bmc1_ucm_layered_model                none
% 16.09/2.50  --bmc1_ucm_max_lemma_size               10
% 16.09/2.50  
% 16.09/2.50  ------ AIG Options
% 16.09/2.50  
% 16.09/2.50  --aig_mode                              false
% 16.09/2.50  
% 16.09/2.50  ------ Instantiation Options
% 16.09/2.50  
% 16.09/2.50  --instantiation_flag                    true
% 16.09/2.50  --inst_sos_flag                         false
% 16.09/2.50  --inst_sos_phase                        true
% 16.09/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 16.09/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 16.09/2.50  --inst_lit_sel_side                     num_symb
% 16.09/2.50  --inst_solver_per_active                1400
% 16.09/2.50  --inst_solver_calls_frac                1.
% 16.09/2.50  --inst_passive_queue_type               priority_queues
% 16.09/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 16.09/2.50  --inst_passive_queues_freq              [25;2]
% 16.09/2.50  --inst_dismatching                      true
% 16.09/2.50  --inst_eager_unprocessed_to_passive     true
% 16.09/2.50  --inst_prop_sim_given                   true
% 16.09/2.50  --inst_prop_sim_new                     false
% 16.09/2.50  --inst_subs_new                         false
% 16.09/2.50  --inst_eq_res_simp                      false
% 16.09/2.50  --inst_subs_given                       false
% 16.09/2.50  --inst_orphan_elimination               true
% 16.09/2.50  --inst_learning_loop_flag               true
% 16.09/2.50  --inst_learning_start                   3000
% 16.09/2.50  --inst_learning_factor                  2
% 16.09/2.50  --inst_start_prop_sim_after_learn       3
% 16.09/2.50  --inst_sel_renew                        solver
% 16.09/2.50  --inst_lit_activity_flag                true
% 16.09/2.50  --inst_restr_to_given                   false
% 16.09/2.50  --inst_activity_threshold               500
% 16.09/2.50  --inst_out_proof                        true
% 16.09/2.50  
% 16.09/2.50  ------ Resolution Options
% 16.09/2.50  
% 16.09/2.50  --resolution_flag                       true
% 16.09/2.50  --res_lit_sel                           adaptive
% 16.09/2.50  --res_lit_sel_side                      none
% 16.09/2.50  --res_ordering                          kbo
% 16.09/2.50  --res_to_prop_solver                    active
% 16.09/2.50  --res_prop_simpl_new                    false
% 16.09/2.50  --res_prop_simpl_given                  true
% 16.09/2.50  --res_passive_queue_type                priority_queues
% 16.09/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 16.09/2.50  --res_passive_queues_freq               [15;5]
% 16.09/2.50  --res_forward_subs                      full
% 16.09/2.50  --res_backward_subs                     full
% 16.09/2.50  --res_forward_subs_resolution           true
% 16.09/2.50  --res_backward_subs_resolution          true
% 16.09/2.50  --res_orphan_elimination                true
% 16.09/2.50  --res_time_limit                        2.
% 16.09/2.50  --res_out_proof                         true
% 16.09/2.50  
% 16.09/2.50  ------ Superposition Options
% 16.09/2.50  
% 16.09/2.50  --superposition_flag                    true
% 16.09/2.50  --sup_passive_queue_type                priority_queues
% 16.09/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 16.09/2.50  --sup_passive_queues_freq               [1;4]
% 16.09/2.50  --demod_completeness_check              fast
% 16.09/2.50  --demod_use_ground                      true
% 16.09/2.50  --sup_to_prop_solver                    passive
% 16.09/2.50  --sup_prop_simpl_new                    true
% 16.09/2.50  --sup_prop_simpl_given                  true
% 16.09/2.50  --sup_fun_splitting                     false
% 16.09/2.50  --sup_smt_interval                      50000
% 16.09/2.50  
% 16.09/2.50  ------ Superposition Simplification Setup
% 16.09/2.50  
% 16.09/2.50  --sup_indices_passive                   []
% 16.09/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.09/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.09/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.09/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 16.09/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.09/2.50  --sup_full_bw                           [BwDemod]
% 16.09/2.50  --sup_immed_triv                        [TrivRules]
% 16.09/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 16.09/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.09/2.50  --sup_immed_bw_main                     []
% 16.09/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.09/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 16.09/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.09/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.09/2.50  
% 16.09/2.50  ------ Combination Options
% 16.09/2.50  
% 16.09/2.50  --comb_res_mult                         3
% 16.09/2.50  --comb_sup_mult                         2
% 16.09/2.50  --comb_inst_mult                        10
% 16.09/2.50  
% 16.09/2.50  ------ Debug Options
% 16.09/2.50  
% 16.09/2.50  --dbg_backtrace                         false
% 16.09/2.50  --dbg_dump_prop_clauses                 false
% 16.09/2.50  --dbg_dump_prop_clauses_file            -
% 16.09/2.50  --dbg_out_stat                          false
% 16.09/2.50  ------ Parsing...
% 16.09/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 16.09/2.50  
% 16.09/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 16.09/2.50  
% 16.09/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 16.09/2.50  
% 16.09/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.09/2.50  ------ Proving...
% 16.09/2.50  ------ Problem Properties 
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  clauses                                 14
% 16.09/2.50  conjectures                             3
% 16.09/2.50  EPR                                     3
% 16.09/2.50  Horn                                    12
% 16.09/2.50  unary                                   10
% 16.09/2.50  binary                                  4
% 16.09/2.50  lits                                    18
% 16.09/2.50  lits eq                                 7
% 16.09/2.50  fd_pure                                 0
% 16.09/2.50  fd_pseudo                               0
% 16.09/2.50  fd_cond                                 1
% 16.09/2.50  fd_pseudo_cond                          0
% 16.09/2.50  AC symbols                              0
% 16.09/2.50  
% 16.09/2.50  ------ Input Options Time Limit: Unbounded
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  ------ 
% 16.09/2.50  Current options:
% 16.09/2.50  ------ 
% 16.09/2.50  
% 16.09/2.50  ------ Input Options
% 16.09/2.50  
% 16.09/2.50  --out_options                           all
% 16.09/2.50  --tptp_safe_out                         true
% 16.09/2.50  --problem_path                          ""
% 16.09/2.50  --include_path                          ""
% 16.09/2.50  --clausifier                            res/vclausify_rel
% 16.09/2.50  --clausifier_options                    --mode clausify
% 16.09/2.50  --stdin                                 false
% 16.09/2.50  --stats_out                             sel
% 16.09/2.50  
% 16.09/2.50  ------ General Options
% 16.09/2.50  
% 16.09/2.50  --fof                                   false
% 16.09/2.50  --time_out_real                         604.99
% 16.09/2.50  --time_out_virtual                      -1.
% 16.09/2.50  --symbol_type_check                     false
% 16.09/2.50  --clausify_out                          false
% 16.09/2.50  --sig_cnt_out                           false
% 16.09/2.50  --trig_cnt_out                          false
% 16.09/2.50  --trig_cnt_out_tolerance                1.
% 16.09/2.50  --trig_cnt_out_sk_spl                   false
% 16.09/2.50  --abstr_cl_out                          false
% 16.09/2.50  
% 16.09/2.50  ------ Global Options
% 16.09/2.50  
% 16.09/2.50  --schedule                              none
% 16.09/2.50  --add_important_lit                     false
% 16.09/2.50  --prop_solver_per_cl                    1000
% 16.09/2.50  --min_unsat_core                        false
% 16.09/2.50  --soft_assumptions                      false
% 16.09/2.50  --soft_lemma_size                       3
% 16.09/2.50  --prop_impl_unit_size                   0
% 16.09/2.50  --prop_impl_unit                        []
% 16.09/2.50  --share_sel_clauses                     true
% 16.09/2.50  --reset_solvers                         false
% 16.09/2.50  --bc_imp_inh                            [conj_cone]
% 16.09/2.50  --conj_cone_tolerance                   3.
% 16.09/2.50  --extra_neg_conj                        none
% 16.09/2.50  --large_theory_mode                     true
% 16.09/2.50  --prolific_symb_bound                   200
% 16.09/2.50  --lt_threshold                          2000
% 16.09/2.50  --clause_weak_htbl                      true
% 16.09/2.50  --gc_record_bc_elim                     false
% 16.09/2.50  
% 16.09/2.50  ------ Preprocessing Options
% 16.09/2.50  
% 16.09/2.50  --preprocessing_flag                    true
% 16.09/2.50  --time_out_prep_mult                    0.1
% 16.09/2.50  --splitting_mode                        input
% 16.09/2.50  --splitting_grd                         true
% 16.09/2.50  --splitting_cvd                         false
% 16.09/2.50  --splitting_cvd_svl                     false
% 16.09/2.50  --splitting_nvd                         32
% 16.09/2.50  --sub_typing                            true
% 16.09/2.50  --prep_gs_sim                           false
% 16.09/2.50  --prep_unflatten                        true
% 16.09/2.50  --prep_res_sim                          true
% 16.09/2.50  --prep_upred                            true
% 16.09/2.50  --prep_sem_filter                       exhaustive
% 16.09/2.50  --prep_sem_filter_out                   false
% 16.09/2.50  --pred_elim                             false
% 16.09/2.50  --res_sim_input                         true
% 16.09/2.50  --eq_ax_congr_red                       true
% 16.09/2.50  --pure_diseq_elim                       true
% 16.09/2.50  --brand_transform                       false
% 16.09/2.50  --non_eq_to_eq                          false
% 16.09/2.50  --prep_def_merge                        true
% 16.09/2.50  --prep_def_merge_prop_impl              false
% 16.09/2.50  --prep_def_merge_mbd                    true
% 16.09/2.50  --prep_def_merge_tr_red                 false
% 16.09/2.50  --prep_def_merge_tr_cl                  false
% 16.09/2.50  --smt_preprocessing                     true
% 16.09/2.50  --smt_ac_axioms                         fast
% 16.09/2.50  --preprocessed_out                      false
% 16.09/2.50  --preprocessed_stats                    false
% 16.09/2.50  
% 16.09/2.50  ------ Abstraction refinement Options
% 16.09/2.50  
% 16.09/2.50  --abstr_ref                             []
% 16.09/2.50  --abstr_ref_prep                        false
% 16.09/2.50  --abstr_ref_until_sat                   false
% 16.09/2.50  --abstr_ref_sig_restrict                funpre
% 16.09/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 16.09/2.50  --abstr_ref_under                       []
% 16.09/2.50  
% 16.09/2.50  ------ SAT Options
% 16.09/2.50  
% 16.09/2.50  --sat_mode                              false
% 16.09/2.50  --sat_fm_restart_options                ""
% 16.09/2.50  --sat_gr_def                            false
% 16.09/2.50  --sat_epr_types                         true
% 16.09/2.50  --sat_non_cyclic_types                  false
% 16.09/2.50  --sat_finite_models                     false
% 16.09/2.50  --sat_fm_lemmas                         false
% 16.09/2.50  --sat_fm_prep                           false
% 16.09/2.50  --sat_fm_uc_incr                        true
% 16.09/2.50  --sat_out_model                         small
% 16.09/2.50  --sat_out_clauses                       false
% 16.09/2.50  
% 16.09/2.50  ------ QBF Options
% 16.09/2.50  
% 16.09/2.50  --qbf_mode                              false
% 16.09/2.50  --qbf_elim_univ                         false
% 16.09/2.50  --qbf_dom_inst                          none
% 16.09/2.50  --qbf_dom_pre_inst                      false
% 16.09/2.50  --qbf_sk_in                             false
% 16.09/2.50  --qbf_pred_elim                         true
% 16.09/2.50  --qbf_split                             512
% 16.09/2.50  
% 16.09/2.50  ------ BMC1 Options
% 16.09/2.50  
% 16.09/2.50  --bmc1_incremental                      false
% 16.09/2.50  --bmc1_axioms                           reachable_all
% 16.09/2.50  --bmc1_min_bound                        0
% 16.09/2.50  --bmc1_max_bound                        -1
% 16.09/2.50  --bmc1_max_bound_default                -1
% 16.09/2.50  --bmc1_symbol_reachability              true
% 16.09/2.50  --bmc1_property_lemmas                  false
% 16.09/2.50  --bmc1_k_induction                      false
% 16.09/2.50  --bmc1_non_equiv_states                 false
% 16.09/2.50  --bmc1_deadlock                         false
% 16.09/2.50  --bmc1_ucm                              false
% 16.09/2.50  --bmc1_add_unsat_core                   none
% 16.09/2.50  --bmc1_unsat_core_children              false
% 16.09/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 16.09/2.50  --bmc1_out_stat                         full
% 16.09/2.50  --bmc1_ground_init                      false
% 16.09/2.50  --bmc1_pre_inst_next_state              false
% 16.09/2.50  --bmc1_pre_inst_state                   false
% 16.09/2.50  --bmc1_pre_inst_reach_state             false
% 16.09/2.50  --bmc1_out_unsat_core                   false
% 16.09/2.50  --bmc1_aig_witness_out                  false
% 16.09/2.50  --bmc1_verbose                          false
% 16.09/2.50  --bmc1_dump_clauses_tptp                false
% 16.09/2.50  --bmc1_dump_unsat_core_tptp             false
% 16.09/2.50  --bmc1_dump_file                        -
% 16.09/2.50  --bmc1_ucm_expand_uc_limit              128
% 16.09/2.50  --bmc1_ucm_n_expand_iterations          6
% 16.09/2.50  --bmc1_ucm_extend_mode                  1
% 16.09/2.50  --bmc1_ucm_init_mode                    2
% 16.09/2.50  --bmc1_ucm_cone_mode                    none
% 16.09/2.50  --bmc1_ucm_reduced_relation_type        0
% 16.09/2.50  --bmc1_ucm_relax_model                  4
% 16.09/2.50  --bmc1_ucm_full_tr_after_sat            true
% 16.09/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 16.09/2.50  --bmc1_ucm_layered_model                none
% 16.09/2.50  --bmc1_ucm_max_lemma_size               10
% 16.09/2.50  
% 16.09/2.50  ------ AIG Options
% 16.09/2.50  
% 16.09/2.50  --aig_mode                              false
% 16.09/2.50  
% 16.09/2.50  ------ Instantiation Options
% 16.09/2.50  
% 16.09/2.50  --instantiation_flag                    true
% 16.09/2.50  --inst_sos_flag                         false
% 16.09/2.50  --inst_sos_phase                        true
% 16.09/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 16.09/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 16.09/2.50  --inst_lit_sel_side                     num_symb
% 16.09/2.50  --inst_solver_per_active                1400
% 16.09/2.50  --inst_solver_calls_frac                1.
% 16.09/2.50  --inst_passive_queue_type               priority_queues
% 16.09/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 16.09/2.50  --inst_passive_queues_freq              [25;2]
% 16.09/2.50  --inst_dismatching                      true
% 16.09/2.50  --inst_eager_unprocessed_to_passive     true
% 16.09/2.50  --inst_prop_sim_given                   true
% 16.09/2.50  --inst_prop_sim_new                     false
% 16.09/2.50  --inst_subs_new                         false
% 16.09/2.50  --inst_eq_res_simp                      false
% 16.09/2.50  --inst_subs_given                       false
% 16.09/2.50  --inst_orphan_elimination               true
% 16.09/2.50  --inst_learning_loop_flag               true
% 16.09/2.50  --inst_learning_start                   3000
% 16.09/2.50  --inst_learning_factor                  2
% 16.09/2.50  --inst_start_prop_sim_after_learn       3
% 16.09/2.50  --inst_sel_renew                        solver
% 16.09/2.50  --inst_lit_activity_flag                true
% 16.09/2.50  --inst_restr_to_given                   false
% 16.09/2.50  --inst_activity_threshold               500
% 16.09/2.50  --inst_out_proof                        true
% 16.09/2.50  
% 16.09/2.50  ------ Resolution Options
% 16.09/2.50  
% 16.09/2.50  --resolution_flag                       true
% 16.09/2.50  --res_lit_sel                           adaptive
% 16.09/2.50  --res_lit_sel_side                      none
% 16.09/2.50  --res_ordering                          kbo
% 16.09/2.50  --res_to_prop_solver                    active
% 16.09/2.50  --res_prop_simpl_new                    false
% 16.09/2.50  --res_prop_simpl_given                  true
% 16.09/2.50  --res_passive_queue_type                priority_queues
% 16.09/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 16.09/2.50  --res_passive_queues_freq               [15;5]
% 16.09/2.50  --res_forward_subs                      full
% 16.09/2.50  --res_backward_subs                     full
% 16.09/2.50  --res_forward_subs_resolution           true
% 16.09/2.50  --res_backward_subs_resolution          true
% 16.09/2.50  --res_orphan_elimination                true
% 16.09/2.50  --res_time_limit                        2.
% 16.09/2.50  --res_out_proof                         true
% 16.09/2.50  
% 16.09/2.50  ------ Superposition Options
% 16.09/2.50  
% 16.09/2.50  --superposition_flag                    true
% 16.09/2.50  --sup_passive_queue_type                priority_queues
% 16.09/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 16.09/2.50  --sup_passive_queues_freq               [1;4]
% 16.09/2.50  --demod_completeness_check              fast
% 16.09/2.50  --demod_use_ground                      true
% 16.09/2.50  --sup_to_prop_solver                    passive
% 16.09/2.50  --sup_prop_simpl_new                    true
% 16.09/2.50  --sup_prop_simpl_given                  true
% 16.09/2.50  --sup_fun_splitting                     false
% 16.09/2.50  --sup_smt_interval                      50000
% 16.09/2.50  
% 16.09/2.50  ------ Superposition Simplification Setup
% 16.09/2.50  
% 16.09/2.50  --sup_indices_passive                   []
% 16.09/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.09/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.09/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.09/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 16.09/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.09/2.50  --sup_full_bw                           [BwDemod]
% 16.09/2.50  --sup_immed_triv                        [TrivRules]
% 16.09/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 16.09/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.09/2.50  --sup_immed_bw_main                     []
% 16.09/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.09/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 16.09/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.09/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.09/2.50  
% 16.09/2.50  ------ Combination Options
% 16.09/2.50  
% 16.09/2.50  --comb_res_mult                         3
% 16.09/2.50  --comb_sup_mult                         2
% 16.09/2.50  --comb_inst_mult                        10
% 16.09/2.50  
% 16.09/2.50  ------ Debug Options
% 16.09/2.50  
% 16.09/2.50  --dbg_backtrace                         false
% 16.09/2.50  --dbg_dump_prop_clauses                 false
% 16.09/2.50  --dbg_dump_prop_clauses_file            -
% 16.09/2.50  --dbg_out_stat                          false
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  ------ Proving...
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  % SZS status Theorem for theBenchmark.p
% 16.09/2.50  
% 16.09/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 16.09/2.50  
% 16.09/2.50  fof(f12,conjecture,(
% 16.09/2.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f13,negated_conjecture,(
% 16.09/2.50    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 16.09/2.50    inference(negated_conjecture,[],[f12])).
% 16.09/2.50  
% 16.09/2.50  fof(f19,plain,(
% 16.09/2.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 16.09/2.50    inference(ennf_transformation,[],[f13])).
% 16.09/2.50  
% 16.09/2.50  fof(f24,plain,(
% 16.09/2.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) & r1_tarski(sK2,sK4) & ~r1_xboole_0(sK2,sK3))),
% 16.09/2.50    introduced(choice_axiom,[])).
% 16.09/2.50  
% 16.09/2.50  fof(f25,plain,(
% 16.09/2.50    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4)) & r1_tarski(sK2,sK4) & ~r1_xboole_0(sK2,sK3)),
% 16.09/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f24])).
% 16.09/2.50  
% 16.09/2.50  fof(f40,plain,(
% 16.09/2.50    r1_xboole_0(sK2,k3_xboole_0(sK3,sK4))),
% 16.09/2.50    inference(cnf_transformation,[],[f25])).
% 16.09/2.50  
% 16.09/2.50  fof(f8,axiom,(
% 16.09/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f34,plain,(
% 16.09/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 16.09/2.50    inference(cnf_transformation,[],[f8])).
% 16.09/2.50  
% 16.09/2.50  fof(f47,plain,(
% 16.09/2.50    r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))),
% 16.09/2.50    inference(definition_unfolding,[],[f40,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f2,axiom,(
% 16.09/2.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f17,plain,(
% 16.09/2.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 16.09/2.50    inference(ennf_transformation,[],[f2])).
% 16.09/2.50  
% 16.09/2.50  fof(f22,plain,(
% 16.09/2.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 16.09/2.50    introduced(choice_axiom,[])).
% 16.09/2.50  
% 16.09/2.50  fof(f23,plain,(
% 16.09/2.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 16.09/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f22])).
% 16.09/2.50  
% 16.09/2.50  fof(f28,plain,(
% 16.09/2.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 16.09/2.50    inference(cnf_transformation,[],[f23])).
% 16.09/2.50  
% 16.09/2.50  fof(f1,axiom,(
% 16.09/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f14,plain,(
% 16.09/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 16.09/2.50    inference(rectify,[],[f1])).
% 16.09/2.50  
% 16.09/2.50  fof(f16,plain,(
% 16.09/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 16.09/2.50    inference(ennf_transformation,[],[f14])).
% 16.09/2.50  
% 16.09/2.50  fof(f20,plain,(
% 16.09/2.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 16.09/2.50    introduced(choice_axiom,[])).
% 16.09/2.50  
% 16.09/2.50  fof(f21,plain,(
% 16.09/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 16.09/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f20])).
% 16.09/2.50  
% 16.09/2.50  fof(f27,plain,(
% 16.09/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 16.09/2.50    inference(cnf_transformation,[],[f21])).
% 16.09/2.50  
% 16.09/2.50  fof(f41,plain,(
% 16.09/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 16.09/2.50    inference(definition_unfolding,[],[f27,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f39,plain,(
% 16.09/2.50    r1_tarski(sK2,sK4)),
% 16.09/2.50    inference(cnf_transformation,[],[f25])).
% 16.09/2.50  
% 16.09/2.50  fof(f3,axiom,(
% 16.09/2.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f15,plain,(
% 16.09/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 16.09/2.50    inference(unused_predicate_definition_removal,[],[f3])).
% 16.09/2.50  
% 16.09/2.50  fof(f18,plain,(
% 16.09/2.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 16.09/2.50    inference(ennf_transformation,[],[f15])).
% 16.09/2.50  
% 16.09/2.50  fof(f29,plain,(
% 16.09/2.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 16.09/2.50    inference(cnf_transformation,[],[f18])).
% 16.09/2.50  
% 16.09/2.50  fof(f10,axiom,(
% 16.09/2.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f36,plain,(
% 16.09/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 16.09/2.50    inference(cnf_transformation,[],[f10])).
% 16.09/2.50  
% 16.09/2.50  fof(f46,plain,(
% 16.09/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 16.09/2.50    inference(definition_unfolding,[],[f36,f34,f34,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f9,axiom,(
% 16.09/2.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f35,plain,(
% 16.09/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 16.09/2.50    inference(cnf_transformation,[],[f9])).
% 16.09/2.50  
% 16.09/2.50  fof(f45,plain,(
% 16.09/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 16.09/2.50    inference(definition_unfolding,[],[f35,f34,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f7,axiom,(
% 16.09/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f33,plain,(
% 16.09/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 16.09/2.50    inference(cnf_transformation,[],[f7])).
% 16.09/2.50  
% 16.09/2.50  fof(f44,plain,(
% 16.09/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 16.09/2.50    inference(definition_unfolding,[],[f33,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f6,axiom,(
% 16.09/2.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f32,plain,(
% 16.09/2.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 16.09/2.50    inference(cnf_transformation,[],[f6])).
% 16.09/2.50  
% 16.09/2.50  fof(f5,axiom,(
% 16.09/2.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f31,plain,(
% 16.09/2.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 16.09/2.50    inference(cnf_transformation,[],[f5])).
% 16.09/2.50  
% 16.09/2.50  fof(f4,axiom,(
% 16.09/2.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f30,plain,(
% 16.09/2.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 16.09/2.50    inference(cnf_transformation,[],[f4])).
% 16.09/2.50  
% 16.09/2.50  fof(f43,plain,(
% 16.09/2.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 16.09/2.50    inference(definition_unfolding,[],[f30,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f26,plain,(
% 16.09/2.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 16.09/2.50    inference(cnf_transformation,[],[f21])).
% 16.09/2.50  
% 16.09/2.50  fof(f42,plain,(
% 16.09/2.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 16.09/2.50    inference(definition_unfolding,[],[f26,f34])).
% 16.09/2.50  
% 16.09/2.50  fof(f11,axiom,(
% 16.09/2.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 16.09/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.09/2.50  
% 16.09/2.50  fof(f37,plain,(
% 16.09/2.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 16.09/2.50    inference(cnf_transformation,[],[f11])).
% 16.09/2.50  
% 16.09/2.50  fof(f38,plain,(
% 16.09/2.50    ~r1_xboole_0(sK2,sK3)),
% 16.09/2.50    inference(cnf_transformation,[],[f25])).
% 16.09/2.50  
% 16.09/2.50  cnf(c_11,negated_conjecture,
% 16.09/2.50      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
% 16.09/2.50      inference(cnf_transformation,[],[f47]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_268,plain,
% 16.09/2.50      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 16.09/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_2,plain,
% 16.09/2.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 16.09/2.50      inference(cnf_transformation,[],[f28]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_272,plain,
% 16.09/2.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 16.09/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_0,plain,
% 16.09/2.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 16.09/2.50      | ~ r1_xboole_0(X1,X2) ),
% 16.09/2.50      inference(cnf_transformation,[],[f41]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_274,plain,
% 16.09/2.50      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 16.09/2.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 16.09/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_1860,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 16.09/2.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_272,c_274]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_87522,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k1_xboole_0 ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_268,c_1860]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_12,negated_conjecture,
% 16.09/2.50      ( r1_tarski(sK2,sK4) ),
% 16.09/2.50      inference(cnf_transformation,[],[f39]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_267,plain,
% 16.09/2.50      ( r1_tarski(sK2,sK4) = iProver_top ),
% 16.09/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_3,plain,
% 16.09/2.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 16.09/2.50      inference(cnf_transformation,[],[f29]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_271,plain,
% 16.09/2.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 16.09/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 16.09/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_1027,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_267,c_271]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_9,plain,
% 16.09/2.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 16.09/2.50      inference(cnf_transformation,[],[f46]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_8,plain,
% 16.09/2.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 16.09/2.50      inference(cnf_transformation,[],[f45]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_436,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_7,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 16.09/2.50      inference(cnf_transformation,[],[f44]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_5919,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_436,c_7]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_6013,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 16.09/2.50      inference(demodulation,[status(thm)],[c_5919,c_7]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_24137,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(X0,sK4)) ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_1027,c_6013]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_6,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 16.09/2.50      inference(cnf_transformation,[],[f32]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_5,plain,
% 16.09/2.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 16.09/2.50      inference(cnf_transformation,[],[f31]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_270,plain,
% 16.09/2.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 16.09/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_1026,plain,
% 16.09/2.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_270,c_271]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_22128,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_1026,c_8]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_22490,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_22128,c_7]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_22752,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 16.09/2.50      inference(light_normalisation,[status(thm)],[c_22490,c_6]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_24203,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK4)) = sK2 ),
% 16.09/2.50      inference(demodulation,[status(thm)],[c_24137,c_6,c_22752]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_24923,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,sK4))) = k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK2,sK2))) ),
% 16.09/2.50      inference(superposition,[status(thm)],[c_24203,c_6013]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_4,plain,
% 16.09/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 16.09/2.50      inference(cnf_transformation,[],[f43]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_285,plain,
% 16.09/2.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 16.09/2.50      inference(light_normalisation,[status(thm)],[c_4,c_6]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_25029,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X1,sK4))) = k4_xboole_0(sK2,X0) ),
% 16.09/2.50      inference(demodulation,[status(thm)],[c_24923,c_6,c_285]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_87524,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 16.09/2.50      inference(demodulation,[status(thm)],[c_87522,c_25029]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_97,plain,
% 16.09/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 16.09/2.50      theory(equality) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_968,plain,
% 16.09/2.50      ( r2_hidden(X0,X1)
% 16.09/2.50      | ~ r2_hidden(sK0(sK2,sK3),X2)
% 16.09/2.50      | X1 != X2
% 16.09/2.50      | X0 != sK0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_97]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_3174,plain,
% 16.09/2.50      ( ~ r2_hidden(sK0(sK2,sK3),X0)
% 16.09/2.50      | r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),X1)
% 16.09/2.50      | X1 != X0
% 16.09/2.50      | k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) != sK0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_968]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_7170,plain,
% 16.09/2.50      ( ~ r2_hidden(sK0(sK2,sK3),X0)
% 16.09/2.50      | r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 16.09/2.50      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != X0
% 16.09/2.50      | k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) != sK0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_3174]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_7172,plain,
% 16.09/2.50      ( ~ r2_hidden(sK0(sK2,sK3),k1_xboole_0)
% 16.09/2.50      | r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 16.09/2.50      | k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) != sK0(sK2,sK3)
% 16.09/2.50      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_7170]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_94,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_586,plain,
% 16.09/2.50      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_94]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_1440,plain,
% 16.09/2.50      ( X0 != X1
% 16.09/2.50      | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 16.09/2.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_586]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_1441,plain,
% 16.09/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0
% 16.09/2.50      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 16.09/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_1440]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_944,plain,
% 16.09/2.50      ( ~ r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 16.09/2.50      | ~ r1_xboole_0(X0,X1) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_950,plain,
% 16.09/2.50      ( ~ r2_hidden(k4_xboole_0(sK0(sK2,sK3),k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 16.09/2.50      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_944]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_93,plain,( X0 = X0 ),theory(equality) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_654,plain,
% 16.09/2.50      ( sK0(sK2,sK3) = sK0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_93]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_523,plain,
% 16.09/2.50      ( r2_hidden(X0,X1)
% 16.09/2.50      | ~ r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 16.09/2.50      | X0 != sK0(sK2,sK3)
% 16.09/2.50      | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_97]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_653,plain,
% 16.09/2.50      ( r2_hidden(sK0(sK2,sK3),X0)
% 16.09/2.50      | ~ r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 16.09/2.50      | X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 16.09/2.50      | sK0(sK2,sK3) != sK0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_523]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_656,plain,
% 16.09/2.50      ( ~ r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 16.09/2.50      | r2_hidden(sK0(sK2,sK3),k1_xboole_0)
% 16.09/2.50      | sK0(sK2,sK3) != sK0(sK2,sK3)
% 16.09/2.50      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_653]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_648,plain,
% 16.09/2.50      ( k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) = sK0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_1,plain,
% 16.09/2.50      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 16.09/2.50      | r1_xboole_0(X0,X1) ),
% 16.09/2.50      inference(cnf_transformation,[],[f42]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_359,plain,
% 16.09/2.50      ( r2_hidden(sK0(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 16.09/2.50      | r1_xboole_0(sK2,sK3) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_104,plain,
% 16.09/2.50      ( k1_xboole_0 = k1_xboole_0 ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_93]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_27,plain,
% 16.09/2.50      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_10,plain,
% 16.09/2.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 16.09/2.50      inference(cnf_transformation,[],[f37]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_18,plain,
% 16.09/2.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 16.09/2.50      inference(instantiation,[status(thm)],[c_10]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(c_13,negated_conjecture,
% 16.09/2.50      ( ~ r1_xboole_0(sK2,sK3) ),
% 16.09/2.50      inference(cnf_transformation,[],[f38]) ).
% 16.09/2.50  
% 16.09/2.50  cnf(contradiction,plain,
% 16.09/2.50      ( $false ),
% 16.09/2.50      inference(minisat,
% 16.09/2.50                [status(thm)],
% 16.09/2.50                [c_87524,c_7172,c_1441,c_950,c_654,c_656,c_648,c_359,
% 16.09/2.50                 c_104,c_27,c_18,c_13]) ).
% 16.09/2.50  
% 16.09/2.50  
% 16.09/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 16.09/2.50  
% 16.09/2.50  ------                               Statistics
% 16.09/2.50  
% 16.09/2.50  ------ Selected
% 16.09/2.50  
% 16.09/2.50  total_time:                             1.99
% 16.09/2.50  
%------------------------------------------------------------------------------
