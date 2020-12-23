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
% DateTime   : Thu Dec  3 11:23:46 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 217 expanded)
%              Number of clauses        :   63 (  90 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   22
%              Number of atoms          :  187 ( 425 expanded)
%              Number of equality atoms :  125 ( 268 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK3 != sK4
      & r1_xboole_0(sK5,sK3)
      & r1_xboole_0(sK4,sK2)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK3 != sK4
    & r1_xboole_0(sK5,sK3)
    & r1_xboole_0(sK4,sK2)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f24])).

fof(f37,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f22])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f35,f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f39,plain,(
    r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_267,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_257,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_114,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK5 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_115,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_255,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_284,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_255])).

cnf(c_2427,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_257,c_284])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2967,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_2427,c_8])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2972,plain,
    ( k4_xboole_0(sK3,sK5) = sK3 ),
    inference(demodulation,[status(thm)],[c_2967,c_6])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3210,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2972,c_7])).

cnf(c_6212,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK5)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3210])).

cnf(c_7768,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_267,c_6212])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_95,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_96,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_7802,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7768,c_96])).

cnf(c_534,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_7998,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_7802,c_534])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_123,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_254,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_2426,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_257,c_254])).

cnf(c_2508,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2426,c_8])).

cnf(c_2513,plain,
    ( k4_xboole_0(sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_2508,c_6])).

cnf(c_3118,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2513,c_7])).

cnf(c_4836,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3118])).

cnf(c_491,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_267,c_96])).

cnf(c_7546,plain,
    ( k4_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4836,c_491])).

cnf(c_8012,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
    inference(light_normalisation,[status(thm)],[c_7998,c_7546])).

cnf(c_536,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_8013,plain,
    ( k4_xboole_0(sK3,X0) = k4_xboole_0(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_8012,c_7,c_536])).

cnf(c_8032,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8013])).

cnf(c_173,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_315,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_699,plain,
    ( k4_xboole_0(X0,X1) != X2
    | sK4 != X2
    | sK4 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1363,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(sK4,k1_xboole_0)
    | sK4 = k4_xboole_0(X0,X1)
    | sK4 != k4_xboole_0(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_3912,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) != k4_xboole_0(sK4,k1_xboole_0)
    | sK4 != k4_xboole_0(sK4,k1_xboole_0)
    | sK4 = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_305,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_635,plain,
    ( sK4 != k4_xboole_0(X0,X1)
    | sK3 != k4_xboole_0(X0,X1)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_3152,plain,
    ( sK4 != k4_xboole_0(sK3,k1_xboole_0)
    | sK3 != k4_xboole_0(sK3,k1_xboole_0)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_1252,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_516,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_690,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1251,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) != sK3
    | sK3 = k4_xboole_0(sK3,k1_xboole_0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_172,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_515,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_415,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_344,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_414,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) != sK4
    | sK4 = k4_xboole_0(sK4,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_345,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_10,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8032,c_3912,c_3152,c_1252,c_1251,c_515,c_415,c_414,c_345,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:30:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.32/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.97  
% 3.32/0.97  ------  iProver source info
% 3.32/0.97  
% 3.32/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.97  git: non_committed_changes: false
% 3.32/0.97  git: last_make_outside_of_git: false
% 3.32/0.97  
% 3.32/0.97  ------ 
% 3.32/0.97  
% 3.32/0.97  ------ Input Options
% 3.32/0.97  
% 3.32/0.97  --out_options                           all
% 3.32/0.97  --tptp_safe_out                         true
% 3.32/0.97  --problem_path                          ""
% 3.32/0.97  --include_path                          ""
% 3.32/0.97  --clausifier                            res/vclausify_rel
% 3.32/0.97  --clausifier_options                    --mode clausify
% 3.32/0.97  --stdin                                 false
% 3.32/0.97  --stats_out                             all
% 3.32/0.97  
% 3.32/0.97  ------ General Options
% 3.32/0.97  
% 3.32/0.97  --fof                                   false
% 3.32/0.97  --time_out_real                         305.
% 3.32/0.97  --time_out_virtual                      -1.
% 3.32/0.97  --symbol_type_check                     false
% 3.32/0.97  --clausify_out                          false
% 3.32/0.97  --sig_cnt_out                           false
% 3.32/0.97  --trig_cnt_out                          false
% 3.32/0.97  --trig_cnt_out_tolerance                1.
% 3.32/0.97  --trig_cnt_out_sk_spl                   false
% 3.32/0.97  --abstr_cl_out                          false
% 3.32/0.97  
% 3.32/0.97  ------ Global Options
% 3.32/0.97  
% 3.32/0.97  --schedule                              default
% 3.32/0.97  --add_important_lit                     false
% 3.32/0.97  --prop_solver_per_cl                    1000
% 3.32/0.97  --min_unsat_core                        false
% 3.32/0.97  --soft_assumptions                      false
% 3.32/0.97  --soft_lemma_size                       3
% 3.32/0.97  --prop_impl_unit_size                   0
% 3.32/0.97  --prop_impl_unit                        []
% 3.32/0.97  --share_sel_clauses                     true
% 3.32/0.97  --reset_solvers                         false
% 3.32/0.97  --bc_imp_inh                            [conj_cone]
% 3.32/0.97  --conj_cone_tolerance                   3.
% 3.32/0.97  --extra_neg_conj                        none
% 3.32/0.97  --large_theory_mode                     true
% 3.32/0.97  --prolific_symb_bound                   200
% 3.32/0.97  --lt_threshold                          2000
% 3.32/0.97  --clause_weak_htbl                      true
% 3.32/0.97  --gc_record_bc_elim                     false
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing Options
% 3.32/0.97  
% 3.32/0.97  --preprocessing_flag                    true
% 3.32/0.97  --time_out_prep_mult                    0.1
% 3.32/0.97  --splitting_mode                        input
% 3.32/0.97  --splitting_grd                         true
% 3.32/0.97  --splitting_cvd                         false
% 3.32/0.97  --splitting_cvd_svl                     false
% 3.32/0.97  --splitting_nvd                         32
% 3.32/0.97  --sub_typing                            true
% 3.32/0.97  --prep_gs_sim                           true
% 3.32/0.97  --prep_unflatten                        true
% 3.32/0.97  --prep_res_sim                          true
% 3.32/0.97  --prep_upred                            true
% 3.32/0.97  --prep_sem_filter                       exhaustive
% 3.32/0.97  --prep_sem_filter_out                   false
% 3.32/0.97  --pred_elim                             true
% 3.32/0.97  --res_sim_input                         true
% 3.32/0.97  --eq_ax_congr_red                       true
% 3.32/0.97  --pure_diseq_elim                       true
% 3.32/0.97  --brand_transform                       false
% 3.32/0.97  --non_eq_to_eq                          false
% 3.32/0.97  --prep_def_merge                        true
% 3.32/0.97  --prep_def_merge_prop_impl              false
% 3.32/0.97  --prep_def_merge_mbd                    true
% 3.32/0.97  --prep_def_merge_tr_red                 false
% 3.32/0.97  --prep_def_merge_tr_cl                  false
% 3.32/0.97  --smt_preprocessing                     true
% 3.32/0.97  --smt_ac_axioms                         fast
% 3.32/0.97  --preprocessed_out                      false
% 3.32/0.97  --preprocessed_stats                    false
% 3.32/0.97  
% 3.32/0.97  ------ Abstraction refinement Options
% 3.32/0.97  
% 3.32/0.97  --abstr_ref                             []
% 3.32/0.97  --abstr_ref_prep                        false
% 3.32/0.97  --abstr_ref_until_sat                   false
% 3.32/0.97  --abstr_ref_sig_restrict                funpre
% 3.32/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.97  --abstr_ref_under                       []
% 3.32/0.97  
% 3.32/0.97  ------ SAT Options
% 3.32/0.97  
% 3.32/0.97  --sat_mode                              false
% 3.32/0.97  --sat_fm_restart_options                ""
% 3.32/0.97  --sat_gr_def                            false
% 3.32/0.97  --sat_epr_types                         true
% 3.32/0.97  --sat_non_cyclic_types                  false
% 3.32/0.97  --sat_finite_models                     false
% 3.32/0.97  --sat_fm_lemmas                         false
% 3.32/0.97  --sat_fm_prep                           false
% 3.32/0.97  --sat_fm_uc_incr                        true
% 3.32/0.97  --sat_out_model                         small
% 3.32/0.97  --sat_out_clauses                       false
% 3.32/0.97  
% 3.32/0.97  ------ QBF Options
% 3.32/0.97  
% 3.32/0.97  --qbf_mode                              false
% 3.32/0.97  --qbf_elim_univ                         false
% 3.32/0.97  --qbf_dom_inst                          none
% 3.32/0.97  --qbf_dom_pre_inst                      false
% 3.32/0.97  --qbf_sk_in                             false
% 3.32/0.97  --qbf_pred_elim                         true
% 3.32/0.97  --qbf_split                             512
% 3.32/0.97  
% 3.32/0.97  ------ BMC1 Options
% 3.32/0.97  
% 3.32/0.97  --bmc1_incremental                      false
% 3.32/0.97  --bmc1_axioms                           reachable_all
% 3.32/0.97  --bmc1_min_bound                        0
% 3.32/0.97  --bmc1_max_bound                        -1
% 3.32/0.97  --bmc1_max_bound_default                -1
% 3.32/0.97  --bmc1_symbol_reachability              true
% 3.32/0.97  --bmc1_property_lemmas                  false
% 3.32/0.97  --bmc1_k_induction                      false
% 3.32/0.97  --bmc1_non_equiv_states                 false
% 3.32/0.97  --bmc1_deadlock                         false
% 3.32/0.97  --bmc1_ucm                              false
% 3.32/0.97  --bmc1_add_unsat_core                   none
% 3.32/0.97  --bmc1_unsat_core_children              false
% 3.32/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.97  --bmc1_out_stat                         full
% 3.32/0.97  --bmc1_ground_init                      false
% 3.32/0.97  --bmc1_pre_inst_next_state              false
% 3.32/0.97  --bmc1_pre_inst_state                   false
% 3.32/0.97  --bmc1_pre_inst_reach_state             false
% 3.32/0.97  --bmc1_out_unsat_core                   false
% 3.32/0.97  --bmc1_aig_witness_out                  false
% 3.32/0.97  --bmc1_verbose                          false
% 3.32/0.97  --bmc1_dump_clauses_tptp                false
% 3.32/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.97  --bmc1_dump_file                        -
% 3.32/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.97  --bmc1_ucm_extend_mode                  1
% 3.32/0.97  --bmc1_ucm_init_mode                    2
% 3.32/0.97  --bmc1_ucm_cone_mode                    none
% 3.32/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.97  --bmc1_ucm_relax_model                  4
% 3.32/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.97  --bmc1_ucm_layered_model                none
% 3.32/0.97  --bmc1_ucm_max_lemma_size               10
% 3.32/0.97  
% 3.32/0.97  ------ AIG Options
% 3.32/0.97  
% 3.32/0.97  --aig_mode                              false
% 3.32/0.97  
% 3.32/0.97  ------ Instantiation Options
% 3.32/0.97  
% 3.32/0.97  --instantiation_flag                    true
% 3.32/0.97  --inst_sos_flag                         false
% 3.32/0.97  --inst_sos_phase                        true
% 3.32/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel_side                     num_symb
% 3.32/0.97  --inst_solver_per_active                1400
% 3.32/0.97  --inst_solver_calls_frac                1.
% 3.32/0.97  --inst_passive_queue_type               priority_queues
% 3.32/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.97  --inst_passive_queues_freq              [25;2]
% 3.32/0.97  --inst_dismatching                      true
% 3.32/0.97  --inst_eager_unprocessed_to_passive     true
% 3.32/0.97  --inst_prop_sim_given                   true
% 3.32/0.97  --inst_prop_sim_new                     false
% 3.32/0.97  --inst_subs_new                         false
% 3.32/0.97  --inst_eq_res_simp                      false
% 3.32/0.97  --inst_subs_given                       false
% 3.32/0.97  --inst_orphan_elimination               true
% 3.32/0.97  --inst_learning_loop_flag               true
% 3.32/0.97  --inst_learning_start                   3000
% 3.32/0.97  --inst_learning_factor                  2
% 3.32/0.97  --inst_start_prop_sim_after_learn       3
% 3.32/0.97  --inst_sel_renew                        solver
% 3.32/0.97  --inst_lit_activity_flag                true
% 3.32/0.97  --inst_restr_to_given                   false
% 3.32/0.97  --inst_activity_threshold               500
% 3.32/0.97  --inst_out_proof                        true
% 3.32/0.97  
% 3.32/0.97  ------ Resolution Options
% 3.32/0.97  
% 3.32/0.97  --resolution_flag                       true
% 3.32/0.97  --res_lit_sel                           adaptive
% 3.32/0.97  --res_lit_sel_side                      none
% 3.32/0.97  --res_ordering                          kbo
% 3.32/0.97  --res_to_prop_solver                    active
% 3.32/0.97  --res_prop_simpl_new                    false
% 3.32/0.97  --res_prop_simpl_given                  true
% 3.32/0.97  --res_passive_queue_type                priority_queues
% 3.32/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.97  --res_passive_queues_freq               [15;5]
% 3.32/0.97  --res_forward_subs                      full
% 3.32/0.97  --res_backward_subs                     full
% 3.32/0.97  --res_forward_subs_resolution           true
% 3.32/0.97  --res_backward_subs_resolution          true
% 3.32/0.97  --res_orphan_elimination                true
% 3.32/0.97  --res_time_limit                        2.
% 3.32/0.97  --res_out_proof                         true
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Options
% 3.32/0.97  
% 3.32/0.97  --superposition_flag                    true
% 3.32/0.97  --sup_passive_queue_type                priority_queues
% 3.32/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.97  --demod_completeness_check              fast
% 3.32/0.97  --demod_use_ground                      true
% 3.32/0.97  --sup_to_prop_solver                    passive
% 3.32/0.97  --sup_prop_simpl_new                    true
% 3.32/0.97  --sup_prop_simpl_given                  true
% 3.32/0.97  --sup_fun_splitting                     false
% 3.32/0.97  --sup_smt_interval                      50000
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Simplification Setup
% 3.32/0.97  
% 3.32/0.97  --sup_indices_passive                   []
% 3.32/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.97  --sup_full_bw                           [BwDemod]
% 3.32/0.97  --sup_immed_triv                        [TrivRules]
% 3.32/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.97  --sup_immed_bw_main                     []
% 3.32/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.97  
% 3.32/0.97  ------ Combination Options
% 3.32/0.97  
% 3.32/0.97  --comb_res_mult                         3
% 3.32/0.97  --comb_sup_mult                         2
% 3.32/0.97  --comb_inst_mult                        10
% 3.32/0.97  
% 3.32/0.97  ------ Debug Options
% 3.32/0.97  
% 3.32/0.97  --dbg_backtrace                         false
% 3.32/0.97  --dbg_dump_prop_clauses                 false
% 3.32/0.97  --dbg_dump_prop_clauses_file            -
% 3.32/0.97  --dbg_out_stat                          false
% 3.32/0.97  ------ Parsing...
% 3.32/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.97  ------ Proving...
% 3.32/0.97  ------ Problem Properties 
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  clauses                                 12
% 3.32/0.97  conjectures                             2
% 3.32/0.97  EPR                                     1
% 3.32/0.97  Horn                                    11
% 3.32/0.97  unary                                   10
% 3.32/0.97  binary                                  2
% 3.32/0.97  lits                                    14
% 3.32/0.97  lits eq                                 9
% 3.32/0.97  fd_pure                                 0
% 3.32/0.97  fd_pseudo                               0
% 3.32/0.97  fd_cond                                 1
% 3.32/0.97  fd_pseudo_cond                          0
% 3.32/0.97  AC symbols                              0
% 3.32/0.97  
% 3.32/0.97  ------ Schedule dynamic 5 is on 
% 3.32/0.97  
% 3.32/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  ------ 
% 3.32/0.97  Current options:
% 3.32/0.97  ------ 
% 3.32/0.97  
% 3.32/0.97  ------ Input Options
% 3.32/0.97  
% 3.32/0.97  --out_options                           all
% 3.32/0.97  --tptp_safe_out                         true
% 3.32/0.97  --problem_path                          ""
% 3.32/0.97  --include_path                          ""
% 3.32/0.97  --clausifier                            res/vclausify_rel
% 3.32/0.97  --clausifier_options                    --mode clausify
% 3.32/0.97  --stdin                                 false
% 3.32/0.97  --stats_out                             all
% 3.32/0.97  
% 3.32/0.97  ------ General Options
% 3.32/0.97  
% 3.32/0.97  --fof                                   false
% 3.32/0.97  --time_out_real                         305.
% 3.32/0.97  --time_out_virtual                      -1.
% 3.32/0.97  --symbol_type_check                     false
% 3.32/0.97  --clausify_out                          false
% 3.32/0.97  --sig_cnt_out                           false
% 3.32/0.97  --trig_cnt_out                          false
% 3.32/0.97  --trig_cnt_out_tolerance                1.
% 3.32/0.97  --trig_cnt_out_sk_spl                   false
% 3.32/0.97  --abstr_cl_out                          false
% 3.32/0.97  
% 3.32/0.97  ------ Global Options
% 3.32/0.97  
% 3.32/0.97  --schedule                              default
% 3.32/0.97  --add_important_lit                     false
% 3.32/0.97  --prop_solver_per_cl                    1000
% 3.32/0.97  --min_unsat_core                        false
% 3.32/0.97  --soft_assumptions                      false
% 3.32/0.97  --soft_lemma_size                       3
% 3.32/0.97  --prop_impl_unit_size                   0
% 3.32/0.97  --prop_impl_unit                        []
% 3.32/0.97  --share_sel_clauses                     true
% 3.32/0.97  --reset_solvers                         false
% 3.32/0.97  --bc_imp_inh                            [conj_cone]
% 3.32/0.97  --conj_cone_tolerance                   3.
% 3.32/0.97  --extra_neg_conj                        none
% 3.32/0.97  --large_theory_mode                     true
% 3.32/0.97  --prolific_symb_bound                   200
% 3.32/0.97  --lt_threshold                          2000
% 3.32/0.97  --clause_weak_htbl                      true
% 3.32/0.97  --gc_record_bc_elim                     false
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing Options
% 3.32/0.97  
% 3.32/0.97  --preprocessing_flag                    true
% 3.32/0.97  --time_out_prep_mult                    0.1
% 3.32/0.97  --splitting_mode                        input
% 3.32/0.97  --splitting_grd                         true
% 3.32/0.97  --splitting_cvd                         false
% 3.32/0.97  --splitting_cvd_svl                     false
% 3.32/0.97  --splitting_nvd                         32
% 3.32/0.97  --sub_typing                            true
% 3.32/0.97  --prep_gs_sim                           true
% 3.32/0.97  --prep_unflatten                        true
% 3.32/0.97  --prep_res_sim                          true
% 3.32/0.97  --prep_upred                            true
% 3.32/0.97  --prep_sem_filter                       exhaustive
% 3.32/0.97  --prep_sem_filter_out                   false
% 3.32/0.97  --pred_elim                             true
% 3.32/0.97  --res_sim_input                         true
% 3.32/0.97  --eq_ax_congr_red                       true
% 3.32/0.97  --pure_diseq_elim                       true
% 3.32/0.97  --brand_transform                       false
% 3.32/0.97  --non_eq_to_eq                          false
% 3.32/0.97  --prep_def_merge                        true
% 3.32/0.97  --prep_def_merge_prop_impl              false
% 3.32/0.97  --prep_def_merge_mbd                    true
% 3.32/0.97  --prep_def_merge_tr_red                 false
% 3.32/0.97  --prep_def_merge_tr_cl                  false
% 3.32/0.97  --smt_preprocessing                     true
% 3.32/0.97  --smt_ac_axioms                         fast
% 3.32/0.97  --preprocessed_out                      false
% 3.32/0.97  --preprocessed_stats                    false
% 3.32/0.97  
% 3.32/0.97  ------ Abstraction refinement Options
% 3.32/0.97  
% 3.32/0.97  --abstr_ref                             []
% 3.32/0.97  --abstr_ref_prep                        false
% 3.32/0.97  --abstr_ref_until_sat                   false
% 3.32/0.97  --abstr_ref_sig_restrict                funpre
% 3.32/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.97  --abstr_ref_under                       []
% 3.32/0.97  
% 3.32/0.97  ------ SAT Options
% 3.32/0.97  
% 3.32/0.97  --sat_mode                              false
% 3.32/0.97  --sat_fm_restart_options                ""
% 3.32/0.97  --sat_gr_def                            false
% 3.32/0.97  --sat_epr_types                         true
% 3.32/0.97  --sat_non_cyclic_types                  false
% 3.32/0.97  --sat_finite_models                     false
% 3.32/0.97  --sat_fm_lemmas                         false
% 3.32/0.97  --sat_fm_prep                           false
% 3.32/0.97  --sat_fm_uc_incr                        true
% 3.32/0.97  --sat_out_model                         small
% 3.32/0.97  --sat_out_clauses                       false
% 3.32/0.97  
% 3.32/0.97  ------ QBF Options
% 3.32/0.97  
% 3.32/0.97  --qbf_mode                              false
% 3.32/0.97  --qbf_elim_univ                         false
% 3.32/0.97  --qbf_dom_inst                          none
% 3.32/0.97  --qbf_dom_pre_inst                      false
% 3.32/0.97  --qbf_sk_in                             false
% 3.32/0.97  --qbf_pred_elim                         true
% 3.32/0.97  --qbf_split                             512
% 3.32/0.97  
% 3.32/0.97  ------ BMC1 Options
% 3.32/0.97  
% 3.32/0.97  --bmc1_incremental                      false
% 3.32/0.97  --bmc1_axioms                           reachable_all
% 3.32/0.97  --bmc1_min_bound                        0
% 3.32/0.97  --bmc1_max_bound                        -1
% 3.32/0.97  --bmc1_max_bound_default                -1
% 3.32/0.97  --bmc1_symbol_reachability              true
% 3.32/0.97  --bmc1_property_lemmas                  false
% 3.32/0.97  --bmc1_k_induction                      false
% 3.32/0.97  --bmc1_non_equiv_states                 false
% 3.32/0.97  --bmc1_deadlock                         false
% 3.32/0.97  --bmc1_ucm                              false
% 3.32/0.97  --bmc1_add_unsat_core                   none
% 3.32/0.97  --bmc1_unsat_core_children              false
% 3.32/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.97  --bmc1_out_stat                         full
% 3.32/0.97  --bmc1_ground_init                      false
% 3.32/0.97  --bmc1_pre_inst_next_state              false
% 3.32/0.97  --bmc1_pre_inst_state                   false
% 3.32/0.97  --bmc1_pre_inst_reach_state             false
% 3.32/0.97  --bmc1_out_unsat_core                   false
% 3.32/0.97  --bmc1_aig_witness_out                  false
% 3.32/0.97  --bmc1_verbose                          false
% 3.32/0.97  --bmc1_dump_clauses_tptp                false
% 3.32/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.97  --bmc1_dump_file                        -
% 3.32/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.97  --bmc1_ucm_extend_mode                  1
% 3.32/0.97  --bmc1_ucm_init_mode                    2
% 3.32/0.97  --bmc1_ucm_cone_mode                    none
% 3.32/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.97  --bmc1_ucm_relax_model                  4
% 3.32/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.97  --bmc1_ucm_layered_model                none
% 3.32/0.97  --bmc1_ucm_max_lemma_size               10
% 3.32/0.97  
% 3.32/0.97  ------ AIG Options
% 3.32/0.97  
% 3.32/0.97  --aig_mode                              false
% 3.32/0.97  
% 3.32/0.97  ------ Instantiation Options
% 3.32/0.97  
% 3.32/0.97  --instantiation_flag                    true
% 3.32/0.97  --inst_sos_flag                         false
% 3.32/0.97  --inst_sos_phase                        true
% 3.32/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.97  --inst_lit_sel_side                     none
% 3.32/0.97  --inst_solver_per_active                1400
% 3.32/0.97  --inst_solver_calls_frac                1.
% 3.32/0.97  --inst_passive_queue_type               priority_queues
% 3.32/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.97  --inst_passive_queues_freq              [25;2]
% 3.32/0.97  --inst_dismatching                      true
% 3.32/0.97  --inst_eager_unprocessed_to_passive     true
% 3.32/0.97  --inst_prop_sim_given                   true
% 3.32/0.97  --inst_prop_sim_new                     false
% 3.32/0.97  --inst_subs_new                         false
% 3.32/0.97  --inst_eq_res_simp                      false
% 3.32/0.97  --inst_subs_given                       false
% 3.32/0.97  --inst_orphan_elimination               true
% 3.32/0.97  --inst_learning_loop_flag               true
% 3.32/0.97  --inst_learning_start                   3000
% 3.32/0.97  --inst_learning_factor                  2
% 3.32/0.97  --inst_start_prop_sim_after_learn       3
% 3.32/0.97  --inst_sel_renew                        solver
% 3.32/0.97  --inst_lit_activity_flag                true
% 3.32/0.97  --inst_restr_to_given                   false
% 3.32/0.97  --inst_activity_threshold               500
% 3.32/0.97  --inst_out_proof                        true
% 3.32/0.97  
% 3.32/0.97  ------ Resolution Options
% 3.32/0.97  
% 3.32/0.97  --resolution_flag                       false
% 3.32/0.97  --res_lit_sel                           adaptive
% 3.32/0.97  --res_lit_sel_side                      none
% 3.32/0.97  --res_ordering                          kbo
% 3.32/0.97  --res_to_prop_solver                    active
% 3.32/0.97  --res_prop_simpl_new                    false
% 3.32/0.97  --res_prop_simpl_given                  true
% 3.32/0.97  --res_passive_queue_type                priority_queues
% 3.32/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.97  --res_passive_queues_freq               [15;5]
% 3.32/0.97  --res_forward_subs                      full
% 3.32/0.97  --res_backward_subs                     full
% 3.32/0.97  --res_forward_subs_resolution           true
% 3.32/0.97  --res_backward_subs_resolution          true
% 3.32/0.97  --res_orphan_elimination                true
% 3.32/0.97  --res_time_limit                        2.
% 3.32/0.97  --res_out_proof                         true
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Options
% 3.32/0.97  
% 3.32/0.97  --superposition_flag                    true
% 3.32/0.97  --sup_passive_queue_type                priority_queues
% 3.32/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.97  --demod_completeness_check              fast
% 3.32/0.97  --demod_use_ground                      true
% 3.32/0.97  --sup_to_prop_solver                    passive
% 3.32/0.97  --sup_prop_simpl_new                    true
% 3.32/0.97  --sup_prop_simpl_given                  true
% 3.32/0.97  --sup_fun_splitting                     false
% 3.32/0.97  --sup_smt_interval                      50000
% 3.32/0.97  
% 3.32/0.97  ------ Superposition Simplification Setup
% 3.32/0.97  
% 3.32/0.97  --sup_indices_passive                   []
% 3.32/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.97  --sup_full_bw                           [BwDemod]
% 3.32/0.97  --sup_immed_triv                        [TrivRules]
% 3.32/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.97  --sup_immed_bw_main                     []
% 3.32/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.97  
% 3.32/0.97  ------ Combination Options
% 3.32/0.97  
% 3.32/0.97  --comb_res_mult                         3
% 3.32/0.97  --comb_sup_mult                         2
% 3.32/0.97  --comb_inst_mult                        10
% 3.32/0.97  
% 3.32/0.97  ------ Debug Options
% 3.32/0.97  
% 3.32/0.97  --dbg_backtrace                         false
% 3.32/0.97  --dbg_dump_prop_clauses                 false
% 3.32/0.97  --dbg_dump_prop_clauses_file            -
% 3.32/0.97  --dbg_out_stat                          false
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  ------ Proving...
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  % SZS status Theorem for theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  fof(f1,axiom,(
% 3.32/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f26,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f1])).
% 3.32/0.97  
% 3.32/0.97  fof(f11,conjecture,(
% 3.32/0.97    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f12,negated_conjecture,(
% 3.32/0.97    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.32/0.97    inference(negated_conjecture,[],[f11])).
% 3.32/0.97  
% 3.32/0.97  fof(f18,plain,(
% 3.32/0.97    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.32/0.97    inference(ennf_transformation,[],[f12])).
% 3.32/0.97  
% 3.32/0.97  fof(f19,plain,(
% 3.32/0.97    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.32/0.97    inference(flattening,[],[f18])).
% 3.32/0.97  
% 3.32/0.97  fof(f24,plain,(
% 3.32/0.97    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f25,plain,(
% 3.32/0.97    sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f24])).
% 3.32/0.97  
% 3.32/0.97  fof(f37,plain,(
% 3.32/0.97    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 3.32/0.97    inference(cnf_transformation,[],[f25])).
% 3.32/0.97  
% 3.32/0.97  fof(f4,axiom,(
% 3.32/0.97    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f16,plain,(
% 3.32/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.32/0.97    inference(ennf_transformation,[],[f4])).
% 3.32/0.97  
% 3.32/0.97  fof(f22,plain,(
% 3.32/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f23,plain,(
% 3.32/0.97    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f22])).
% 3.32/0.97  
% 3.32/0.97  fof(f30,plain,(
% 3.32/0.97    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.32/0.97    inference(cnf_transformation,[],[f23])).
% 3.32/0.97  
% 3.32/0.97  fof(f2,axiom,(
% 3.32/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f27,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f2])).
% 3.32/0.97  
% 3.32/0.97  fof(f9,axiom,(
% 3.32/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f35,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.32/0.97    inference(cnf_transformation,[],[f9])).
% 3.32/0.97  
% 3.32/0.97  fof(f41,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.32/0.97    inference(definition_unfolding,[],[f27,f35,f35])).
% 3.32/0.97  
% 3.32/0.97  fof(f3,axiom,(
% 3.32/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f13,plain,(
% 3.32/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(rectify,[],[f3])).
% 3.32/0.97  
% 3.32/0.97  fof(f15,plain,(
% 3.32/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(ennf_transformation,[],[f13])).
% 3.32/0.97  
% 3.32/0.97  fof(f20,plain,(
% 3.32/0.97    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.32/0.97    introduced(choice_axiom,[])).
% 3.32/0.97  
% 3.32/0.97  fof(f21,plain,(
% 3.32/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.32/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).
% 3.32/0.97  
% 3.32/0.97  fof(f29,plain,(
% 3.32/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.32/0.97    inference(cnf_transformation,[],[f21])).
% 3.32/0.97  
% 3.32/0.97  fof(f42,plain,(
% 3.32/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.32/0.97    inference(definition_unfolding,[],[f29,f35])).
% 3.32/0.97  
% 3.32/0.97  fof(f39,plain,(
% 3.32/0.97    r1_xboole_0(sK5,sK3)),
% 3.32/0.97    inference(cnf_transformation,[],[f25])).
% 3.32/0.97  
% 3.32/0.97  fof(f8,axiom,(
% 3.32/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f34,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.32/0.97    inference(cnf_transformation,[],[f8])).
% 3.32/0.97  
% 3.32/0.97  fof(f44,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.32/0.97    inference(definition_unfolding,[],[f34,f35])).
% 3.32/0.97  
% 3.32/0.97  fof(f6,axiom,(
% 3.32/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f32,plain,(
% 3.32/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.32/0.97    inference(cnf_transformation,[],[f6])).
% 3.32/0.97  
% 3.32/0.97  fof(f7,axiom,(
% 3.32/0.97    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f33,plain,(
% 3.32/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f7])).
% 3.32/0.97  
% 3.32/0.97  fof(f5,axiom,(
% 3.32/0.97    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f14,plain,(
% 3.32/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 3.32/0.97    inference(unused_predicate_definition_removal,[],[f5])).
% 3.32/0.97  
% 3.32/0.97  fof(f17,plain,(
% 3.32/0.97    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 3.32/0.97    inference(ennf_transformation,[],[f14])).
% 3.32/0.97  
% 3.32/0.97  fof(f31,plain,(
% 3.32/0.97    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.32/0.97    inference(cnf_transformation,[],[f17])).
% 3.32/0.97  
% 3.32/0.97  fof(f10,axiom,(
% 3.32/0.97    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.32/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.97  
% 3.32/0.97  fof(f36,plain,(
% 3.32/0.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.32/0.97    inference(cnf_transformation,[],[f10])).
% 3.32/0.97  
% 3.32/0.97  fof(f38,plain,(
% 3.32/0.97    r1_xboole_0(sK4,sK2)),
% 3.32/0.97    inference(cnf_transformation,[],[f25])).
% 3.32/0.97  
% 3.32/0.97  fof(f40,plain,(
% 3.32/0.97    sK3 != sK4),
% 3.32/0.97    inference(cnf_transformation,[],[f25])).
% 3.32/0.97  
% 3.32/0.97  cnf(c_0,plain,
% 3.32/0.97      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.32/0.97      inference(cnf_transformation,[],[f26]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_13,negated_conjecture,
% 3.32/0.97      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
% 3.32/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_267,plain,
% 3.32/0.97      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
% 3.32/0.97      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_4,plain,
% 3.32/0.97      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.32/0.97      inference(cnf_transformation,[],[f30]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_257,plain,
% 3.32/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.32/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_1,plain,
% 3.32/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.32/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2,plain,
% 3.32/0.97      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.32/0.97      | ~ r1_xboole_0(X1,X2) ),
% 3.32/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_11,negated_conjecture,
% 3.32/0.97      ( r1_xboole_0(sK5,sK3) ),
% 3.32/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_114,plain,
% 3.32/0.97      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.32/0.97      | sK5 != X1
% 3.32/0.97      | sK3 != X2 ),
% 3.32/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_115,plain,
% 3.32/0.97      ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
% 3.32/0.97      inference(unflattening,[status(thm)],[c_114]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_255,plain,
% 3.32/0.97      ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
% 3.32/0.97      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_284,plain,
% 3.32/0.97      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
% 3.32/0.97      inference(demodulation,[status(thm)],[c_1,c_255]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2427,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_257,c_284]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_8,plain,
% 3.32/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.32/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2967,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK5) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_2427,c_8]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_6,plain,
% 3.32/0.97      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.32/0.97      inference(cnf_transformation,[],[f32]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2972,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,sK5) = sK3 ),
% 3.32/0.97      inference(demodulation,[status(thm)],[c_2967,c_6]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_7,plain,
% 3.32/0.97      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.32/0.97      inference(cnf_transformation,[],[f33]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_3210,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK3,X0) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_2972,c_7]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_6212,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK5)) = k4_xboole_0(sK3,X0) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_0,c_3210]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_7768,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK3,sK4) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_267,c_6212]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_5,plain,
% 3.32/0.97      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.32/0.97      inference(cnf_transformation,[],[f31]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_9,plain,
% 3.32/0.97      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.32/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_95,plain,
% 3.32/0.97      ( X0 != X1
% 3.32/0.97      | k4_xboole_0(X1,X2) = k1_xboole_0
% 3.32/0.97      | k2_xboole_0(X0,X3) != X2 ),
% 3.32/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_96,plain,
% 3.32/0.97      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.32/0.97      inference(unflattening,[status(thm)],[c_95]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_7802,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 3.32/0.97      inference(demodulation,[status(thm)],[c_7768,c_96]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_534,plain,
% 3.32/0.97      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_7998,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_7802,c_534]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_12,negated_conjecture,
% 3.32/0.97      ( r1_xboole_0(sK4,sK2) ),
% 3.32/0.97      inference(cnf_transformation,[],[f38]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_123,plain,
% 3.32/0.97      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.32/0.97      | sK2 != X2
% 3.32/0.97      | sK4 != X1 ),
% 3.32/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_124,plain,
% 3.32/0.97      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
% 3.32/0.97      inference(unflattening,[status(thm)],[c_123]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_254,plain,
% 3.32/0.97      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
% 3.32/0.97      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2426,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_257,c_254]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2508,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK4,sK2) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_2426,c_8]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_2513,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,sK2) = sK4 ),
% 3.32/0.97      inference(demodulation,[status(thm)],[c_2508,c_6]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_3118,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK4,X0) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_2513,c_7]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_4836,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK4,X0) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_0,c_3118]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_491,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_267,c_96]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_7546,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_4836,c_491]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_8012,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
% 3.32/0.97      inference(light_normalisation,[status(thm)],[c_7998,c_7546]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_536,plain,
% 3.32/0.97      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 3.32/0.97      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_8013,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,X0) = k4_xboole_0(sK4,X0) ),
% 3.32/0.97      inference(demodulation,[status(thm)],[c_8012,c_7,c_536]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_8032,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_8013]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_173,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_315,plain,
% 3.32/0.97      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_173]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_699,plain,
% 3.32/0.97      ( k4_xboole_0(X0,X1) != X2 | sK4 != X2 | sK4 = k4_xboole_0(X0,X1) ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_315]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_1363,plain,
% 3.32/0.97      ( k4_xboole_0(X0,X1) != k4_xboole_0(sK4,k1_xboole_0)
% 3.32/0.97      | sK4 = k4_xboole_0(X0,X1)
% 3.32/0.97      | sK4 != k4_xboole_0(sK4,k1_xboole_0) ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_699]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_3912,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k1_xboole_0) != k4_xboole_0(sK4,k1_xboole_0)
% 3.32/0.97      | sK4 != k4_xboole_0(sK4,k1_xboole_0)
% 3.32/0.97      | sK4 = k4_xboole_0(sK3,k1_xboole_0) ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_1363]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_305,plain,
% 3.32/0.97      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_173]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_635,plain,
% 3.32/0.97      ( sK4 != k4_xboole_0(X0,X1)
% 3.32/0.97      | sK3 != k4_xboole_0(X0,X1)
% 3.32/0.97      | sK3 = sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_305]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_3152,plain,
% 3.32/0.97      ( sK4 != k4_xboole_0(sK3,k1_xboole_0)
% 3.32/0.97      | sK3 != k4_xboole_0(sK3,k1_xboole_0)
% 3.32/0.97      | sK3 = sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_635]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_1252,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_516,plain,
% 3.32/0.97      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_173]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_690,plain,
% 3.32/0.97      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_516]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_1251,plain,
% 3.32/0.97      ( k4_xboole_0(sK3,k1_xboole_0) != sK3
% 3.32/0.97      | sK3 = k4_xboole_0(sK3,k1_xboole_0)
% 3.32/0.97      | sK3 != sK3 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_690]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_172,plain,( X0 = X0 ),theory(equality) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_515,plain,
% 3.32/0.97      ( sK3 = sK3 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_172]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_415,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k1_xboole_0) = sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_344,plain,
% 3.32/0.97      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_315]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_414,plain,
% 3.32/0.97      ( k4_xboole_0(sK4,k1_xboole_0) != sK4
% 3.32/0.97      | sK4 = k4_xboole_0(sK4,k1_xboole_0)
% 3.32/0.97      | sK4 != sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_344]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_345,plain,
% 3.32/0.97      ( sK4 = sK4 ),
% 3.32/0.97      inference(instantiation,[status(thm)],[c_172]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(c_10,negated_conjecture,
% 3.32/0.97      ( sK3 != sK4 ),
% 3.32/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.32/0.97  
% 3.32/0.97  cnf(contradiction,plain,
% 3.32/0.97      ( $false ),
% 3.32/0.97      inference(minisat,
% 3.32/0.97                [status(thm)],
% 3.32/0.97                [c_8032,c_3912,c_3152,c_1252,c_1251,c_515,c_415,c_414,
% 3.32/0.97                 c_345,c_10]) ).
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.97  
% 3.32/0.97  ------                               Statistics
% 3.32/0.97  
% 3.32/0.97  ------ General
% 3.32/0.97  
% 3.32/0.97  abstr_ref_over_cycles:                  0
% 3.32/0.97  abstr_ref_under_cycles:                 0
% 3.32/0.97  gc_basic_clause_elim:                   0
% 3.32/0.97  forced_gc_time:                         0
% 3.32/0.97  parsing_time:                           0.007
% 3.32/0.97  unif_index_cands_time:                  0.
% 3.32/0.97  unif_index_add_time:                    0.
% 3.32/0.97  orderings_time:                         0.
% 3.32/0.97  out_proof_time:                         0.006
% 3.32/0.97  total_time:                             0.252
% 3.32/0.97  num_of_symbols:                         43
% 3.32/0.97  num_of_terms:                           11198
% 3.32/0.97  
% 3.32/0.97  ------ Preprocessing
% 3.32/0.97  
% 3.32/0.97  num_of_splits:                          0
% 3.32/0.97  num_of_split_atoms:                     0
% 3.32/0.97  num_of_reused_defs:                     0
% 3.32/0.97  num_eq_ax_congr_red:                    10
% 3.32/0.97  num_of_sem_filtered_clauses:            1
% 3.32/0.97  num_of_subtypes:                        0
% 3.32/0.97  monotx_restored_types:                  0
% 3.32/0.97  sat_num_of_epr_types:                   0
% 3.32/0.97  sat_num_of_non_cyclic_types:            0
% 3.32/0.97  sat_guarded_non_collapsed_types:        0
% 3.32/0.97  num_pure_diseq_elim:                    0
% 3.32/0.97  simp_replaced_by:                       0
% 3.32/0.97  res_preprocessed:                       61
% 3.32/0.97  prep_upred:                             0
% 3.32/0.97  prep_unflattend:                        8
% 3.32/0.97  smt_new_axioms:                         0
% 3.32/0.97  pred_elim_cands:                        1
% 3.32/0.97  pred_elim:                              2
% 3.32/0.97  pred_elim_cl:                           2
% 3.32/0.97  pred_elim_cycles:                       4
% 3.32/0.97  merged_defs:                            0
% 3.32/0.97  merged_defs_ncl:                        0
% 3.32/0.97  bin_hyper_res:                          0
% 3.32/0.97  prep_cycles:                            4
% 3.32/0.97  pred_elim_time:                         0.001
% 3.32/0.97  splitting_time:                         0.
% 3.32/0.97  sem_filter_time:                        0.
% 3.32/0.97  monotx_time:                            0.
% 3.32/0.97  subtype_inf_time:                       0.
% 3.32/0.97  
% 3.32/0.97  ------ Problem properties
% 3.32/0.97  
% 3.32/0.97  clauses:                                12
% 3.32/0.97  conjectures:                            2
% 3.32/0.97  epr:                                    1
% 3.32/0.97  horn:                                   11
% 3.32/0.97  ground:                                 2
% 3.32/0.97  unary:                                  10
% 3.32/0.97  binary:                                 2
% 3.32/0.97  lits:                                   14
% 3.32/0.97  lits_eq:                                9
% 3.32/0.97  fd_pure:                                0
% 3.32/0.97  fd_pseudo:                              0
% 3.32/0.97  fd_cond:                                1
% 3.32/0.97  fd_pseudo_cond:                         0
% 3.32/0.97  ac_symbols:                             0
% 3.32/0.97  
% 3.32/0.97  ------ Propositional Solver
% 3.32/0.97  
% 3.32/0.97  prop_solver_calls:                      31
% 3.32/0.97  prop_fast_solver_calls:                 278
% 3.32/0.97  smt_solver_calls:                       0
% 3.32/0.97  smt_fast_solver_calls:                  0
% 3.32/0.97  prop_num_of_clauses:                    2218
% 3.32/0.97  prop_preprocess_simplified:             3216
% 3.32/0.97  prop_fo_subsumed:                       0
% 3.32/0.97  prop_solver_time:                       0.
% 3.32/0.97  smt_solver_time:                        0.
% 3.32/0.97  smt_fast_solver_time:                   0.
% 3.32/0.97  prop_fast_solver_time:                  0.
% 3.32/0.97  prop_unsat_core_time:                   0.
% 3.32/0.97  
% 3.32/0.97  ------ QBF
% 3.32/0.97  
% 3.32/0.97  qbf_q_res:                              0
% 3.32/0.97  qbf_num_tautologies:                    0
% 3.32/0.97  qbf_prep_cycles:                        0
% 3.32/0.97  
% 3.32/0.97  ------ BMC1
% 3.32/0.97  
% 3.32/0.97  bmc1_current_bound:                     -1
% 3.32/0.97  bmc1_last_solved_bound:                 -1
% 3.32/0.97  bmc1_unsat_core_size:                   -1
% 3.32/0.97  bmc1_unsat_core_parents_size:           -1
% 3.32/0.97  bmc1_merge_next_fun:                    0
% 3.32/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.97  
% 3.32/0.97  ------ Instantiation
% 3.32/0.97  
% 3.32/0.97  inst_num_of_clauses:                    619
% 3.32/0.97  inst_num_in_passive:                    1
% 3.32/0.97  inst_num_in_active:                     367
% 3.32/0.97  inst_num_in_unprocessed:                251
% 3.32/0.97  inst_num_of_loops:                      450
% 3.32/0.97  inst_num_of_learning_restarts:          0
% 3.32/0.97  inst_num_moves_active_passive:          78
% 3.32/0.97  inst_lit_activity:                      0
% 3.32/0.97  inst_lit_activity_moves:                0
% 3.32/0.97  inst_num_tautologies:                   0
% 3.32/0.97  inst_num_prop_implied:                  0
% 3.32/0.97  inst_num_existing_simplified:           0
% 3.32/0.97  inst_num_eq_res_simplified:             0
% 3.32/0.97  inst_num_child_elim:                    0
% 3.32/0.97  inst_num_of_dismatching_blockings:      268
% 3.32/0.97  inst_num_of_non_proper_insts:           843
% 3.32/0.97  inst_num_of_duplicates:                 0
% 3.32/0.97  inst_inst_num_from_inst_to_res:         0
% 3.32/0.97  inst_dismatching_checking_time:         0.
% 3.32/0.97  
% 3.32/0.97  ------ Resolution
% 3.32/0.97  
% 3.32/0.97  res_num_of_clauses:                     0
% 3.32/0.97  res_num_in_passive:                     0
% 3.32/0.97  res_num_in_active:                      0
% 3.32/0.97  res_num_of_loops:                       65
% 3.32/0.97  res_forward_subset_subsumed:            58
% 3.32/0.97  res_backward_subset_subsumed:           0
% 3.32/0.97  res_forward_subsumed:                   0
% 3.32/0.97  res_backward_subsumed:                  0
% 3.32/0.97  res_forward_subsumption_resolution:     0
% 3.32/0.97  res_backward_subsumption_resolution:    0
% 3.32/0.97  res_clause_to_clause_subsumption:       3859
% 3.32/0.97  res_orphan_elimination:                 0
% 3.32/0.97  res_tautology_del:                      96
% 3.32/0.97  res_num_eq_res_simplified:              0
% 3.32/0.97  res_num_sel_changes:                    0
% 3.32/0.97  res_moves_from_active_to_pass:          0
% 3.32/0.97  
% 3.32/0.97  ------ Superposition
% 3.32/0.97  
% 3.32/0.97  sup_time_total:                         0.
% 3.32/0.97  sup_time_generating:                    0.
% 3.32/0.97  sup_time_sim_full:                      0.
% 3.32/0.97  sup_time_sim_immed:                     0.
% 3.32/0.97  
% 3.32/0.97  sup_num_of_clauses:                     575
% 3.32/0.97  sup_num_in_active:                      79
% 3.32/0.97  sup_num_in_passive:                     496
% 3.32/0.97  sup_num_of_loops:                       89
% 3.32/0.97  sup_fw_superposition:                   843
% 3.32/0.97  sup_bw_superposition:                   661
% 3.32/0.97  sup_immediate_simplified:               736
% 3.32/0.97  sup_given_eliminated:                   3
% 3.32/0.97  comparisons_done:                       0
% 3.32/0.97  comparisons_avoided:                    0
% 3.32/0.97  
% 3.32/0.97  ------ Simplifications
% 3.32/0.97  
% 3.32/0.97  
% 3.32/0.97  sim_fw_subset_subsumed:                 0
% 3.32/0.97  sim_bw_subset_subsumed:                 0
% 3.32/0.97  sim_fw_subsumed:                        124
% 3.32/0.97  sim_bw_subsumed:                        1
% 3.32/0.97  sim_fw_subsumption_res:                 0
% 3.32/0.97  sim_bw_subsumption_res:                 0
% 3.32/0.97  sim_tautology_del:                      0
% 3.32/0.97  sim_eq_tautology_del:                   153
% 3.32/0.97  sim_eq_res_simp:                        0
% 3.32/0.97  sim_fw_demodulated:                     306
% 3.32/0.97  sim_bw_demodulated:                     17
% 3.32/0.97  sim_light_normalised:                   426
% 3.32/0.97  sim_joinable_taut:                      0
% 3.32/0.97  sim_joinable_simp:                      0
% 3.32/0.97  sim_ac_normalised:                      0
% 3.32/0.97  sim_smt_subsumption:                    0
% 3.32/0.97  
%------------------------------------------------------------------------------
