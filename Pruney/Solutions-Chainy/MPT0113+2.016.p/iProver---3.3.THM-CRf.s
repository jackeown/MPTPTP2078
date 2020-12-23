%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:45 EST 2020

% Result     : Theorem 11.20s
% Output     : CNFRefutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 372 expanded)
%              Number of clauses        :   59 ( 156 expanded)
%              Number of leaves         :   16 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          :  157 ( 507 expanded)
%              Number of equality atoms :   90 ( 331 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f32,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f28,f24,f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_193,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_196,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_931,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_193,c_196])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_195,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_930,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_195,c_196])).

cnf(c_24562,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_930,c_930])).

cnf(c_24683,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_24562,c_930])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_24685,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24683,c_9])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_433,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_302,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_765,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_433,c_302])).

cnf(c_772,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_765])).

cnf(c_25590,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_24685,c_772])).

cnf(c_25758,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_25590,c_7])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_451,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_27504,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_25758,c_451])).

cnf(c_27528,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27504,c_9,c_302])).

cnf(c_27626,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_27528,c_930])).

cnf(c_27758,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_27626,c_27528])).

cnf(c_27760,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_27758,c_7])).

cnf(c_28511,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0),X1) ),
    inference(superposition,[status(thm)],[c_27760,c_772])).

cnf(c_28565,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_28511,c_930])).

cnf(c_28566,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28565,c_9])).

cnf(c_31331,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(superposition,[status(thm)],[c_28566,c_772])).

cnf(c_31396,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31331,c_7,c_9])).

cnf(c_48039,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_931,c_31396])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_27430,plain,
    ( r1_xboole_0(sK0,sK2)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_18007,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_560,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
    | X0 != k5_xboole_0(sK0,k1_xboole_0)
    | X1 != k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_2040,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | ~ r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
    | X0 != k5_xboole_0(sK0,k1_xboole_0)
    | k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_9263,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
    | r1_tarski(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | sK0 != k5_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_2041,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_74,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_505,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_581,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_918,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) != sK0
    | sK0 = k5_xboole_0(sK0,k1_xboole_0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_690,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_271,plain,
    ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
    | k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_424,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_294,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | X1 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | X0 != sK0 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_324,plain,
    ( r1_tarski(k5_xboole_0(sK0,k1_xboole_0),X0)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | X0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | k5_xboole_0(sK0,k1_xboole_0) != sK0 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_423,plain,
    ( r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | k5_xboole_0(sK0,k1_xboole_0) != sK0
    | k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_73,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_331,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_325,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48039,c_27430,c_18007,c_9263,c_2041,c_918,c_690,c_424,c_423,c_331,c_325,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:42:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.20/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.20/2.01  
% 11.20/2.01  ------  iProver source info
% 11.20/2.01  
% 11.20/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.20/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.20/2.01  git: non_committed_changes: false
% 11.20/2.01  git: last_make_outside_of_git: false
% 11.20/2.01  
% 11.20/2.01  ------ 
% 11.20/2.01  
% 11.20/2.01  ------ Input Options
% 11.20/2.01  
% 11.20/2.01  --out_options                           all
% 11.20/2.01  --tptp_safe_out                         true
% 11.20/2.01  --problem_path                          ""
% 11.20/2.01  --include_path                          ""
% 11.20/2.01  --clausifier                            res/vclausify_rel
% 11.20/2.01  --clausifier_options                    --mode clausify
% 11.20/2.01  --stdin                                 false
% 11.20/2.01  --stats_out                             sel
% 11.20/2.01  
% 11.20/2.01  ------ General Options
% 11.20/2.01  
% 11.20/2.01  --fof                                   false
% 11.20/2.01  --time_out_real                         604.98
% 11.20/2.01  --time_out_virtual                      -1.
% 11.20/2.01  --symbol_type_check                     false
% 11.20/2.01  --clausify_out                          false
% 11.20/2.01  --sig_cnt_out                           false
% 11.20/2.01  --trig_cnt_out                          false
% 11.20/2.01  --trig_cnt_out_tolerance                1.
% 11.20/2.01  --trig_cnt_out_sk_spl                   false
% 11.20/2.01  --abstr_cl_out                          false
% 11.20/2.01  
% 11.20/2.01  ------ Global Options
% 11.20/2.01  
% 11.20/2.01  --schedule                              none
% 11.20/2.01  --add_important_lit                     false
% 11.20/2.01  --prop_solver_per_cl                    1000
% 11.20/2.01  --min_unsat_core                        false
% 11.20/2.01  --soft_assumptions                      false
% 11.20/2.01  --soft_lemma_size                       3
% 11.20/2.01  --prop_impl_unit_size                   0
% 11.20/2.01  --prop_impl_unit                        []
% 11.20/2.01  --share_sel_clauses                     true
% 11.20/2.01  --reset_solvers                         false
% 11.20/2.01  --bc_imp_inh                            [conj_cone]
% 11.20/2.01  --conj_cone_tolerance                   3.
% 11.20/2.01  --extra_neg_conj                        none
% 11.20/2.01  --large_theory_mode                     true
% 11.20/2.01  --prolific_symb_bound                   200
% 11.20/2.01  --lt_threshold                          2000
% 11.20/2.01  --clause_weak_htbl                      true
% 11.20/2.01  --gc_record_bc_elim                     false
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing Options
% 11.20/2.01  
% 11.20/2.01  --preprocessing_flag                    true
% 11.20/2.01  --time_out_prep_mult                    0.1
% 11.20/2.01  --splitting_mode                        input
% 11.20/2.01  --splitting_grd                         true
% 11.20/2.01  --splitting_cvd                         false
% 11.20/2.01  --splitting_cvd_svl                     false
% 11.20/2.01  --splitting_nvd                         32
% 11.20/2.01  --sub_typing                            true
% 11.20/2.01  --prep_gs_sim                           false
% 11.20/2.01  --prep_unflatten                        true
% 11.20/2.01  --prep_res_sim                          true
% 11.20/2.01  --prep_upred                            true
% 11.20/2.01  --prep_sem_filter                       exhaustive
% 11.20/2.01  --prep_sem_filter_out                   false
% 11.20/2.01  --pred_elim                             false
% 11.20/2.01  --res_sim_input                         true
% 11.20/2.01  --eq_ax_congr_red                       true
% 11.20/2.01  --pure_diseq_elim                       true
% 11.20/2.01  --brand_transform                       false
% 11.20/2.01  --non_eq_to_eq                          false
% 11.20/2.01  --prep_def_merge                        true
% 11.20/2.01  --prep_def_merge_prop_impl              false
% 11.20/2.01  --prep_def_merge_mbd                    true
% 11.20/2.01  --prep_def_merge_tr_red                 false
% 11.20/2.01  --prep_def_merge_tr_cl                  false
% 11.20/2.01  --smt_preprocessing                     true
% 11.20/2.01  --smt_ac_axioms                         fast
% 11.20/2.01  --preprocessed_out                      false
% 11.20/2.01  --preprocessed_stats                    false
% 11.20/2.01  
% 11.20/2.01  ------ Abstraction refinement Options
% 11.20/2.01  
% 11.20/2.01  --abstr_ref                             []
% 11.20/2.01  --abstr_ref_prep                        false
% 11.20/2.01  --abstr_ref_until_sat                   false
% 11.20/2.01  --abstr_ref_sig_restrict                funpre
% 11.20/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.20/2.01  --abstr_ref_under                       []
% 11.20/2.01  
% 11.20/2.01  ------ SAT Options
% 11.20/2.01  
% 11.20/2.01  --sat_mode                              false
% 11.20/2.01  --sat_fm_restart_options                ""
% 11.20/2.01  --sat_gr_def                            false
% 11.20/2.01  --sat_epr_types                         true
% 11.20/2.01  --sat_non_cyclic_types                  false
% 11.20/2.01  --sat_finite_models                     false
% 11.20/2.01  --sat_fm_lemmas                         false
% 11.20/2.01  --sat_fm_prep                           false
% 11.20/2.01  --sat_fm_uc_incr                        true
% 11.20/2.01  --sat_out_model                         small
% 11.20/2.01  --sat_out_clauses                       false
% 11.20/2.01  
% 11.20/2.01  ------ QBF Options
% 11.20/2.01  
% 11.20/2.01  --qbf_mode                              false
% 11.20/2.01  --qbf_elim_univ                         false
% 11.20/2.01  --qbf_dom_inst                          none
% 11.20/2.01  --qbf_dom_pre_inst                      false
% 11.20/2.01  --qbf_sk_in                             false
% 11.20/2.01  --qbf_pred_elim                         true
% 11.20/2.01  --qbf_split                             512
% 11.20/2.01  
% 11.20/2.01  ------ BMC1 Options
% 11.20/2.01  
% 11.20/2.01  --bmc1_incremental                      false
% 11.20/2.01  --bmc1_axioms                           reachable_all
% 11.20/2.01  --bmc1_min_bound                        0
% 11.20/2.01  --bmc1_max_bound                        -1
% 11.20/2.01  --bmc1_max_bound_default                -1
% 11.20/2.01  --bmc1_symbol_reachability              true
% 11.20/2.01  --bmc1_property_lemmas                  false
% 11.20/2.01  --bmc1_k_induction                      false
% 11.20/2.01  --bmc1_non_equiv_states                 false
% 11.20/2.01  --bmc1_deadlock                         false
% 11.20/2.01  --bmc1_ucm                              false
% 11.20/2.01  --bmc1_add_unsat_core                   none
% 11.20/2.01  --bmc1_unsat_core_children              false
% 11.20/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.20/2.01  --bmc1_out_stat                         full
% 11.20/2.01  --bmc1_ground_init                      false
% 11.20/2.01  --bmc1_pre_inst_next_state              false
% 11.20/2.01  --bmc1_pre_inst_state                   false
% 11.20/2.01  --bmc1_pre_inst_reach_state             false
% 11.20/2.01  --bmc1_out_unsat_core                   false
% 11.20/2.01  --bmc1_aig_witness_out                  false
% 11.20/2.01  --bmc1_verbose                          false
% 11.20/2.01  --bmc1_dump_clauses_tptp                false
% 11.20/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.20/2.01  --bmc1_dump_file                        -
% 11.20/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.20/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.20/2.01  --bmc1_ucm_extend_mode                  1
% 11.20/2.01  --bmc1_ucm_init_mode                    2
% 11.20/2.01  --bmc1_ucm_cone_mode                    none
% 11.20/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.20/2.01  --bmc1_ucm_relax_model                  4
% 11.20/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.20/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.20/2.01  --bmc1_ucm_layered_model                none
% 11.20/2.01  --bmc1_ucm_max_lemma_size               10
% 11.20/2.01  
% 11.20/2.01  ------ AIG Options
% 11.20/2.01  
% 11.20/2.01  --aig_mode                              false
% 11.20/2.01  
% 11.20/2.01  ------ Instantiation Options
% 11.20/2.01  
% 11.20/2.01  --instantiation_flag                    true
% 11.20/2.01  --inst_sos_flag                         false
% 11.20/2.01  --inst_sos_phase                        true
% 11.20/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel_side                     num_symb
% 11.20/2.01  --inst_solver_per_active                1400
% 11.20/2.01  --inst_solver_calls_frac                1.
% 11.20/2.01  --inst_passive_queue_type               priority_queues
% 11.20/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.20/2.01  --inst_passive_queues_freq              [25;2]
% 11.20/2.01  --inst_dismatching                      true
% 11.20/2.01  --inst_eager_unprocessed_to_passive     true
% 11.20/2.01  --inst_prop_sim_given                   true
% 11.20/2.01  --inst_prop_sim_new                     false
% 11.20/2.01  --inst_subs_new                         false
% 11.20/2.01  --inst_eq_res_simp                      false
% 11.20/2.01  --inst_subs_given                       false
% 11.20/2.01  --inst_orphan_elimination               true
% 11.20/2.01  --inst_learning_loop_flag               true
% 11.20/2.01  --inst_learning_start                   3000
% 11.20/2.01  --inst_learning_factor                  2
% 11.20/2.01  --inst_start_prop_sim_after_learn       3
% 11.20/2.01  --inst_sel_renew                        solver
% 11.20/2.01  --inst_lit_activity_flag                true
% 11.20/2.01  --inst_restr_to_given                   false
% 11.20/2.01  --inst_activity_threshold               500
% 11.20/2.01  --inst_out_proof                        true
% 11.20/2.01  
% 11.20/2.01  ------ Resolution Options
% 11.20/2.01  
% 11.20/2.01  --resolution_flag                       true
% 11.20/2.01  --res_lit_sel                           adaptive
% 11.20/2.01  --res_lit_sel_side                      none
% 11.20/2.01  --res_ordering                          kbo
% 11.20/2.01  --res_to_prop_solver                    active
% 11.20/2.01  --res_prop_simpl_new                    false
% 11.20/2.01  --res_prop_simpl_given                  true
% 11.20/2.01  --res_passive_queue_type                priority_queues
% 11.20/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.20/2.01  --res_passive_queues_freq               [15;5]
% 11.20/2.01  --res_forward_subs                      full
% 11.20/2.01  --res_backward_subs                     full
% 11.20/2.01  --res_forward_subs_resolution           true
% 11.20/2.01  --res_backward_subs_resolution          true
% 11.20/2.01  --res_orphan_elimination                true
% 11.20/2.01  --res_time_limit                        2.
% 11.20/2.01  --res_out_proof                         true
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Options
% 11.20/2.01  
% 11.20/2.01  --superposition_flag                    true
% 11.20/2.01  --sup_passive_queue_type                priority_queues
% 11.20/2.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.20/2.01  --sup_passive_queues_freq               [1;4]
% 11.20/2.01  --demod_completeness_check              fast
% 11.20/2.01  --demod_use_ground                      true
% 11.20/2.01  --sup_to_prop_solver                    passive
% 11.20/2.01  --sup_prop_simpl_new                    true
% 11.20/2.01  --sup_prop_simpl_given                  true
% 11.20/2.01  --sup_fun_splitting                     false
% 11.20/2.01  --sup_smt_interval                      50000
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Simplification Setup
% 11.20/2.01  
% 11.20/2.01  --sup_indices_passive                   []
% 11.20/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.20/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.20/2.01  --sup_full_bw                           [BwDemod]
% 11.20/2.01  --sup_immed_triv                        [TrivRules]
% 11.20/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.20/2.01  --sup_immed_bw_main                     []
% 11.20/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.20/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.20/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.20/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.20/2.01  
% 11.20/2.01  ------ Combination Options
% 11.20/2.01  
% 11.20/2.01  --comb_res_mult                         3
% 11.20/2.01  --comb_sup_mult                         2
% 11.20/2.01  --comb_inst_mult                        10
% 11.20/2.01  
% 11.20/2.01  ------ Debug Options
% 11.20/2.01  
% 11.20/2.01  --dbg_backtrace                         false
% 11.20/2.01  --dbg_dump_prop_clauses                 false
% 11.20/2.01  --dbg_dump_prop_clauses_file            -
% 11.20/2.01  --dbg_out_stat                          false
% 11.20/2.01  ------ Parsing...
% 11.20/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.20/2.01  ------ Proving...
% 11.20/2.01  ------ Problem Properties 
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  clauses                                 12
% 11.20/2.01  conjectures                             2
% 11.20/2.01  EPR                                     1
% 11.20/2.01  Horn                                    12
% 11.20/2.01  unary                                   8
% 11.20/2.01  binary                                  4
% 11.20/2.01  lits                                    16
% 11.20/2.01  lits eq                                 8
% 11.20/2.01  fd_pure                                 0
% 11.20/2.01  fd_pseudo                               0
% 11.20/2.01  fd_cond                                 0
% 11.20/2.01  fd_pseudo_cond                          0
% 11.20/2.01  AC symbols                              1
% 11.20/2.01  
% 11.20/2.01  ------ Input Options Time Limit: Unbounded
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  ------ 
% 11.20/2.01  Current options:
% 11.20/2.01  ------ 
% 11.20/2.01  
% 11.20/2.01  ------ Input Options
% 11.20/2.01  
% 11.20/2.01  --out_options                           all
% 11.20/2.01  --tptp_safe_out                         true
% 11.20/2.01  --problem_path                          ""
% 11.20/2.01  --include_path                          ""
% 11.20/2.01  --clausifier                            res/vclausify_rel
% 11.20/2.01  --clausifier_options                    --mode clausify
% 11.20/2.01  --stdin                                 false
% 11.20/2.01  --stats_out                             sel
% 11.20/2.01  
% 11.20/2.01  ------ General Options
% 11.20/2.01  
% 11.20/2.01  --fof                                   false
% 11.20/2.01  --time_out_real                         604.98
% 11.20/2.01  --time_out_virtual                      -1.
% 11.20/2.01  --symbol_type_check                     false
% 11.20/2.01  --clausify_out                          false
% 11.20/2.01  --sig_cnt_out                           false
% 11.20/2.01  --trig_cnt_out                          false
% 11.20/2.01  --trig_cnt_out_tolerance                1.
% 11.20/2.01  --trig_cnt_out_sk_spl                   false
% 11.20/2.01  --abstr_cl_out                          false
% 11.20/2.01  
% 11.20/2.01  ------ Global Options
% 11.20/2.01  
% 11.20/2.01  --schedule                              none
% 11.20/2.01  --add_important_lit                     false
% 11.20/2.01  --prop_solver_per_cl                    1000
% 11.20/2.01  --min_unsat_core                        false
% 11.20/2.01  --soft_assumptions                      false
% 11.20/2.01  --soft_lemma_size                       3
% 11.20/2.01  --prop_impl_unit_size                   0
% 11.20/2.01  --prop_impl_unit                        []
% 11.20/2.01  --share_sel_clauses                     true
% 11.20/2.01  --reset_solvers                         false
% 11.20/2.01  --bc_imp_inh                            [conj_cone]
% 11.20/2.01  --conj_cone_tolerance                   3.
% 11.20/2.01  --extra_neg_conj                        none
% 11.20/2.01  --large_theory_mode                     true
% 11.20/2.01  --prolific_symb_bound                   200
% 11.20/2.01  --lt_threshold                          2000
% 11.20/2.01  --clause_weak_htbl                      true
% 11.20/2.01  --gc_record_bc_elim                     false
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing Options
% 11.20/2.01  
% 11.20/2.01  --preprocessing_flag                    true
% 11.20/2.01  --time_out_prep_mult                    0.1
% 11.20/2.01  --splitting_mode                        input
% 11.20/2.01  --splitting_grd                         true
% 11.20/2.01  --splitting_cvd                         false
% 11.20/2.01  --splitting_cvd_svl                     false
% 11.20/2.01  --splitting_nvd                         32
% 11.20/2.01  --sub_typing                            true
% 11.20/2.01  --prep_gs_sim                           false
% 11.20/2.01  --prep_unflatten                        true
% 11.20/2.01  --prep_res_sim                          true
% 11.20/2.01  --prep_upred                            true
% 11.20/2.01  --prep_sem_filter                       exhaustive
% 11.20/2.01  --prep_sem_filter_out                   false
% 11.20/2.01  --pred_elim                             false
% 11.20/2.01  --res_sim_input                         true
% 11.20/2.01  --eq_ax_congr_red                       true
% 11.20/2.01  --pure_diseq_elim                       true
% 11.20/2.01  --brand_transform                       false
% 11.20/2.01  --non_eq_to_eq                          false
% 11.20/2.01  --prep_def_merge                        true
% 11.20/2.01  --prep_def_merge_prop_impl              false
% 11.20/2.01  --prep_def_merge_mbd                    true
% 11.20/2.01  --prep_def_merge_tr_red                 false
% 11.20/2.01  --prep_def_merge_tr_cl                  false
% 11.20/2.01  --smt_preprocessing                     true
% 11.20/2.01  --smt_ac_axioms                         fast
% 11.20/2.01  --preprocessed_out                      false
% 11.20/2.01  --preprocessed_stats                    false
% 11.20/2.01  
% 11.20/2.01  ------ Abstraction refinement Options
% 11.20/2.01  
% 11.20/2.01  --abstr_ref                             []
% 11.20/2.01  --abstr_ref_prep                        false
% 11.20/2.01  --abstr_ref_until_sat                   false
% 11.20/2.01  --abstr_ref_sig_restrict                funpre
% 11.20/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.20/2.01  --abstr_ref_under                       []
% 11.20/2.01  
% 11.20/2.01  ------ SAT Options
% 11.20/2.01  
% 11.20/2.01  --sat_mode                              false
% 11.20/2.01  --sat_fm_restart_options                ""
% 11.20/2.01  --sat_gr_def                            false
% 11.20/2.01  --sat_epr_types                         true
% 11.20/2.01  --sat_non_cyclic_types                  false
% 11.20/2.01  --sat_finite_models                     false
% 11.20/2.01  --sat_fm_lemmas                         false
% 11.20/2.01  --sat_fm_prep                           false
% 11.20/2.01  --sat_fm_uc_incr                        true
% 11.20/2.01  --sat_out_model                         small
% 11.20/2.01  --sat_out_clauses                       false
% 11.20/2.01  
% 11.20/2.01  ------ QBF Options
% 11.20/2.01  
% 11.20/2.01  --qbf_mode                              false
% 11.20/2.01  --qbf_elim_univ                         false
% 11.20/2.01  --qbf_dom_inst                          none
% 11.20/2.01  --qbf_dom_pre_inst                      false
% 11.20/2.01  --qbf_sk_in                             false
% 11.20/2.01  --qbf_pred_elim                         true
% 11.20/2.01  --qbf_split                             512
% 11.20/2.01  
% 11.20/2.01  ------ BMC1 Options
% 11.20/2.01  
% 11.20/2.01  --bmc1_incremental                      false
% 11.20/2.01  --bmc1_axioms                           reachable_all
% 11.20/2.01  --bmc1_min_bound                        0
% 11.20/2.01  --bmc1_max_bound                        -1
% 11.20/2.01  --bmc1_max_bound_default                -1
% 11.20/2.01  --bmc1_symbol_reachability              true
% 11.20/2.01  --bmc1_property_lemmas                  false
% 11.20/2.01  --bmc1_k_induction                      false
% 11.20/2.01  --bmc1_non_equiv_states                 false
% 11.20/2.01  --bmc1_deadlock                         false
% 11.20/2.01  --bmc1_ucm                              false
% 11.20/2.01  --bmc1_add_unsat_core                   none
% 11.20/2.01  --bmc1_unsat_core_children              false
% 11.20/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.20/2.01  --bmc1_out_stat                         full
% 11.20/2.01  --bmc1_ground_init                      false
% 11.20/2.01  --bmc1_pre_inst_next_state              false
% 11.20/2.01  --bmc1_pre_inst_state                   false
% 11.20/2.01  --bmc1_pre_inst_reach_state             false
% 11.20/2.01  --bmc1_out_unsat_core                   false
% 11.20/2.01  --bmc1_aig_witness_out                  false
% 11.20/2.01  --bmc1_verbose                          false
% 11.20/2.01  --bmc1_dump_clauses_tptp                false
% 11.20/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.20/2.01  --bmc1_dump_file                        -
% 11.20/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.20/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.20/2.01  --bmc1_ucm_extend_mode                  1
% 11.20/2.01  --bmc1_ucm_init_mode                    2
% 11.20/2.01  --bmc1_ucm_cone_mode                    none
% 11.20/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.20/2.01  --bmc1_ucm_relax_model                  4
% 11.20/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.20/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.20/2.01  --bmc1_ucm_layered_model                none
% 11.20/2.01  --bmc1_ucm_max_lemma_size               10
% 11.20/2.01  
% 11.20/2.01  ------ AIG Options
% 11.20/2.01  
% 11.20/2.01  --aig_mode                              false
% 11.20/2.01  
% 11.20/2.01  ------ Instantiation Options
% 11.20/2.01  
% 11.20/2.01  --instantiation_flag                    true
% 11.20/2.01  --inst_sos_flag                         false
% 11.20/2.01  --inst_sos_phase                        true
% 11.20/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel_side                     num_symb
% 11.20/2.01  --inst_solver_per_active                1400
% 11.20/2.01  --inst_solver_calls_frac                1.
% 11.20/2.01  --inst_passive_queue_type               priority_queues
% 11.20/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.20/2.01  --inst_passive_queues_freq              [25;2]
% 11.20/2.01  --inst_dismatching                      true
% 11.20/2.01  --inst_eager_unprocessed_to_passive     true
% 11.20/2.01  --inst_prop_sim_given                   true
% 11.20/2.01  --inst_prop_sim_new                     false
% 11.20/2.01  --inst_subs_new                         false
% 11.20/2.01  --inst_eq_res_simp                      false
% 11.20/2.01  --inst_subs_given                       false
% 11.20/2.01  --inst_orphan_elimination               true
% 11.20/2.01  --inst_learning_loop_flag               true
% 11.20/2.01  --inst_learning_start                   3000
% 11.20/2.01  --inst_learning_factor                  2
% 11.20/2.01  --inst_start_prop_sim_after_learn       3
% 11.20/2.01  --inst_sel_renew                        solver
% 11.20/2.01  --inst_lit_activity_flag                true
% 11.20/2.01  --inst_restr_to_given                   false
% 11.20/2.01  --inst_activity_threshold               500
% 11.20/2.01  --inst_out_proof                        true
% 11.20/2.01  
% 11.20/2.01  ------ Resolution Options
% 11.20/2.01  
% 11.20/2.01  --resolution_flag                       true
% 11.20/2.01  --res_lit_sel                           adaptive
% 11.20/2.01  --res_lit_sel_side                      none
% 11.20/2.01  --res_ordering                          kbo
% 11.20/2.01  --res_to_prop_solver                    active
% 11.20/2.01  --res_prop_simpl_new                    false
% 11.20/2.01  --res_prop_simpl_given                  true
% 11.20/2.01  --res_passive_queue_type                priority_queues
% 11.20/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.20/2.01  --res_passive_queues_freq               [15;5]
% 11.20/2.01  --res_forward_subs                      full
% 11.20/2.01  --res_backward_subs                     full
% 11.20/2.01  --res_forward_subs_resolution           true
% 11.20/2.01  --res_backward_subs_resolution          true
% 11.20/2.01  --res_orphan_elimination                true
% 11.20/2.01  --res_time_limit                        2.
% 11.20/2.01  --res_out_proof                         true
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Options
% 11.20/2.01  
% 11.20/2.01  --superposition_flag                    true
% 11.20/2.01  --sup_passive_queue_type                priority_queues
% 11.20/2.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.20/2.01  --sup_passive_queues_freq               [1;4]
% 11.20/2.01  --demod_completeness_check              fast
% 11.20/2.01  --demod_use_ground                      true
% 11.20/2.01  --sup_to_prop_solver                    passive
% 11.20/2.01  --sup_prop_simpl_new                    true
% 11.20/2.01  --sup_prop_simpl_given                  true
% 11.20/2.01  --sup_fun_splitting                     false
% 11.20/2.01  --sup_smt_interval                      50000
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Simplification Setup
% 11.20/2.01  
% 11.20/2.01  --sup_indices_passive                   []
% 11.20/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.20/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.20/2.01  --sup_full_bw                           [BwDemod]
% 11.20/2.01  --sup_immed_triv                        [TrivRules]
% 11.20/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.20/2.01  --sup_immed_bw_main                     []
% 11.20/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.20/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.20/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.20/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.20/2.01  
% 11.20/2.01  ------ Combination Options
% 11.20/2.01  
% 11.20/2.01  --comb_res_mult                         3
% 11.20/2.01  --comb_sup_mult                         2
% 11.20/2.01  --comb_inst_mult                        10
% 11.20/2.01  
% 11.20/2.01  ------ Debug Options
% 11.20/2.01  
% 11.20/2.01  --dbg_backtrace                         false
% 11.20/2.01  --dbg_dump_prop_clauses                 false
% 11.20/2.01  --dbg_dump_prop_clauses_file            -
% 11.20/2.01  --dbg_out_stat                          false
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  ------ Proving...
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  % SZS status Theorem for theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  fof(f12,conjecture,(
% 11.20/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f13,negated_conjecture,(
% 11.20/2.01    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.20/2.01    inference(negated_conjecture,[],[f12])).
% 11.20/2.01  
% 11.20/2.01  fof(f18,plain,(
% 11.20/2.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.20/2.01    inference(ennf_transformation,[],[f13])).
% 11.20/2.01  
% 11.20/2.01  fof(f19,plain,(
% 11.20/2.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 11.20/2.01    introduced(choice_axiom,[])).
% 11.20/2.01  
% 11.20/2.01  fof(f20,plain,(
% 11.20/2.01    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 11.20/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 11.20/2.01  
% 11.20/2.01  fof(f32,plain,(
% 11.20/2.01    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 11.20/2.01    inference(cnf_transformation,[],[f20])).
% 11.20/2.01  
% 11.20/2.01  fof(f4,axiom,(
% 11.20/2.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f24,plain,(
% 11.20/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f4])).
% 11.20/2.01  
% 11.20/2.01  fof(f36,plain,(
% 11.20/2.01    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 11.20/2.01    inference(definition_unfolding,[],[f32,f24])).
% 11.20/2.01  
% 11.20/2.01  fof(f6,axiom,(
% 11.20/2.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f17,plain,(
% 11.20/2.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.20/2.01    inference(ennf_transformation,[],[f6])).
% 11.20/2.01  
% 11.20/2.01  fof(f26,plain,(
% 11.20/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f17])).
% 11.20/2.01  
% 11.20/2.01  fof(f7,axiom,(
% 11.20/2.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f27,plain,(
% 11.20/2.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f7])).
% 11.20/2.01  
% 11.20/2.01  fof(f34,plain,(
% 11.20/2.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.20/2.01    inference(definition_unfolding,[],[f27,f24])).
% 11.20/2.01  
% 11.20/2.01  fof(f11,axiom,(
% 11.20/2.01    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f31,plain,(
% 11.20/2.01    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.20/2.01    inference(cnf_transformation,[],[f11])).
% 11.20/2.01  
% 11.20/2.01  fof(f8,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f28,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f8])).
% 11.20/2.01  
% 11.20/2.01  fof(f35,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 11.20/2.01    inference(definition_unfolding,[],[f28,f24,f24])).
% 11.20/2.01  
% 11.20/2.01  fof(f10,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f30,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f10])).
% 11.20/2.01  
% 11.20/2.01  fof(f9,axiom,(
% 11.20/2.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f29,plain,(
% 11.20/2.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.20/2.01    inference(cnf_transformation,[],[f9])).
% 11.20/2.01  
% 11.20/2.01  fof(f2,axiom,(
% 11.20/2.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f22,plain,(
% 11.20/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f2])).
% 11.20/2.01  
% 11.20/2.01  fof(f1,axiom,(
% 11.20/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f21,plain,(
% 11.20/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f1])).
% 11.20/2.01  
% 11.20/2.01  fof(f3,axiom,(
% 11.20/2.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f14,plain,(
% 11.20/2.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 11.20/2.01    inference(unused_predicate_definition_removal,[],[f3])).
% 11.20/2.01  
% 11.20/2.01  fof(f15,plain,(
% 11.20/2.01    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 11.20/2.01    inference(ennf_transformation,[],[f14])).
% 11.20/2.01  
% 11.20/2.01  fof(f23,plain,(
% 11.20/2.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.20/2.01    inference(cnf_transformation,[],[f15])).
% 11.20/2.01  
% 11.20/2.01  fof(f5,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 11.20/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f16,plain,(
% 11.20/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 11.20/2.01    inference(ennf_transformation,[],[f5])).
% 11.20/2.01  
% 11.20/2.01  fof(f25,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 11.20/2.01    inference(cnf_transformation,[],[f16])).
% 11.20/2.01  
% 11.20/2.01  fof(f33,plain,(
% 11.20/2.01    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 11.20/2.01    inference(cnf_transformation,[],[f20])).
% 11.20/2.01  
% 11.20/2.01  cnf(c_11,negated_conjecture,
% 11.20/2.01      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 11.20/2.01      inference(cnf_transformation,[],[f36]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_193,plain,
% 11.20/2.01      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4,plain,
% 11.20/2.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f26]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_196,plain,
% 11.20/2.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_931,plain,
% 11.20/2.01      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_193,c_196]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5,plain,
% 11.20/2.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f34]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_195,plain,
% 11.20/2.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_930,plain,
% 11.20/2.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_195,c_196]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_24562,plain,
% 11.20/2.01      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_930,c_930]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_24683,plain,
% 11.20/2.01      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_24562,c_930]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_9,plain,
% 11.20/2.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f31]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_24685,plain,
% 11.20/2.01      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_24683,c_9]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_6,plain,
% 11.20/2.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.20/2.01      inference(cnf_transformation,[],[f35]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_8,plain,
% 11.20/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.20/2.01      inference(cnf_transformation,[],[f30]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_433,plain,
% 11.20/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_7,plain,
% 11.20/2.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f29]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1,plain,
% 11.20/2.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f22]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_302,plain,
% 11.20/2.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_765,plain,
% 11.20/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_433,c_302]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_772,plain,
% 11.20/2.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_6,c_765]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25590,plain,
% 11.20/2.01      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_24685,c_772]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25758,plain,
% 11.20/2.01      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) = k3_xboole_0(k1_xboole_0,X0) ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_25590,c_7]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_0,plain,
% 11.20/2.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f21]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_451,plain,
% 11.20/2.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27504,plain,
% 11.20/2.01      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_25758,c_451]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27528,plain,
% 11.20/2.01      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_27504,c_9,c_302]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27626,plain,
% 11.20/2.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_27528,c_930]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27758,plain,
% 11.20/2.01      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_27626,c_27528]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27760,plain,
% 11.20/2.01      ( k3_xboole_0(X0,X0) = X0 ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_27758,c_7]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_28511,plain,
% 11.20/2.01      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0),X1) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_27760,c_772]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_28565,plain,
% 11.20/2.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_28511,c_930]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_28566,plain,
% 11.20/2.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_28565,c_9]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_31331,plain,
% 11.20/2.01      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_28566,c_772]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_31396,plain,
% 11.20/2.01      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = k1_xboole_0 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_31331,c_7,c_9]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_48039,plain,
% 11.20/2.01      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_931,c_31396]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2,plain,
% 11.20/2.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f23]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27430,plain,
% 11.20/2.01      ( r1_xboole_0(sK0,sK2) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_2]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_3,plain,
% 11.20/2.01      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 11.20/2.01      inference(cnf_transformation,[],[f25]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_18007,plain,
% 11.20/2.01      ( ~ r1_tarski(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
% 11.20/2.01      | r1_tarski(sK0,sK1) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_78,plain,
% 11.20/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.20/2.01      theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_560,plain,
% 11.20/2.01      ( r1_tarski(X0,X1)
% 11.20/2.01      | ~ r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
% 11.20/2.01      | X0 != k5_xboole_0(sK0,k1_xboole_0)
% 11.20/2.01      | X1 != k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_78]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2040,plain,
% 11.20/2.01      ( r1_tarski(X0,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
% 11.20/2.01      | ~ r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
% 11.20/2.01      | X0 != k5_xboole_0(sK0,k1_xboole_0)
% 11.20/2.01      | k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_560]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_9263,plain,
% 11.20/2.01      ( ~ r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
% 11.20/2.01      | r1_tarski(sK0,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
% 11.20/2.01      | k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
% 11.20/2.01      | sK0 != k5_xboole_0(sK0,k1_xboole_0) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_2040]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2041,plain,
% 11.20/2.01      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_74,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_505,plain,
% 11.20/2.01      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_74]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_581,plain,
% 11.20/2.01      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_505]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_918,plain,
% 11.20/2.01      ( k5_xboole_0(sK0,k1_xboole_0) != sK0
% 11.20/2.01      | sK0 = k5_xboole_0(sK0,k1_xboole_0)
% 11.20/2.01      | sK0 != sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_581]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_690,plain,
% 11.20/2.01      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_271,plain,
% 11.20/2.01      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
% 11.20/2.01      | k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_424,plain,
% 11.20/2.01      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
% 11.20/2.01      | k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_271]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_294,plain,
% 11.20/2.01      ( r1_tarski(X0,X1)
% 11.20/2.01      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 11.20/2.01      | X1 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
% 11.20/2.01      | X0 != sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_78]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_324,plain,
% 11.20/2.01      ( r1_tarski(k5_xboole_0(sK0,k1_xboole_0),X0)
% 11.20/2.01      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 11.20/2.01      | X0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
% 11.20/2.01      | k5_xboole_0(sK0,k1_xboole_0) != sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_294]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_423,plain,
% 11.20/2.01      ( r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
% 11.20/2.01      | ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 11.20/2.01      | k5_xboole_0(sK0,k1_xboole_0) != sK0
% 11.20/2.01      | k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_324]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_73,plain,( X0 = X0 ),theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_331,plain,
% 11.20/2.01      ( sK0 = sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_73]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_325,plain,
% 11.20/2.01      ( k5_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_10,negated_conjecture,
% 11.20/2.01      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 11.20/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(contradiction,plain,
% 11.20/2.01      ( $false ),
% 11.20/2.01      inference(minisat,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_48039,c_27430,c_18007,c_9263,c_2041,c_918,c_690,c_424,
% 11.20/2.01                 c_423,c_331,c_325,c_10,c_11]) ).
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  ------                               Statistics
% 11.20/2.01  
% 11.20/2.01  ------ Selected
% 11.20/2.01  
% 11.20/2.01  total_time:                             1.139
% 11.20/2.01  
%------------------------------------------------------------------------------
