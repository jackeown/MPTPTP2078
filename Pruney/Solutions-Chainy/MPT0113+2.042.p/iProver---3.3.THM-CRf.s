%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:49 EST 2020

% Result     : Theorem 39.13s
% Output     : CNFRefutation 39.13s
% Verified   : 
% Statistics : Number of formulae       :  104 (1060 expanded)
%              Number of clauses        :   69 ( 312 expanded)
%              Number of leaves         :   11 ( 291 expanded)
%              Depth                    :   22
%              Number of atoms          :  144 (1516 expanded)
%              Number of equality atoms :   95 ( 933 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f21,f25,f25,f25,f25])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f25,f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_445,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_446,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1697,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_445,c_446])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_444,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1698,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_444,c_446])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2264,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1698,c_4])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2722,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_2264,c_0])).

cnf(c_2729,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_2722,c_0])).

cnf(c_103165,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1697,c_2729])).

cnf(c_2266,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1698,c_0])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_763,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_5809,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),X0))))) = k4_xboole_0(k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k5_xboole_0(sK0,sK0))))) ),
    inference(superposition,[status(thm)],[c_2266,c_763])).

cnf(c_2276,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2266,c_1698])).

cnf(c_5999,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_5809,c_2266,c_2276])).

cnf(c_6000,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_5999,c_2729])).

cnf(c_747,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_445])).

cnf(c_1005,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_747])).

cnf(c_2271,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1698,c_1005])).

cnf(c_2589,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2271,c_446])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_62,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_152,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_8])).

cnf(c_153,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_1376,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_153,c_0])).

cnf(c_4979,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2589,c_1376])).

cnf(c_5025,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(demodulation,[status(thm)],[c_4979,c_2589])).

cnf(c_9562,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_1,c_5025])).

cnf(c_10482,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_9562,c_1])).

cnf(c_10807,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_10482])).

cnf(c_10429,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),sK0)) ),
    inference(superposition,[status(thm)],[c_1,c_9562])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_656,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_10569,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_10429,c_656,c_1697])).

cnf(c_10847,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_10807,c_10569])).

cnf(c_11716,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6000,c_10847])).

cnf(c_11801,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_11716,c_2729])).

cnf(c_1377,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_153,c_1])).

cnf(c_1534,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1377,c_0])).

cnf(c_1538,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1534,c_656])).

cnf(c_1559,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1538,c_0])).

cnf(c_657,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_658,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_657,c_6])).

cnf(c_1566,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1559,c_658])).

cnf(c_11806,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11801,c_1566,c_2266])).

cnf(c_103420,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_103165,c_11806])).

cnf(c_106258,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_103420,c_747])).

cnf(c_2284,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_2276,c_0])).

cnf(c_2292,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2284,c_2276])).

cnf(c_2293,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_2292,c_656,c_1566])).

cnf(c_106432,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_106258,c_2293])).

cnf(c_748,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_1781,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_1538,c_748])).

cnf(c_1783,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1781,c_6,c_656])).

cnf(c_2706,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1783,c_2264])).

cnf(c_2753,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2706,c_6,c_2729])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_60,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_158,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_60,c_9])).

cnf(c_159,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_160,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_106432,c_2753,c_160])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 39.13/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.13/5.50  
% 39.13/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.13/5.50  
% 39.13/5.50  ------  iProver source info
% 39.13/5.50  
% 39.13/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.13/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.13/5.50  git: non_committed_changes: false
% 39.13/5.50  git: last_make_outside_of_git: false
% 39.13/5.50  
% 39.13/5.50  ------ 
% 39.13/5.50  
% 39.13/5.50  ------ Input Options
% 39.13/5.50  
% 39.13/5.50  --out_options                           all
% 39.13/5.50  --tptp_safe_out                         true
% 39.13/5.50  --problem_path                          ""
% 39.13/5.50  --include_path                          ""
% 39.13/5.50  --clausifier                            res/vclausify_rel
% 39.13/5.50  --clausifier_options                    ""
% 39.13/5.50  --stdin                                 false
% 39.13/5.50  --stats_out                             all
% 39.13/5.50  
% 39.13/5.50  ------ General Options
% 39.13/5.50  
% 39.13/5.50  --fof                                   false
% 39.13/5.50  --time_out_real                         305.
% 39.13/5.50  --time_out_virtual                      -1.
% 39.13/5.50  --symbol_type_check                     false
% 39.13/5.50  --clausify_out                          false
% 39.13/5.50  --sig_cnt_out                           false
% 39.13/5.50  --trig_cnt_out                          false
% 39.13/5.50  --trig_cnt_out_tolerance                1.
% 39.13/5.50  --trig_cnt_out_sk_spl                   false
% 39.13/5.50  --abstr_cl_out                          false
% 39.13/5.50  
% 39.13/5.50  ------ Global Options
% 39.13/5.50  
% 39.13/5.50  --schedule                              default
% 39.13/5.50  --add_important_lit                     false
% 39.13/5.50  --prop_solver_per_cl                    1000
% 39.13/5.50  --min_unsat_core                        false
% 39.13/5.50  --soft_assumptions                      false
% 39.13/5.50  --soft_lemma_size                       3
% 39.13/5.50  --prop_impl_unit_size                   0
% 39.13/5.50  --prop_impl_unit                        []
% 39.13/5.50  --share_sel_clauses                     true
% 39.13/5.50  --reset_solvers                         false
% 39.13/5.50  --bc_imp_inh                            [conj_cone]
% 39.13/5.50  --conj_cone_tolerance                   3.
% 39.13/5.50  --extra_neg_conj                        none
% 39.13/5.50  --large_theory_mode                     true
% 39.13/5.50  --prolific_symb_bound                   200
% 39.13/5.50  --lt_threshold                          2000
% 39.13/5.50  --clause_weak_htbl                      true
% 39.13/5.50  --gc_record_bc_elim                     false
% 39.13/5.50  
% 39.13/5.50  ------ Preprocessing Options
% 39.13/5.50  
% 39.13/5.50  --preprocessing_flag                    true
% 39.13/5.50  --time_out_prep_mult                    0.1
% 39.13/5.50  --splitting_mode                        input
% 39.13/5.50  --splitting_grd                         true
% 39.13/5.50  --splitting_cvd                         false
% 39.13/5.50  --splitting_cvd_svl                     false
% 39.13/5.50  --splitting_nvd                         32
% 39.13/5.50  --sub_typing                            true
% 39.13/5.50  --prep_gs_sim                           true
% 39.13/5.50  --prep_unflatten                        true
% 39.13/5.50  --prep_res_sim                          true
% 39.13/5.50  --prep_upred                            true
% 39.13/5.50  --prep_sem_filter                       exhaustive
% 39.13/5.50  --prep_sem_filter_out                   false
% 39.13/5.50  --pred_elim                             true
% 39.13/5.50  --res_sim_input                         true
% 39.13/5.50  --eq_ax_congr_red                       true
% 39.13/5.50  --pure_diseq_elim                       true
% 39.13/5.50  --brand_transform                       false
% 39.13/5.50  --non_eq_to_eq                          false
% 39.13/5.50  --prep_def_merge                        true
% 39.13/5.50  --prep_def_merge_prop_impl              false
% 39.13/5.50  --prep_def_merge_mbd                    true
% 39.13/5.50  --prep_def_merge_tr_red                 false
% 39.13/5.50  --prep_def_merge_tr_cl                  false
% 39.13/5.50  --smt_preprocessing                     true
% 39.13/5.50  --smt_ac_axioms                         fast
% 39.13/5.50  --preprocessed_out                      false
% 39.13/5.50  --preprocessed_stats                    false
% 39.13/5.50  
% 39.13/5.50  ------ Abstraction refinement Options
% 39.13/5.50  
% 39.13/5.50  --abstr_ref                             []
% 39.13/5.50  --abstr_ref_prep                        false
% 39.13/5.50  --abstr_ref_until_sat                   false
% 39.13/5.50  --abstr_ref_sig_restrict                funpre
% 39.13/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.13/5.50  --abstr_ref_under                       []
% 39.13/5.50  
% 39.13/5.50  ------ SAT Options
% 39.13/5.50  
% 39.13/5.50  --sat_mode                              false
% 39.13/5.50  --sat_fm_restart_options                ""
% 39.13/5.50  --sat_gr_def                            false
% 39.13/5.50  --sat_epr_types                         true
% 39.13/5.50  --sat_non_cyclic_types                  false
% 39.13/5.50  --sat_finite_models                     false
% 39.13/5.50  --sat_fm_lemmas                         false
% 39.13/5.50  --sat_fm_prep                           false
% 39.13/5.50  --sat_fm_uc_incr                        true
% 39.13/5.50  --sat_out_model                         small
% 39.13/5.50  --sat_out_clauses                       false
% 39.13/5.50  
% 39.13/5.50  ------ QBF Options
% 39.13/5.50  
% 39.13/5.50  --qbf_mode                              false
% 39.13/5.50  --qbf_elim_univ                         false
% 39.13/5.50  --qbf_dom_inst                          none
% 39.13/5.50  --qbf_dom_pre_inst                      false
% 39.13/5.50  --qbf_sk_in                             false
% 39.13/5.50  --qbf_pred_elim                         true
% 39.13/5.50  --qbf_split                             512
% 39.13/5.50  
% 39.13/5.50  ------ BMC1 Options
% 39.13/5.50  
% 39.13/5.50  --bmc1_incremental                      false
% 39.13/5.50  --bmc1_axioms                           reachable_all
% 39.13/5.50  --bmc1_min_bound                        0
% 39.13/5.50  --bmc1_max_bound                        -1
% 39.13/5.50  --bmc1_max_bound_default                -1
% 39.13/5.50  --bmc1_symbol_reachability              true
% 39.13/5.50  --bmc1_property_lemmas                  false
% 39.13/5.50  --bmc1_k_induction                      false
% 39.13/5.50  --bmc1_non_equiv_states                 false
% 39.13/5.50  --bmc1_deadlock                         false
% 39.13/5.50  --bmc1_ucm                              false
% 39.13/5.50  --bmc1_add_unsat_core                   none
% 39.13/5.50  --bmc1_unsat_core_children              false
% 39.13/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.13/5.50  --bmc1_out_stat                         full
% 39.13/5.50  --bmc1_ground_init                      false
% 39.13/5.50  --bmc1_pre_inst_next_state              false
% 39.13/5.50  --bmc1_pre_inst_state                   false
% 39.13/5.50  --bmc1_pre_inst_reach_state             false
% 39.13/5.50  --bmc1_out_unsat_core                   false
% 39.13/5.50  --bmc1_aig_witness_out                  false
% 39.13/5.50  --bmc1_verbose                          false
% 39.13/5.50  --bmc1_dump_clauses_tptp                false
% 39.13/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.13/5.50  --bmc1_dump_file                        -
% 39.13/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.13/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.13/5.50  --bmc1_ucm_extend_mode                  1
% 39.13/5.50  --bmc1_ucm_init_mode                    2
% 39.13/5.50  --bmc1_ucm_cone_mode                    none
% 39.13/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.13/5.50  --bmc1_ucm_relax_model                  4
% 39.13/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.13/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.13/5.50  --bmc1_ucm_layered_model                none
% 39.13/5.50  --bmc1_ucm_max_lemma_size               10
% 39.13/5.50  
% 39.13/5.50  ------ AIG Options
% 39.13/5.50  
% 39.13/5.50  --aig_mode                              false
% 39.13/5.50  
% 39.13/5.50  ------ Instantiation Options
% 39.13/5.50  
% 39.13/5.50  --instantiation_flag                    true
% 39.13/5.50  --inst_sos_flag                         true
% 39.13/5.50  --inst_sos_phase                        true
% 39.13/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.13/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.13/5.50  --inst_lit_sel_side                     num_symb
% 39.13/5.50  --inst_solver_per_active                1400
% 39.13/5.50  --inst_solver_calls_frac                1.
% 39.13/5.50  --inst_passive_queue_type               priority_queues
% 39.13/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.13/5.50  --inst_passive_queues_freq              [25;2]
% 39.13/5.50  --inst_dismatching                      true
% 39.13/5.50  --inst_eager_unprocessed_to_passive     true
% 39.13/5.50  --inst_prop_sim_given                   true
% 39.13/5.50  --inst_prop_sim_new                     false
% 39.13/5.50  --inst_subs_new                         false
% 39.13/5.50  --inst_eq_res_simp                      false
% 39.13/5.50  --inst_subs_given                       false
% 39.13/5.50  --inst_orphan_elimination               true
% 39.13/5.50  --inst_learning_loop_flag               true
% 39.13/5.50  --inst_learning_start                   3000
% 39.13/5.50  --inst_learning_factor                  2
% 39.13/5.50  --inst_start_prop_sim_after_learn       3
% 39.13/5.50  --inst_sel_renew                        solver
% 39.13/5.50  --inst_lit_activity_flag                true
% 39.13/5.50  --inst_restr_to_given                   false
% 39.13/5.50  --inst_activity_threshold               500
% 39.13/5.50  --inst_out_proof                        true
% 39.13/5.50  
% 39.13/5.50  ------ Resolution Options
% 39.13/5.50  
% 39.13/5.50  --resolution_flag                       true
% 39.13/5.50  --res_lit_sel                           adaptive
% 39.13/5.50  --res_lit_sel_side                      none
% 39.13/5.50  --res_ordering                          kbo
% 39.13/5.50  --res_to_prop_solver                    active
% 39.13/5.50  --res_prop_simpl_new                    false
% 39.13/5.50  --res_prop_simpl_given                  true
% 39.13/5.50  --res_passive_queue_type                priority_queues
% 39.13/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.13/5.50  --res_passive_queues_freq               [15;5]
% 39.13/5.50  --res_forward_subs                      full
% 39.13/5.50  --res_backward_subs                     full
% 39.13/5.50  --res_forward_subs_resolution           true
% 39.13/5.50  --res_backward_subs_resolution          true
% 39.13/5.50  --res_orphan_elimination                true
% 39.13/5.50  --res_time_limit                        2.
% 39.13/5.50  --res_out_proof                         true
% 39.13/5.50  
% 39.13/5.50  ------ Superposition Options
% 39.13/5.50  
% 39.13/5.50  --superposition_flag                    true
% 39.13/5.50  --sup_passive_queue_type                priority_queues
% 39.13/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.13/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.13/5.50  --demod_completeness_check              fast
% 39.13/5.50  --demod_use_ground                      true
% 39.13/5.50  --sup_to_prop_solver                    passive
% 39.13/5.50  --sup_prop_simpl_new                    true
% 39.13/5.50  --sup_prop_simpl_given                  true
% 39.13/5.50  --sup_fun_splitting                     true
% 39.13/5.50  --sup_smt_interval                      50000
% 39.13/5.50  
% 39.13/5.50  ------ Superposition Simplification Setup
% 39.13/5.50  
% 39.13/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.13/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.13/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.13/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.13/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.13/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.13/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.13/5.50  --sup_immed_triv                        [TrivRules]
% 39.13/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.13/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.13/5.50  --sup_immed_bw_main                     []
% 39.13/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.13/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.13/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.13/5.50  --sup_input_bw                          []
% 39.13/5.50  
% 39.13/5.50  ------ Combination Options
% 39.13/5.50  
% 39.13/5.50  --comb_res_mult                         3
% 39.13/5.50  --comb_sup_mult                         2
% 39.13/5.50  --comb_inst_mult                        10
% 39.13/5.50  
% 39.13/5.50  ------ Debug Options
% 39.13/5.50  
% 39.13/5.50  --dbg_backtrace                         false
% 39.13/5.50  --dbg_dump_prop_clauses                 false
% 39.13/5.50  --dbg_dump_prop_clauses_file            -
% 39.13/5.50  --dbg_out_stat                          false
% 39.13/5.50  ------ Parsing...
% 39.13/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.13/5.50  
% 39.13/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.13/5.50  
% 39.13/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.13/5.50  
% 39.13/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.13/5.50  ------ Proving...
% 39.13/5.50  ------ Problem Properties 
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  clauses                                 10
% 39.13/5.50  conjectures                             1
% 39.13/5.50  EPR                                     0
% 39.13/5.50  Horn                                    10
% 39.13/5.50  unary                                   7
% 39.13/5.50  binary                                  3
% 39.13/5.50  lits                                    13
% 39.13/5.50  lits eq                                 8
% 39.13/5.50  fd_pure                                 0
% 39.13/5.50  fd_pseudo                               0
% 39.13/5.50  fd_cond                                 0
% 39.13/5.50  fd_pseudo_cond                          0
% 39.13/5.50  AC symbols                              0
% 39.13/5.50  
% 39.13/5.50  ------ Schedule dynamic 5 is on 
% 39.13/5.50  
% 39.13/5.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  ------ 
% 39.13/5.50  Current options:
% 39.13/5.50  ------ 
% 39.13/5.50  
% 39.13/5.50  ------ Input Options
% 39.13/5.50  
% 39.13/5.50  --out_options                           all
% 39.13/5.50  --tptp_safe_out                         true
% 39.13/5.50  --problem_path                          ""
% 39.13/5.50  --include_path                          ""
% 39.13/5.50  --clausifier                            res/vclausify_rel
% 39.13/5.50  --clausifier_options                    ""
% 39.13/5.50  --stdin                                 false
% 39.13/5.50  --stats_out                             all
% 39.13/5.50  
% 39.13/5.50  ------ General Options
% 39.13/5.50  
% 39.13/5.50  --fof                                   false
% 39.13/5.50  --time_out_real                         305.
% 39.13/5.50  --time_out_virtual                      -1.
% 39.13/5.50  --symbol_type_check                     false
% 39.13/5.50  --clausify_out                          false
% 39.13/5.50  --sig_cnt_out                           false
% 39.13/5.50  --trig_cnt_out                          false
% 39.13/5.50  --trig_cnt_out_tolerance                1.
% 39.13/5.50  --trig_cnt_out_sk_spl                   false
% 39.13/5.50  --abstr_cl_out                          false
% 39.13/5.50  
% 39.13/5.50  ------ Global Options
% 39.13/5.50  
% 39.13/5.50  --schedule                              default
% 39.13/5.50  --add_important_lit                     false
% 39.13/5.50  --prop_solver_per_cl                    1000
% 39.13/5.50  --min_unsat_core                        false
% 39.13/5.50  --soft_assumptions                      false
% 39.13/5.50  --soft_lemma_size                       3
% 39.13/5.50  --prop_impl_unit_size                   0
% 39.13/5.50  --prop_impl_unit                        []
% 39.13/5.50  --share_sel_clauses                     true
% 39.13/5.50  --reset_solvers                         false
% 39.13/5.50  --bc_imp_inh                            [conj_cone]
% 39.13/5.50  --conj_cone_tolerance                   3.
% 39.13/5.50  --extra_neg_conj                        none
% 39.13/5.50  --large_theory_mode                     true
% 39.13/5.50  --prolific_symb_bound                   200
% 39.13/5.50  --lt_threshold                          2000
% 39.13/5.50  --clause_weak_htbl                      true
% 39.13/5.50  --gc_record_bc_elim                     false
% 39.13/5.50  
% 39.13/5.50  ------ Preprocessing Options
% 39.13/5.50  
% 39.13/5.50  --preprocessing_flag                    true
% 39.13/5.50  --time_out_prep_mult                    0.1
% 39.13/5.50  --splitting_mode                        input
% 39.13/5.50  --splitting_grd                         true
% 39.13/5.50  --splitting_cvd                         false
% 39.13/5.50  --splitting_cvd_svl                     false
% 39.13/5.50  --splitting_nvd                         32
% 39.13/5.50  --sub_typing                            true
% 39.13/5.50  --prep_gs_sim                           true
% 39.13/5.50  --prep_unflatten                        true
% 39.13/5.50  --prep_res_sim                          true
% 39.13/5.50  --prep_upred                            true
% 39.13/5.50  --prep_sem_filter                       exhaustive
% 39.13/5.50  --prep_sem_filter_out                   false
% 39.13/5.50  --pred_elim                             true
% 39.13/5.50  --res_sim_input                         true
% 39.13/5.50  --eq_ax_congr_red                       true
% 39.13/5.50  --pure_diseq_elim                       true
% 39.13/5.50  --brand_transform                       false
% 39.13/5.50  --non_eq_to_eq                          false
% 39.13/5.50  --prep_def_merge                        true
% 39.13/5.50  --prep_def_merge_prop_impl              false
% 39.13/5.50  --prep_def_merge_mbd                    true
% 39.13/5.50  --prep_def_merge_tr_red                 false
% 39.13/5.50  --prep_def_merge_tr_cl                  false
% 39.13/5.50  --smt_preprocessing                     true
% 39.13/5.50  --smt_ac_axioms                         fast
% 39.13/5.50  --preprocessed_out                      false
% 39.13/5.50  --preprocessed_stats                    false
% 39.13/5.50  
% 39.13/5.50  ------ Abstraction refinement Options
% 39.13/5.50  
% 39.13/5.50  --abstr_ref                             []
% 39.13/5.50  --abstr_ref_prep                        false
% 39.13/5.50  --abstr_ref_until_sat                   false
% 39.13/5.50  --abstr_ref_sig_restrict                funpre
% 39.13/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.13/5.50  --abstr_ref_under                       []
% 39.13/5.50  
% 39.13/5.50  ------ SAT Options
% 39.13/5.50  
% 39.13/5.50  --sat_mode                              false
% 39.13/5.50  --sat_fm_restart_options                ""
% 39.13/5.50  --sat_gr_def                            false
% 39.13/5.50  --sat_epr_types                         true
% 39.13/5.50  --sat_non_cyclic_types                  false
% 39.13/5.50  --sat_finite_models                     false
% 39.13/5.50  --sat_fm_lemmas                         false
% 39.13/5.50  --sat_fm_prep                           false
% 39.13/5.50  --sat_fm_uc_incr                        true
% 39.13/5.50  --sat_out_model                         small
% 39.13/5.50  --sat_out_clauses                       false
% 39.13/5.50  
% 39.13/5.50  ------ QBF Options
% 39.13/5.50  
% 39.13/5.50  --qbf_mode                              false
% 39.13/5.50  --qbf_elim_univ                         false
% 39.13/5.50  --qbf_dom_inst                          none
% 39.13/5.50  --qbf_dom_pre_inst                      false
% 39.13/5.50  --qbf_sk_in                             false
% 39.13/5.50  --qbf_pred_elim                         true
% 39.13/5.50  --qbf_split                             512
% 39.13/5.50  
% 39.13/5.50  ------ BMC1 Options
% 39.13/5.50  
% 39.13/5.50  --bmc1_incremental                      false
% 39.13/5.50  --bmc1_axioms                           reachable_all
% 39.13/5.50  --bmc1_min_bound                        0
% 39.13/5.50  --bmc1_max_bound                        -1
% 39.13/5.50  --bmc1_max_bound_default                -1
% 39.13/5.50  --bmc1_symbol_reachability              true
% 39.13/5.50  --bmc1_property_lemmas                  false
% 39.13/5.50  --bmc1_k_induction                      false
% 39.13/5.50  --bmc1_non_equiv_states                 false
% 39.13/5.50  --bmc1_deadlock                         false
% 39.13/5.50  --bmc1_ucm                              false
% 39.13/5.50  --bmc1_add_unsat_core                   none
% 39.13/5.50  --bmc1_unsat_core_children              false
% 39.13/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.13/5.50  --bmc1_out_stat                         full
% 39.13/5.50  --bmc1_ground_init                      false
% 39.13/5.50  --bmc1_pre_inst_next_state              false
% 39.13/5.50  --bmc1_pre_inst_state                   false
% 39.13/5.50  --bmc1_pre_inst_reach_state             false
% 39.13/5.50  --bmc1_out_unsat_core                   false
% 39.13/5.50  --bmc1_aig_witness_out                  false
% 39.13/5.50  --bmc1_verbose                          false
% 39.13/5.50  --bmc1_dump_clauses_tptp                false
% 39.13/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.13/5.50  --bmc1_dump_file                        -
% 39.13/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.13/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.13/5.50  --bmc1_ucm_extend_mode                  1
% 39.13/5.50  --bmc1_ucm_init_mode                    2
% 39.13/5.50  --bmc1_ucm_cone_mode                    none
% 39.13/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.13/5.50  --bmc1_ucm_relax_model                  4
% 39.13/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.13/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.13/5.50  --bmc1_ucm_layered_model                none
% 39.13/5.50  --bmc1_ucm_max_lemma_size               10
% 39.13/5.50  
% 39.13/5.50  ------ AIG Options
% 39.13/5.50  
% 39.13/5.50  --aig_mode                              false
% 39.13/5.50  
% 39.13/5.50  ------ Instantiation Options
% 39.13/5.50  
% 39.13/5.50  --instantiation_flag                    true
% 39.13/5.50  --inst_sos_flag                         true
% 39.13/5.50  --inst_sos_phase                        true
% 39.13/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.13/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.13/5.50  --inst_lit_sel_side                     none
% 39.13/5.50  --inst_solver_per_active                1400
% 39.13/5.50  --inst_solver_calls_frac                1.
% 39.13/5.50  --inst_passive_queue_type               priority_queues
% 39.13/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.13/5.50  --inst_passive_queues_freq              [25;2]
% 39.13/5.50  --inst_dismatching                      true
% 39.13/5.50  --inst_eager_unprocessed_to_passive     true
% 39.13/5.50  --inst_prop_sim_given                   true
% 39.13/5.50  --inst_prop_sim_new                     false
% 39.13/5.50  --inst_subs_new                         false
% 39.13/5.50  --inst_eq_res_simp                      false
% 39.13/5.50  --inst_subs_given                       false
% 39.13/5.50  --inst_orphan_elimination               true
% 39.13/5.50  --inst_learning_loop_flag               true
% 39.13/5.50  --inst_learning_start                   3000
% 39.13/5.50  --inst_learning_factor                  2
% 39.13/5.50  --inst_start_prop_sim_after_learn       3
% 39.13/5.50  --inst_sel_renew                        solver
% 39.13/5.50  --inst_lit_activity_flag                true
% 39.13/5.50  --inst_restr_to_given                   false
% 39.13/5.50  --inst_activity_threshold               500
% 39.13/5.50  --inst_out_proof                        true
% 39.13/5.50  
% 39.13/5.50  ------ Resolution Options
% 39.13/5.50  
% 39.13/5.50  --resolution_flag                       false
% 39.13/5.50  --res_lit_sel                           adaptive
% 39.13/5.50  --res_lit_sel_side                      none
% 39.13/5.50  --res_ordering                          kbo
% 39.13/5.50  --res_to_prop_solver                    active
% 39.13/5.50  --res_prop_simpl_new                    false
% 39.13/5.50  --res_prop_simpl_given                  true
% 39.13/5.50  --res_passive_queue_type                priority_queues
% 39.13/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.13/5.50  --res_passive_queues_freq               [15;5]
% 39.13/5.50  --res_forward_subs                      full
% 39.13/5.50  --res_backward_subs                     full
% 39.13/5.50  --res_forward_subs_resolution           true
% 39.13/5.50  --res_backward_subs_resolution          true
% 39.13/5.50  --res_orphan_elimination                true
% 39.13/5.50  --res_time_limit                        2.
% 39.13/5.50  --res_out_proof                         true
% 39.13/5.50  
% 39.13/5.50  ------ Superposition Options
% 39.13/5.50  
% 39.13/5.50  --superposition_flag                    true
% 39.13/5.50  --sup_passive_queue_type                priority_queues
% 39.13/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.13/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.13/5.50  --demod_completeness_check              fast
% 39.13/5.50  --demod_use_ground                      true
% 39.13/5.50  --sup_to_prop_solver                    passive
% 39.13/5.50  --sup_prop_simpl_new                    true
% 39.13/5.50  --sup_prop_simpl_given                  true
% 39.13/5.50  --sup_fun_splitting                     true
% 39.13/5.50  --sup_smt_interval                      50000
% 39.13/5.50  
% 39.13/5.50  ------ Superposition Simplification Setup
% 39.13/5.50  
% 39.13/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.13/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.13/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.13/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.13/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.13/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.13/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.13/5.50  --sup_immed_triv                        [TrivRules]
% 39.13/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.13/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.13/5.50  --sup_immed_bw_main                     []
% 39.13/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.13/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.13/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.13/5.50  --sup_input_bw                          []
% 39.13/5.50  
% 39.13/5.50  ------ Combination Options
% 39.13/5.50  
% 39.13/5.50  --comb_res_mult                         3
% 39.13/5.50  --comb_sup_mult                         2
% 39.13/5.50  --comb_inst_mult                        10
% 39.13/5.50  
% 39.13/5.50  ------ Debug Options
% 39.13/5.50  
% 39.13/5.50  --dbg_backtrace                         false
% 39.13/5.50  --dbg_dump_prop_clauses                 false
% 39.13/5.50  --dbg_dump_prop_clauses_file            -
% 39.13/5.50  --dbg_out_stat                          false
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  ------ Proving...
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  % SZS status Theorem for theBenchmark.p
% 39.13/5.50  
% 39.13/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.13/5.50  
% 39.13/5.50  fof(f7,axiom,(
% 39.13/5.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f24,plain,(
% 39.13/5.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.13/5.50    inference(cnf_transformation,[],[f7])).
% 39.13/5.50  
% 39.13/5.50  fof(f5,axiom,(
% 39.13/5.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f12,plain,(
% 39.13/5.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.13/5.50    inference(ennf_transformation,[],[f5])).
% 39.13/5.50  
% 39.13/5.50  fof(f22,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.13/5.50    inference(cnf_transformation,[],[f12])).
% 39.13/5.50  
% 39.13/5.50  fof(f8,axiom,(
% 39.13/5.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f25,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.13/5.50    inference(cnf_transformation,[],[f8])).
% 39.13/5.50  
% 39.13/5.50  fof(f34,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 39.13/5.50    inference(definition_unfolding,[],[f22,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f10,conjecture,(
% 39.13/5.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f11,negated_conjecture,(
% 39.13/5.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 39.13/5.50    inference(negated_conjecture,[],[f10])).
% 39.13/5.50  
% 39.13/5.50  fof(f13,plain,(
% 39.13/5.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 39.13/5.50    inference(ennf_transformation,[],[f11])).
% 39.13/5.50  
% 39.13/5.50  fof(f15,plain,(
% 39.13/5.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 39.13/5.50    introduced(choice_axiom,[])).
% 39.13/5.50  
% 39.13/5.50  fof(f16,plain,(
% 39.13/5.50    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 39.13/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 39.13/5.50  
% 39.13/5.50  fof(f27,plain,(
% 39.13/5.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 39.13/5.50    inference(cnf_transformation,[],[f16])).
% 39.13/5.50  
% 39.13/5.50  fof(f4,axiom,(
% 39.13/5.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f21,plain,(
% 39.13/5.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.13/5.50    inference(cnf_transformation,[],[f4])).
% 39.13/5.50  
% 39.13/5.50  fof(f33,plain,(
% 39.13/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 39.13/5.50    inference(definition_unfolding,[],[f21,f25,f25,f25,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f3,axiom,(
% 39.13/5.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f20,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.13/5.50    inference(cnf_transformation,[],[f3])).
% 39.13/5.50  
% 39.13/5.50  fof(f29,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 39.13/5.50    inference(definition_unfolding,[],[f20,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f1,axiom,(
% 39.13/5.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f17,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.13/5.50    inference(cnf_transformation,[],[f1])).
% 39.13/5.50  
% 39.13/5.50  fof(f30,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 39.13/5.50    inference(definition_unfolding,[],[f17,f25,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f2,axiom,(
% 39.13/5.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f14,plain,(
% 39.13/5.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 39.13/5.50    inference(nnf_transformation,[],[f2])).
% 39.13/5.50  
% 39.13/5.50  fof(f18,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 39.13/5.50    inference(cnf_transformation,[],[f14])).
% 39.13/5.50  
% 39.13/5.50  fof(f32,plain,(
% 39.13/5.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 39.13/5.50    inference(definition_unfolding,[],[f18,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f9,axiom,(
% 39.13/5.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f26,plain,(
% 39.13/5.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 39.13/5.50    inference(cnf_transformation,[],[f9])).
% 39.13/5.50  
% 39.13/5.50  fof(f6,axiom,(
% 39.13/5.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 39.13/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.13/5.50  
% 39.13/5.50  fof(f23,plain,(
% 39.13/5.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 39.13/5.50    inference(cnf_transformation,[],[f6])).
% 39.13/5.50  
% 39.13/5.50  fof(f35,plain,(
% 39.13/5.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 39.13/5.50    inference(definition_unfolding,[],[f23,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f19,plain,(
% 39.13/5.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.13/5.50    inference(cnf_transformation,[],[f14])).
% 39.13/5.50  
% 39.13/5.50  fof(f31,plain,(
% 39.13/5.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.13/5.50    inference(definition_unfolding,[],[f19,f25])).
% 39.13/5.50  
% 39.13/5.50  fof(f28,plain,(
% 39.13/5.50    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 39.13/5.50    inference(cnf_transformation,[],[f16])).
% 39.13/5.50  
% 39.13/5.50  cnf(c_7,plain,
% 39.13/5.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 39.13/5.50      inference(cnf_transformation,[],[f24]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_445,plain,
% 39.13/5.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 39.13/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_5,plain,
% 39.13/5.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 39.13/5.50      inference(cnf_transformation,[],[f34]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_446,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 39.13/5.50      | r1_tarski(X0,X1) != iProver_top ),
% 39.13/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1697,plain,
% 39.13/5.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_445,c_446]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_10,negated_conjecture,
% 39.13/5.50      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
% 39.13/5.50      inference(cnf_transformation,[],[f27]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_444,plain,
% 39.13/5.50      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 39.13/5.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1698,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = sK0 ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_444,c_446]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_4,plain,
% 39.13/5.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 39.13/5.50      inference(cnf_transformation,[],[f33]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2264,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1698,c_4]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_0,plain,
% 39.13/5.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 39.13/5.50      inference(cnf_transformation,[],[f29]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2722,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_2264,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2729,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(sK0,X0) ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_2722,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_103165,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1697,c_2729]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2266,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1698,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 39.13/5.50      inference(cnf_transformation,[],[f30]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_763,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_5809,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),X0))))) = k4_xboole_0(k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k5_xboole_0(sK0,sK0))))) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_2266,c_763]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2276,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = sK0 ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_2266,c_1698]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_5999,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_5809,c_2266,c_2276]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_6000,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_5999,c_2729]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_747,plain,
% 39.13/5.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1,c_445]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1005,plain,
% 39.13/5.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_4,c_747]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2271,plain,
% 39.13/5.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1698,c_1005]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2589,plain,
% 39.13/5.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_2271,c_446]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_3,plain,
% 39.13/5.50      ( ~ r1_xboole_0(X0,X1)
% 39.13/5.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.13/5.50      inference(cnf_transformation,[],[f32]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_62,plain,
% 39.13/5.50      ( ~ r1_xboole_0(X0,X1)
% 39.13/5.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.13/5.50      inference(prop_impl,[status(thm)],[c_3]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_8,plain,
% 39.13/5.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 39.13/5.50      inference(cnf_transformation,[],[f26]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_152,plain,
% 39.13/5.50      ( X0 != X1
% 39.13/5.50      | k4_xboole_0(X2,X0) != X3
% 39.13/5.50      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
% 39.13/5.50      inference(resolution_lifted,[status(thm)],[c_62,c_8]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_153,plain,
% 39.13/5.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 39.13/5.50      inference(unflattening,[status(thm)],[c_152]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1376,plain,
% 39.13/5.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_153,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_4979,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_2589,c_1376]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_5025,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_4979,c_2589]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_9562,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1,c_5025]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_10482,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_9562,c_1]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_10807,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1,c_10482]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_10429,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),sK0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1,c_9562]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_6,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 39.13/5.50      inference(cnf_transformation,[],[f35]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_656,plain,
% 39.13/5.50      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_10569,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,X0) ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_10429,c_656,c_1697]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_10847,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_10807,c_10569]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_11716,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,X0) ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_6000,c_10847]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_11801,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_11716,c_2729]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1377,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_153,c_1]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1534,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1377,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1538,plain,
% 39.13/5.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_1534,c_656]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1559,plain,
% 39.13/5.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1538,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_657,plain,
% 39.13/5.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_658,plain,
% 39.13/5.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_657,c_6]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1566,plain,
% 39.13/5.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_1559,c_658]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_11806,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_11801,c_1566,c_2266]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_103420,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_103165,c_11806]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_106258,plain,
% 39.13/5.50      ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) = iProver_top ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_103420,c_747]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2284,plain,
% 39.13/5.50      ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_2276,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2292,plain,
% 39.13/5.50      ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_2284,c_2276]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2293,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_2292,c_656,c_1566]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_106432,plain,
% 39.13/5.50      ( r1_tarski(sK0,sK1) = iProver_top ),
% 39.13/5.50      inference(light_normalisation,[status(thm)],[c_106258,c_2293]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_748,plain,
% 39.13/5.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1781,plain,
% 39.13/5.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1538,c_748]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_1783,plain,
% 39.13/5.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_1781,c_6,c_656]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2706,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 39.13/5.50      inference(superposition,[status(thm)],[c_1783,c_2264]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2753,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 39.13/5.50      inference(demodulation,[status(thm)],[c_2706,c_6,c_2729]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_2,plain,
% 39.13/5.50      ( r1_xboole_0(X0,X1)
% 39.13/5.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 39.13/5.50      inference(cnf_transformation,[],[f31]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_60,plain,
% 39.13/5.50      ( r1_xboole_0(X0,X1)
% 39.13/5.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 39.13/5.50      inference(prop_impl,[status(thm)],[c_2]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_9,negated_conjecture,
% 39.13/5.50      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 39.13/5.50      inference(cnf_transformation,[],[f28]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_158,plain,
% 39.13/5.50      ( ~ r1_tarski(sK0,sK1)
% 39.13/5.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 39.13/5.50      | sK2 != X1
% 39.13/5.50      | sK0 != X0 ),
% 39.13/5.50      inference(resolution_lifted,[status(thm)],[c_60,c_9]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_159,plain,
% 39.13/5.50      ( ~ r1_tarski(sK0,sK1)
% 39.13/5.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 39.13/5.50      inference(unflattening,[status(thm)],[c_158]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(c_160,plain,
% 39.13/5.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
% 39.13/5.50      | r1_tarski(sK0,sK1) != iProver_top ),
% 39.13/5.50      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 39.13/5.50  
% 39.13/5.50  cnf(contradiction,plain,
% 39.13/5.50      ( $false ),
% 39.13/5.50      inference(minisat,[status(thm)],[c_106432,c_2753,c_160]) ).
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.13/5.50  
% 39.13/5.50  ------                               Statistics
% 39.13/5.50  
% 39.13/5.50  ------ General
% 39.13/5.50  
% 39.13/5.50  abstr_ref_over_cycles:                  0
% 39.13/5.50  abstr_ref_under_cycles:                 0
% 39.13/5.50  gc_basic_clause_elim:                   0
% 39.13/5.50  forced_gc_time:                         0
% 39.13/5.50  parsing_time:                           0.014
% 39.13/5.50  unif_index_cands_time:                  0.
% 39.13/5.50  unif_index_add_time:                    0.
% 39.13/5.50  orderings_time:                         0.
% 39.13/5.50  out_proof_time:                         0.012
% 39.13/5.50  total_time:                             4.565
% 39.13/5.50  num_of_symbols:                         39
% 39.13/5.50  num_of_terms:                           195532
% 39.13/5.50  
% 39.13/5.50  ------ Preprocessing
% 39.13/5.50  
% 39.13/5.50  num_of_splits:                          0
% 39.13/5.50  num_of_split_atoms:                     0
% 39.13/5.50  num_of_reused_defs:                     0
% 39.13/5.50  num_eq_ax_congr_red:                    3
% 39.13/5.50  num_of_sem_filtered_clauses:            1
% 39.13/5.50  num_of_subtypes:                        1
% 39.13/5.50  monotx_restored_types:                  0
% 39.13/5.50  sat_num_of_epr_types:                   0
% 39.13/5.50  sat_num_of_non_cyclic_types:            0
% 39.13/5.50  sat_guarded_non_collapsed_types:        1
% 39.13/5.50  num_pure_diseq_elim:                    0
% 39.13/5.50  simp_replaced_by:                       0
% 39.13/5.50  res_preprocessed:                       52
% 39.13/5.50  prep_upred:                             0
% 39.13/5.50  prep_unflattend:                        22
% 39.13/5.50  smt_new_axioms:                         0
% 39.13/5.50  pred_elim_cands:                        1
% 39.13/5.50  pred_elim:                              1
% 39.13/5.50  pred_elim_cl:                           1
% 39.13/5.50  pred_elim_cycles:                       4
% 39.13/5.50  merged_defs:                            2
% 39.13/5.50  merged_defs_ncl:                        0
% 39.13/5.50  bin_hyper_res:                          2
% 39.13/5.50  prep_cycles:                            4
% 39.13/5.50  pred_elim_time:                         0.003
% 39.13/5.50  splitting_time:                         0.
% 39.13/5.50  sem_filter_time:                        0.
% 39.13/5.50  monotx_time:                            0.
% 39.13/5.50  subtype_inf_time:                       0.
% 39.13/5.50  
% 39.13/5.50  ------ Problem properties
% 39.13/5.50  
% 39.13/5.50  clauses:                                10
% 39.13/5.50  conjectures:                            1
% 39.13/5.50  epr:                                    0
% 39.13/5.50  horn:                                   10
% 39.13/5.50  ground:                                 2
% 39.13/5.50  unary:                                  7
% 39.13/5.50  binary:                                 3
% 39.13/5.50  lits:                                   13
% 39.13/5.50  lits_eq:                                8
% 39.13/5.50  fd_pure:                                0
% 39.13/5.50  fd_pseudo:                              0
% 39.13/5.50  fd_cond:                                0
% 39.13/5.50  fd_pseudo_cond:                         0
% 39.13/5.50  ac_symbols:                             0
% 39.13/5.50  
% 39.13/5.50  ------ Propositional Solver
% 39.13/5.50  
% 39.13/5.50  prop_solver_calls:                      35
% 39.13/5.50  prop_fast_solver_calls:                 525
% 39.13/5.50  smt_solver_calls:                       0
% 39.13/5.50  smt_fast_solver_calls:                  0
% 39.13/5.50  prop_num_of_clauses:                    23325
% 39.13/5.50  prop_preprocess_simplified:             16874
% 39.13/5.50  prop_fo_subsumed:                       0
% 39.13/5.50  prop_solver_time:                       0.
% 39.13/5.50  smt_solver_time:                        0.
% 39.13/5.50  smt_fast_solver_time:                   0.
% 39.13/5.50  prop_fast_solver_time:                  0.
% 39.13/5.50  prop_unsat_core_time:                   0.002
% 39.13/5.50  
% 39.13/5.50  ------ QBF
% 39.13/5.50  
% 39.13/5.50  qbf_q_res:                              0
% 39.13/5.50  qbf_num_tautologies:                    0
% 39.13/5.50  qbf_prep_cycles:                        0
% 39.13/5.50  
% 39.13/5.50  ------ BMC1
% 39.13/5.50  
% 39.13/5.50  bmc1_current_bound:                     -1
% 39.13/5.50  bmc1_last_solved_bound:                 -1
% 39.13/5.50  bmc1_unsat_core_size:                   -1
% 39.13/5.50  bmc1_unsat_core_parents_size:           -1
% 39.13/5.50  bmc1_merge_next_fun:                    0
% 39.13/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.13/5.50  
% 39.13/5.50  ------ Instantiation
% 39.13/5.50  
% 39.13/5.50  inst_num_of_clauses:                    3324
% 39.13/5.50  inst_num_in_passive:                    1563
% 39.13/5.50  inst_num_in_active:                     1244
% 39.13/5.50  inst_num_in_unprocessed:                521
% 39.13/5.50  inst_num_of_loops:                      1340
% 39.13/5.50  inst_num_of_learning_restarts:          0
% 39.13/5.50  inst_num_moves_active_passive:          88
% 39.13/5.50  inst_lit_activity:                      0
% 39.13/5.50  inst_lit_activity_moves:                0
% 39.13/5.50  inst_num_tautologies:                   0
% 39.13/5.50  inst_num_prop_implied:                  0
% 39.13/5.50  inst_num_existing_simplified:           0
% 39.13/5.50  inst_num_eq_res_simplified:             0
% 39.13/5.50  inst_num_child_elim:                    0
% 39.13/5.50  inst_num_of_dismatching_blockings:      4384
% 39.13/5.50  inst_num_of_non_proper_insts:           6028
% 39.13/5.50  inst_num_of_duplicates:                 0
% 39.13/5.50  inst_inst_num_from_inst_to_res:         0
% 39.13/5.50  inst_dismatching_checking_time:         0.
% 39.13/5.50  
% 39.13/5.50  ------ Resolution
% 39.13/5.50  
% 39.13/5.50  res_num_of_clauses:                     0
% 39.13/5.50  res_num_in_passive:                     0
% 39.13/5.50  res_num_in_active:                      0
% 39.13/5.50  res_num_of_loops:                       56
% 39.13/5.50  res_forward_subset_subsumed:            813
% 39.13/5.50  res_backward_subset_subsumed:           28
% 39.13/5.50  res_forward_subsumed:                   0
% 39.13/5.50  res_backward_subsumed:                  0
% 39.13/5.50  res_forward_subsumption_resolution:     0
% 39.13/5.50  res_backward_subsumption_resolution:    0
% 39.13/5.50  res_clause_to_clause_subsumption:       124320
% 39.13/5.50  res_orphan_elimination:                 0
% 39.13/5.50  res_tautology_del:                      272
% 39.13/5.50  res_num_eq_res_simplified:              0
% 39.13/5.50  res_num_sel_changes:                    0
% 39.13/5.50  res_moves_from_active_to_pass:          0
% 39.13/5.50  
% 39.13/5.50  ------ Superposition
% 39.13/5.50  
% 39.13/5.50  sup_time_total:                         0.
% 39.13/5.50  sup_time_generating:                    0.
% 39.13/5.50  sup_time_sim_full:                      0.
% 39.13/5.50  sup_time_sim_immed:                     0.
% 39.13/5.50  
% 39.13/5.50  sup_num_of_clauses:                     6634
% 39.13/5.50  sup_num_in_active:                      187
% 39.13/5.50  sup_num_in_passive:                     6447
% 39.13/5.50  sup_num_of_loops:                       266
% 39.13/5.50  sup_fw_superposition:                   18059
% 39.13/5.50  sup_bw_superposition:                   18627
% 39.13/5.50  sup_immediate_simplified:               23794
% 39.13/5.50  sup_given_eliminated:                   54
% 39.13/5.50  comparisons_done:                       0
% 39.13/5.50  comparisons_avoided:                    0
% 39.13/5.50  
% 39.13/5.50  ------ Simplifications
% 39.13/5.50  
% 39.13/5.50  
% 39.13/5.50  sim_fw_subset_subsumed:                 0
% 39.13/5.50  sim_bw_subset_subsumed:                 0
% 39.13/5.50  sim_fw_subsumed:                        3059
% 39.13/5.50  sim_bw_subsumed:                        327
% 39.13/5.50  sim_fw_subsumption_res:                 0
% 39.13/5.50  sim_bw_subsumption_res:                 0
% 39.13/5.50  sim_tautology_del:                      0
% 39.13/5.50  sim_eq_tautology_del:                   6230
% 39.13/5.50  sim_eq_res_simp:                        1
% 39.13/5.50  sim_fw_demodulated:                     24124
% 39.13/5.50  sim_bw_demodulated:                     1390
% 39.13/5.50  sim_light_normalised:                   12065
% 39.13/5.50  sim_joinable_taut:                      0
% 39.13/5.50  sim_joinable_simp:                      0
% 39.13/5.50  sim_ac_normalised:                      0
% 39.13/5.50  sim_smt_subsumption:                    0
% 39.13/5.50  
%------------------------------------------------------------------------------
