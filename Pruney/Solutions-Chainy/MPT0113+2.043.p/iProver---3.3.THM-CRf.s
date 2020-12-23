%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:49 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  122 (2337 expanded)
%              Number of clauses        :   88 ( 747 expanded)
%              Number of leaves         :   11 ( 606 expanded)
%              Depth                    :   22
%              Number of atoms          :  164 (3619 expanded)
%              Number of equality atoms :  112 (2050 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f24,f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f21,f24,f24,f24,f24])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f24])).

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

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_70,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_169,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_70,c_8])).

cnf(c_170,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1483,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_170,c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1522,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1483,c_0])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_163,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_70,c_7])).

cnf(c_164,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_685,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_164,c_0])).

cnf(c_1526,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1522,c_685])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1653,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_1526,c_4])).

cnf(c_756,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_4011,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_756,c_0])).

cnf(c_28443,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
    inference(superposition,[status(thm)],[c_1653,c_4011])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_420,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_421,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1690,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_420,c_421])).

cnf(c_18600,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1653,c_0])).

cnf(c_3946,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_1,c_756])).

cnf(c_27155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3946,c_1526])).

cnf(c_751,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_420])).

cnf(c_1693,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_751,c_421])).

cnf(c_27180,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_27155,c_1693])).

cnf(c_28960,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28443,c_1690,c_18600,c_27180])).

cnf(c_750,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_28688,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4011,c_750])).

cnf(c_28762,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28688,c_27180])).

cnf(c_28966,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_28960,c_28762])).

cnf(c_28981,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28966,c_0])).

cnf(c_30525,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_28981,c_0])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_419,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1691,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_419,c_421])).

cnf(c_2429,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1691,c_4])).

cnf(c_2883,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_2429,c_0])).

cnf(c_2892,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_2883,c_0])).

cnf(c_4370,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_2892])).

cnf(c_30817,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_30525,c_4370])).

cnf(c_2431,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1691,c_0])).

cnf(c_2445,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2431,c_1691])).

cnf(c_2448,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k5_xboole_0(sK0,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2445,c_170])).

cnf(c_2468,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2448,c_2445])).

cnf(c_767,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_5562,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)),X0))))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_2468,c_767])).

cnf(c_2453,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_2445,c_0])).

cnf(c_2464,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2453,c_2445])).

cnf(c_1655,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1526,c_0])).

cnf(c_686,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_164,c_0])).

cnf(c_687,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_686,c_164])).

cnf(c_1662,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1655,c_687])).

cnf(c_2465,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_2464,c_685,c_1662])).

cnf(c_3510,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_2468,c_4])).

cnf(c_3533,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3510,c_2465])).

cnf(c_5746,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_5562,c_2465,c_2468,c_3533])).

cnf(c_1150,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_751])).

cnf(c_2438,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1150])).

cnf(c_2713,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_2438,c_421])).

cnf(c_1482,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_170,c_0])).

cnf(c_5008,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2713,c_1482])).

cnf(c_5058,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(demodulation,[status(thm)],[c_5008,c_2713])).

cnf(c_11853,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_1,c_5058])).

cnf(c_13095,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_11853,c_1])).

cnf(c_13502,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_13095])).

cnf(c_13031,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),sK0)) ),
    inference(superposition,[status(thm)],[c_1,c_11853])).

cnf(c_13234,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_13031,c_685,c_1690])).

cnf(c_13531,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_13502,c_13234])).

cnf(c_14090,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5746,c_13531])).

cnf(c_14219,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_14090,c_2892])).

cnf(c_14225,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14219,c_2431,c_2468])).

cnf(c_31003,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_30817,c_14225])).

cnf(c_31368,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_31003,c_751])).

cnf(c_31469,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31368,c_2465])).

cnf(c_2865,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_170,c_2429])).

cnf(c_2919,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2865,c_2465,c_2468])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_68,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_175,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_68,c_9])).

cnf(c_176,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_177,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31469,c_2919,c_177])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.73/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/2.01  
% 11.73/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.73/2.01  
% 11.73/2.01  ------  iProver source info
% 11.73/2.01  
% 11.73/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.73/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.73/2.01  git: non_committed_changes: false
% 11.73/2.01  git: last_make_outside_of_git: false
% 11.73/2.01  
% 11.73/2.01  ------ 
% 11.73/2.01  
% 11.73/2.01  ------ Input Options
% 11.73/2.01  
% 11.73/2.01  --out_options                           all
% 11.73/2.01  --tptp_safe_out                         true
% 11.73/2.01  --problem_path                          ""
% 11.73/2.01  --include_path                          ""
% 11.73/2.01  --clausifier                            res/vclausify_rel
% 11.73/2.01  --clausifier_options                    ""
% 11.73/2.01  --stdin                                 false
% 11.73/2.01  --stats_out                             all
% 11.73/2.01  
% 11.73/2.01  ------ General Options
% 11.73/2.01  
% 11.73/2.01  --fof                                   false
% 11.73/2.01  --time_out_real                         305.
% 11.73/2.01  --time_out_virtual                      -1.
% 11.73/2.01  --symbol_type_check                     false
% 11.73/2.01  --clausify_out                          false
% 11.73/2.01  --sig_cnt_out                           false
% 11.73/2.01  --trig_cnt_out                          false
% 11.73/2.01  --trig_cnt_out_tolerance                1.
% 11.73/2.01  --trig_cnt_out_sk_spl                   false
% 11.73/2.01  --abstr_cl_out                          false
% 11.73/2.01  
% 11.73/2.01  ------ Global Options
% 11.73/2.01  
% 11.73/2.01  --schedule                              default
% 11.73/2.01  --add_important_lit                     false
% 11.73/2.01  --prop_solver_per_cl                    1000
% 11.73/2.01  --min_unsat_core                        false
% 11.73/2.01  --soft_assumptions                      false
% 11.73/2.01  --soft_lemma_size                       3
% 11.73/2.01  --prop_impl_unit_size                   0
% 11.73/2.01  --prop_impl_unit                        []
% 11.73/2.01  --share_sel_clauses                     true
% 11.73/2.01  --reset_solvers                         false
% 11.73/2.01  --bc_imp_inh                            [conj_cone]
% 11.73/2.01  --conj_cone_tolerance                   3.
% 11.73/2.01  --extra_neg_conj                        none
% 11.73/2.01  --large_theory_mode                     true
% 11.73/2.01  --prolific_symb_bound                   200
% 11.73/2.01  --lt_threshold                          2000
% 11.73/2.01  --clause_weak_htbl                      true
% 11.73/2.01  --gc_record_bc_elim                     false
% 11.73/2.01  
% 11.73/2.01  ------ Preprocessing Options
% 11.73/2.01  
% 11.73/2.01  --preprocessing_flag                    true
% 11.73/2.01  --time_out_prep_mult                    0.1
% 11.73/2.01  --splitting_mode                        input
% 11.73/2.01  --splitting_grd                         true
% 11.73/2.01  --splitting_cvd                         false
% 11.73/2.01  --splitting_cvd_svl                     false
% 11.73/2.01  --splitting_nvd                         32
% 11.73/2.01  --sub_typing                            true
% 11.73/2.01  --prep_gs_sim                           true
% 11.73/2.01  --prep_unflatten                        true
% 11.73/2.01  --prep_res_sim                          true
% 11.73/2.01  --prep_upred                            true
% 11.73/2.01  --prep_sem_filter                       exhaustive
% 11.73/2.01  --prep_sem_filter_out                   false
% 11.73/2.01  --pred_elim                             true
% 11.73/2.01  --res_sim_input                         true
% 11.73/2.01  --eq_ax_congr_red                       true
% 11.73/2.01  --pure_diseq_elim                       true
% 11.73/2.01  --brand_transform                       false
% 11.73/2.01  --non_eq_to_eq                          false
% 11.73/2.01  --prep_def_merge                        true
% 11.73/2.01  --prep_def_merge_prop_impl              false
% 11.73/2.01  --prep_def_merge_mbd                    true
% 11.73/2.01  --prep_def_merge_tr_red                 false
% 11.73/2.01  --prep_def_merge_tr_cl                  false
% 11.73/2.01  --smt_preprocessing                     true
% 11.73/2.01  --smt_ac_axioms                         fast
% 11.73/2.01  --preprocessed_out                      false
% 11.73/2.01  --preprocessed_stats                    false
% 11.73/2.01  
% 11.73/2.01  ------ Abstraction refinement Options
% 11.73/2.01  
% 11.73/2.01  --abstr_ref                             []
% 11.73/2.01  --abstr_ref_prep                        false
% 11.73/2.01  --abstr_ref_until_sat                   false
% 11.73/2.01  --abstr_ref_sig_restrict                funpre
% 11.73/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/2.01  --abstr_ref_under                       []
% 11.73/2.01  
% 11.73/2.01  ------ SAT Options
% 11.73/2.01  
% 11.73/2.01  --sat_mode                              false
% 11.73/2.01  --sat_fm_restart_options                ""
% 11.73/2.01  --sat_gr_def                            false
% 11.73/2.01  --sat_epr_types                         true
% 11.73/2.01  --sat_non_cyclic_types                  false
% 11.73/2.01  --sat_finite_models                     false
% 11.73/2.01  --sat_fm_lemmas                         false
% 11.73/2.01  --sat_fm_prep                           false
% 11.73/2.01  --sat_fm_uc_incr                        true
% 11.73/2.01  --sat_out_model                         small
% 11.73/2.01  --sat_out_clauses                       false
% 11.73/2.01  
% 11.73/2.01  ------ QBF Options
% 11.73/2.01  
% 11.73/2.01  --qbf_mode                              false
% 11.73/2.01  --qbf_elim_univ                         false
% 11.73/2.01  --qbf_dom_inst                          none
% 11.73/2.01  --qbf_dom_pre_inst                      false
% 11.73/2.01  --qbf_sk_in                             false
% 11.73/2.01  --qbf_pred_elim                         true
% 11.73/2.01  --qbf_split                             512
% 11.73/2.01  
% 11.73/2.01  ------ BMC1 Options
% 11.73/2.01  
% 11.73/2.01  --bmc1_incremental                      false
% 11.73/2.01  --bmc1_axioms                           reachable_all
% 11.73/2.01  --bmc1_min_bound                        0
% 11.73/2.01  --bmc1_max_bound                        -1
% 11.73/2.01  --bmc1_max_bound_default                -1
% 11.73/2.01  --bmc1_symbol_reachability              true
% 11.73/2.01  --bmc1_property_lemmas                  false
% 11.73/2.01  --bmc1_k_induction                      false
% 11.73/2.01  --bmc1_non_equiv_states                 false
% 11.73/2.01  --bmc1_deadlock                         false
% 11.73/2.01  --bmc1_ucm                              false
% 11.73/2.01  --bmc1_add_unsat_core                   none
% 11.73/2.01  --bmc1_unsat_core_children              false
% 11.73/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/2.01  --bmc1_out_stat                         full
% 11.73/2.01  --bmc1_ground_init                      false
% 11.73/2.01  --bmc1_pre_inst_next_state              false
% 11.73/2.01  --bmc1_pre_inst_state                   false
% 11.73/2.01  --bmc1_pre_inst_reach_state             false
% 11.73/2.01  --bmc1_out_unsat_core                   false
% 11.73/2.01  --bmc1_aig_witness_out                  false
% 11.73/2.01  --bmc1_verbose                          false
% 11.73/2.01  --bmc1_dump_clauses_tptp                false
% 11.73/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.73/2.01  --bmc1_dump_file                        -
% 11.73/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.73/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.73/2.01  --bmc1_ucm_extend_mode                  1
% 11.73/2.01  --bmc1_ucm_init_mode                    2
% 11.73/2.01  --bmc1_ucm_cone_mode                    none
% 11.73/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.73/2.01  --bmc1_ucm_relax_model                  4
% 11.73/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.73/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/2.01  --bmc1_ucm_layered_model                none
% 11.73/2.01  --bmc1_ucm_max_lemma_size               10
% 11.73/2.01  
% 11.73/2.01  ------ AIG Options
% 11.73/2.01  
% 11.73/2.01  --aig_mode                              false
% 11.73/2.01  
% 11.73/2.01  ------ Instantiation Options
% 11.73/2.01  
% 11.73/2.01  --instantiation_flag                    true
% 11.73/2.01  --inst_sos_flag                         true
% 11.73/2.01  --inst_sos_phase                        true
% 11.73/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/2.01  --inst_lit_sel_side                     num_symb
% 11.73/2.01  --inst_solver_per_active                1400
% 11.73/2.01  --inst_solver_calls_frac                1.
% 11.73/2.01  --inst_passive_queue_type               priority_queues
% 11.73/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/2.01  --inst_passive_queues_freq              [25;2]
% 11.73/2.01  --inst_dismatching                      true
% 11.73/2.01  --inst_eager_unprocessed_to_passive     true
% 11.73/2.01  --inst_prop_sim_given                   true
% 11.73/2.01  --inst_prop_sim_new                     false
% 11.73/2.01  --inst_subs_new                         false
% 11.73/2.01  --inst_eq_res_simp                      false
% 11.73/2.01  --inst_subs_given                       false
% 11.73/2.01  --inst_orphan_elimination               true
% 11.73/2.01  --inst_learning_loop_flag               true
% 11.73/2.01  --inst_learning_start                   3000
% 11.73/2.01  --inst_learning_factor                  2
% 11.73/2.01  --inst_start_prop_sim_after_learn       3
% 11.73/2.01  --inst_sel_renew                        solver
% 11.73/2.01  --inst_lit_activity_flag                true
% 11.73/2.01  --inst_restr_to_given                   false
% 11.73/2.01  --inst_activity_threshold               500
% 11.73/2.01  --inst_out_proof                        true
% 11.73/2.01  
% 11.73/2.01  ------ Resolution Options
% 11.73/2.01  
% 11.73/2.01  --resolution_flag                       true
% 11.73/2.01  --res_lit_sel                           adaptive
% 11.73/2.01  --res_lit_sel_side                      none
% 11.73/2.01  --res_ordering                          kbo
% 11.73/2.01  --res_to_prop_solver                    active
% 11.73/2.01  --res_prop_simpl_new                    false
% 11.73/2.01  --res_prop_simpl_given                  true
% 11.73/2.01  --res_passive_queue_type                priority_queues
% 11.73/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/2.01  --res_passive_queues_freq               [15;5]
% 11.73/2.01  --res_forward_subs                      full
% 11.73/2.01  --res_backward_subs                     full
% 11.73/2.01  --res_forward_subs_resolution           true
% 11.73/2.01  --res_backward_subs_resolution          true
% 11.73/2.01  --res_orphan_elimination                true
% 11.73/2.01  --res_time_limit                        2.
% 11.73/2.01  --res_out_proof                         true
% 11.73/2.01  
% 11.73/2.01  ------ Superposition Options
% 11.73/2.01  
% 11.73/2.01  --superposition_flag                    true
% 11.73/2.01  --sup_passive_queue_type                priority_queues
% 11.73/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.73/2.01  --demod_completeness_check              fast
% 11.73/2.01  --demod_use_ground                      true
% 11.73/2.01  --sup_to_prop_solver                    passive
% 11.73/2.01  --sup_prop_simpl_new                    true
% 11.73/2.01  --sup_prop_simpl_given                  true
% 11.73/2.01  --sup_fun_splitting                     true
% 11.73/2.01  --sup_smt_interval                      50000
% 11.73/2.01  
% 11.73/2.01  ------ Superposition Simplification Setup
% 11.73/2.01  
% 11.73/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/2.01  --sup_immed_triv                        [TrivRules]
% 11.73/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.01  --sup_immed_bw_main                     []
% 11.73/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.01  --sup_input_bw                          []
% 11.73/2.01  
% 11.73/2.01  ------ Combination Options
% 11.73/2.01  
% 11.73/2.01  --comb_res_mult                         3
% 11.73/2.01  --comb_sup_mult                         2
% 11.73/2.01  --comb_inst_mult                        10
% 11.73/2.01  
% 11.73/2.01  ------ Debug Options
% 11.73/2.01  
% 11.73/2.01  --dbg_backtrace                         false
% 11.73/2.01  --dbg_dump_prop_clauses                 false
% 11.73/2.01  --dbg_dump_prop_clauses_file            -
% 11.73/2.01  --dbg_out_stat                          false
% 11.73/2.01  ------ Parsing...
% 11.73/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/2.01  
% 11.73/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 11.73/2.01  
% 11.73/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/2.01  
% 11.73/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.73/2.01  ------ Proving...
% 11.73/2.01  ------ Problem Properties 
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  clauses                                 11
% 11.73/2.01  conjectures                             1
% 11.73/2.01  EPR                                     1
% 11.73/2.01  Horn                                    11
% 11.73/2.01  unary                                   7
% 11.73/2.01  binary                                  4
% 11.73/2.01  lits                                    15
% 11.73/2.01  lits eq                                 9
% 11.73/2.01  fd_pure                                 0
% 11.73/2.01  fd_pseudo                               0
% 11.73/2.01  fd_cond                                 0
% 11.73/2.01  fd_pseudo_cond                          0
% 11.73/2.01  AC symbols                              0
% 11.73/2.01  
% 11.73/2.01  ------ Schedule dynamic 5 is on 
% 11.73/2.01  
% 11.73/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  ------ 
% 11.73/2.01  Current options:
% 11.73/2.01  ------ 
% 11.73/2.01  
% 11.73/2.01  ------ Input Options
% 11.73/2.01  
% 11.73/2.01  --out_options                           all
% 11.73/2.01  --tptp_safe_out                         true
% 11.73/2.01  --problem_path                          ""
% 11.73/2.01  --include_path                          ""
% 11.73/2.01  --clausifier                            res/vclausify_rel
% 11.73/2.01  --clausifier_options                    ""
% 11.73/2.01  --stdin                                 false
% 11.73/2.01  --stats_out                             all
% 11.73/2.01  
% 11.73/2.01  ------ General Options
% 11.73/2.01  
% 11.73/2.01  --fof                                   false
% 11.73/2.01  --time_out_real                         305.
% 11.73/2.01  --time_out_virtual                      -1.
% 11.73/2.01  --symbol_type_check                     false
% 11.73/2.01  --clausify_out                          false
% 11.73/2.01  --sig_cnt_out                           false
% 11.73/2.01  --trig_cnt_out                          false
% 11.73/2.01  --trig_cnt_out_tolerance                1.
% 11.73/2.01  --trig_cnt_out_sk_spl                   false
% 11.73/2.01  --abstr_cl_out                          false
% 11.73/2.01  
% 11.73/2.01  ------ Global Options
% 11.73/2.01  
% 11.73/2.01  --schedule                              default
% 11.73/2.01  --add_important_lit                     false
% 11.73/2.01  --prop_solver_per_cl                    1000
% 11.73/2.01  --min_unsat_core                        false
% 11.73/2.01  --soft_assumptions                      false
% 11.73/2.01  --soft_lemma_size                       3
% 11.73/2.01  --prop_impl_unit_size                   0
% 11.73/2.01  --prop_impl_unit                        []
% 11.73/2.01  --share_sel_clauses                     true
% 11.73/2.01  --reset_solvers                         false
% 11.73/2.01  --bc_imp_inh                            [conj_cone]
% 11.73/2.01  --conj_cone_tolerance                   3.
% 11.73/2.01  --extra_neg_conj                        none
% 11.73/2.01  --large_theory_mode                     true
% 11.73/2.01  --prolific_symb_bound                   200
% 11.73/2.01  --lt_threshold                          2000
% 11.73/2.01  --clause_weak_htbl                      true
% 11.73/2.01  --gc_record_bc_elim                     false
% 11.73/2.01  
% 11.73/2.01  ------ Preprocessing Options
% 11.73/2.01  
% 11.73/2.01  --preprocessing_flag                    true
% 11.73/2.01  --time_out_prep_mult                    0.1
% 11.73/2.01  --splitting_mode                        input
% 11.73/2.01  --splitting_grd                         true
% 11.73/2.01  --splitting_cvd                         false
% 11.73/2.01  --splitting_cvd_svl                     false
% 11.73/2.01  --splitting_nvd                         32
% 11.73/2.01  --sub_typing                            true
% 11.73/2.01  --prep_gs_sim                           true
% 11.73/2.01  --prep_unflatten                        true
% 11.73/2.01  --prep_res_sim                          true
% 11.73/2.01  --prep_upred                            true
% 11.73/2.01  --prep_sem_filter                       exhaustive
% 11.73/2.01  --prep_sem_filter_out                   false
% 11.73/2.01  --pred_elim                             true
% 11.73/2.01  --res_sim_input                         true
% 11.73/2.01  --eq_ax_congr_red                       true
% 11.73/2.01  --pure_diseq_elim                       true
% 11.73/2.01  --brand_transform                       false
% 11.73/2.01  --non_eq_to_eq                          false
% 11.73/2.01  --prep_def_merge                        true
% 11.73/2.01  --prep_def_merge_prop_impl              false
% 11.73/2.01  --prep_def_merge_mbd                    true
% 11.73/2.01  --prep_def_merge_tr_red                 false
% 11.73/2.01  --prep_def_merge_tr_cl                  false
% 11.73/2.01  --smt_preprocessing                     true
% 11.73/2.01  --smt_ac_axioms                         fast
% 11.73/2.01  --preprocessed_out                      false
% 11.73/2.01  --preprocessed_stats                    false
% 11.73/2.01  
% 11.73/2.01  ------ Abstraction refinement Options
% 11.73/2.01  
% 11.73/2.01  --abstr_ref                             []
% 11.73/2.01  --abstr_ref_prep                        false
% 11.73/2.01  --abstr_ref_until_sat                   false
% 11.73/2.01  --abstr_ref_sig_restrict                funpre
% 11.73/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/2.01  --abstr_ref_under                       []
% 11.73/2.01  
% 11.73/2.01  ------ SAT Options
% 11.73/2.01  
% 11.73/2.01  --sat_mode                              false
% 11.73/2.01  --sat_fm_restart_options                ""
% 11.73/2.01  --sat_gr_def                            false
% 11.73/2.01  --sat_epr_types                         true
% 11.73/2.01  --sat_non_cyclic_types                  false
% 11.73/2.01  --sat_finite_models                     false
% 11.73/2.01  --sat_fm_lemmas                         false
% 11.73/2.01  --sat_fm_prep                           false
% 11.73/2.01  --sat_fm_uc_incr                        true
% 11.73/2.01  --sat_out_model                         small
% 11.73/2.01  --sat_out_clauses                       false
% 11.73/2.01  
% 11.73/2.01  ------ QBF Options
% 11.73/2.01  
% 11.73/2.01  --qbf_mode                              false
% 11.73/2.01  --qbf_elim_univ                         false
% 11.73/2.01  --qbf_dom_inst                          none
% 11.73/2.01  --qbf_dom_pre_inst                      false
% 11.73/2.01  --qbf_sk_in                             false
% 11.73/2.01  --qbf_pred_elim                         true
% 11.73/2.01  --qbf_split                             512
% 11.73/2.01  
% 11.73/2.01  ------ BMC1 Options
% 11.73/2.01  
% 11.73/2.01  --bmc1_incremental                      false
% 11.73/2.01  --bmc1_axioms                           reachable_all
% 11.73/2.01  --bmc1_min_bound                        0
% 11.73/2.01  --bmc1_max_bound                        -1
% 11.73/2.01  --bmc1_max_bound_default                -1
% 11.73/2.01  --bmc1_symbol_reachability              true
% 11.73/2.01  --bmc1_property_lemmas                  false
% 11.73/2.01  --bmc1_k_induction                      false
% 11.73/2.01  --bmc1_non_equiv_states                 false
% 11.73/2.01  --bmc1_deadlock                         false
% 11.73/2.01  --bmc1_ucm                              false
% 11.73/2.01  --bmc1_add_unsat_core                   none
% 11.73/2.01  --bmc1_unsat_core_children              false
% 11.73/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/2.01  --bmc1_out_stat                         full
% 11.73/2.01  --bmc1_ground_init                      false
% 11.73/2.01  --bmc1_pre_inst_next_state              false
% 11.73/2.01  --bmc1_pre_inst_state                   false
% 11.73/2.01  --bmc1_pre_inst_reach_state             false
% 11.73/2.01  --bmc1_out_unsat_core                   false
% 11.73/2.01  --bmc1_aig_witness_out                  false
% 11.73/2.01  --bmc1_verbose                          false
% 11.73/2.01  --bmc1_dump_clauses_tptp                false
% 11.73/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.73/2.01  --bmc1_dump_file                        -
% 11.73/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.73/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.73/2.01  --bmc1_ucm_extend_mode                  1
% 11.73/2.01  --bmc1_ucm_init_mode                    2
% 11.73/2.01  --bmc1_ucm_cone_mode                    none
% 11.73/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.73/2.01  --bmc1_ucm_relax_model                  4
% 11.73/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.73/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/2.01  --bmc1_ucm_layered_model                none
% 11.73/2.01  --bmc1_ucm_max_lemma_size               10
% 11.73/2.01  
% 11.73/2.01  ------ AIG Options
% 11.73/2.01  
% 11.73/2.01  --aig_mode                              false
% 11.73/2.01  
% 11.73/2.01  ------ Instantiation Options
% 11.73/2.01  
% 11.73/2.01  --instantiation_flag                    true
% 11.73/2.01  --inst_sos_flag                         true
% 11.73/2.01  --inst_sos_phase                        true
% 11.73/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/2.01  --inst_lit_sel_side                     none
% 11.73/2.01  --inst_solver_per_active                1400
% 11.73/2.01  --inst_solver_calls_frac                1.
% 11.73/2.01  --inst_passive_queue_type               priority_queues
% 11.73/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/2.01  --inst_passive_queues_freq              [25;2]
% 11.73/2.01  --inst_dismatching                      true
% 11.73/2.01  --inst_eager_unprocessed_to_passive     true
% 11.73/2.01  --inst_prop_sim_given                   true
% 11.73/2.01  --inst_prop_sim_new                     false
% 11.73/2.01  --inst_subs_new                         false
% 11.73/2.01  --inst_eq_res_simp                      false
% 11.73/2.01  --inst_subs_given                       false
% 11.73/2.01  --inst_orphan_elimination               true
% 11.73/2.01  --inst_learning_loop_flag               true
% 11.73/2.01  --inst_learning_start                   3000
% 11.73/2.01  --inst_learning_factor                  2
% 11.73/2.01  --inst_start_prop_sim_after_learn       3
% 11.73/2.01  --inst_sel_renew                        solver
% 11.73/2.01  --inst_lit_activity_flag                true
% 11.73/2.01  --inst_restr_to_given                   false
% 11.73/2.01  --inst_activity_threshold               500
% 11.73/2.01  --inst_out_proof                        true
% 11.73/2.01  
% 11.73/2.01  ------ Resolution Options
% 11.73/2.01  
% 11.73/2.01  --resolution_flag                       false
% 11.73/2.01  --res_lit_sel                           adaptive
% 11.73/2.01  --res_lit_sel_side                      none
% 11.73/2.01  --res_ordering                          kbo
% 11.73/2.01  --res_to_prop_solver                    active
% 11.73/2.01  --res_prop_simpl_new                    false
% 11.73/2.01  --res_prop_simpl_given                  true
% 11.73/2.01  --res_passive_queue_type                priority_queues
% 11.73/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/2.01  --res_passive_queues_freq               [15;5]
% 11.73/2.01  --res_forward_subs                      full
% 11.73/2.01  --res_backward_subs                     full
% 11.73/2.01  --res_forward_subs_resolution           true
% 11.73/2.01  --res_backward_subs_resolution          true
% 11.73/2.01  --res_orphan_elimination                true
% 11.73/2.01  --res_time_limit                        2.
% 11.73/2.01  --res_out_proof                         true
% 11.73/2.01  
% 11.73/2.01  ------ Superposition Options
% 11.73/2.01  
% 11.73/2.01  --superposition_flag                    true
% 11.73/2.01  --sup_passive_queue_type                priority_queues
% 11.73/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.73/2.01  --demod_completeness_check              fast
% 11.73/2.01  --demod_use_ground                      true
% 11.73/2.01  --sup_to_prop_solver                    passive
% 11.73/2.01  --sup_prop_simpl_new                    true
% 11.73/2.01  --sup_prop_simpl_given                  true
% 11.73/2.01  --sup_fun_splitting                     true
% 11.73/2.01  --sup_smt_interval                      50000
% 11.73/2.01  
% 11.73/2.01  ------ Superposition Simplification Setup
% 11.73/2.01  
% 11.73/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/2.01  --sup_immed_triv                        [TrivRules]
% 11.73/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.01  --sup_immed_bw_main                     []
% 11.73/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.01  --sup_input_bw                          []
% 11.73/2.01  
% 11.73/2.01  ------ Combination Options
% 11.73/2.01  
% 11.73/2.01  --comb_res_mult                         3
% 11.73/2.01  --comb_sup_mult                         2
% 11.73/2.01  --comb_inst_mult                        10
% 11.73/2.01  
% 11.73/2.01  ------ Debug Options
% 11.73/2.01  
% 11.73/2.01  --dbg_backtrace                         false
% 11.73/2.01  --dbg_dump_prop_clauses                 false
% 11.73/2.01  --dbg_dump_prop_clauses_file            -
% 11.73/2.01  --dbg_out_stat                          false
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  ------ Proving...
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  % SZS status Theorem for theBenchmark.p
% 11.73/2.01  
% 11.73/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/2.01  
% 11.73/2.01  fof(f2,axiom,(
% 11.73/2.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f14,plain,(
% 11.73/2.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.73/2.01    inference(nnf_transformation,[],[f2])).
% 11.73/2.01  
% 11.73/2.01  fof(f18,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f14])).
% 11.73/2.01  
% 11.73/2.01  fof(f7,axiom,(
% 11.73/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f24,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.73/2.01    inference(cnf_transformation,[],[f7])).
% 11.73/2.01  
% 11.73/2.01  fof(f32,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.73/2.01    inference(definition_unfolding,[],[f18,f24])).
% 11.73/2.01  
% 11.73/2.01  fof(f9,axiom,(
% 11.73/2.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f26,plain,(
% 11.73/2.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f9])).
% 11.73/2.01  
% 11.73/2.01  fof(f1,axiom,(
% 11.73/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f17,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f1])).
% 11.73/2.01  
% 11.73/2.01  fof(f30,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.73/2.01    inference(definition_unfolding,[],[f17,f24,f24])).
% 11.73/2.01  
% 11.73/2.01  fof(f3,axiom,(
% 11.73/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f20,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.73/2.01    inference(cnf_transformation,[],[f3])).
% 11.73/2.01  
% 11.73/2.01  fof(f29,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.73/2.01    inference(definition_unfolding,[],[f20,f24])).
% 11.73/2.01  
% 11.73/2.01  fof(f8,axiom,(
% 11.73/2.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f25,plain,(
% 11.73/2.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f8])).
% 11.73/2.01  
% 11.73/2.01  fof(f4,axiom,(
% 11.73/2.01    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f21,plain,(
% 11.73/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f4])).
% 11.73/2.01  
% 11.73/2.01  fof(f33,plain,(
% 11.73/2.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 11.73/2.01    inference(definition_unfolding,[],[f21,f24,f24,f24,f24])).
% 11.73/2.01  
% 11.73/2.01  fof(f6,axiom,(
% 11.73/2.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f23,plain,(
% 11.73/2.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f6])).
% 11.73/2.01  
% 11.73/2.01  fof(f5,axiom,(
% 11.73/2.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f12,plain,(
% 11.73/2.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.73/2.01    inference(ennf_transformation,[],[f5])).
% 11.73/2.01  
% 11.73/2.01  fof(f22,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.73/2.01    inference(cnf_transformation,[],[f12])).
% 11.73/2.01  
% 11.73/2.01  fof(f34,plain,(
% 11.73/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.73/2.01    inference(definition_unfolding,[],[f22,f24])).
% 11.73/2.01  
% 11.73/2.01  fof(f10,conjecture,(
% 11.73/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.73/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.73/2.01  
% 11.73/2.01  fof(f11,negated_conjecture,(
% 11.73/2.01    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.73/2.01    inference(negated_conjecture,[],[f10])).
% 11.73/2.01  
% 11.73/2.01  fof(f13,plain,(
% 11.73/2.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.73/2.01    inference(ennf_transformation,[],[f11])).
% 11.73/2.01  
% 11.73/2.01  fof(f15,plain,(
% 11.73/2.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 11.73/2.01    introduced(choice_axiom,[])).
% 11.73/2.01  
% 11.73/2.01  fof(f16,plain,(
% 11.73/2.01    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 11.73/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 11.73/2.01  
% 11.73/2.01  fof(f27,plain,(
% 11.73/2.01    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 11.73/2.01    inference(cnf_transformation,[],[f16])).
% 11.73/2.01  
% 11.73/2.01  fof(f19,plain,(
% 11.73/2.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.73/2.01    inference(cnf_transformation,[],[f14])).
% 11.73/2.01  
% 11.73/2.01  fof(f31,plain,(
% 11.73/2.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.73/2.01    inference(definition_unfolding,[],[f19,f24])).
% 11.73/2.01  
% 11.73/2.01  fof(f28,plain,(
% 11.73/2.01    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 11.73/2.01    inference(cnf_transformation,[],[f16])).
% 11.73/2.01  
% 11.73/2.01  cnf(c_3,plain,
% 11.73/2.01      ( ~ r1_xboole_0(X0,X1)
% 11.73/2.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.73/2.01      inference(cnf_transformation,[],[f32]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_70,plain,
% 11.73/2.01      ( ~ r1_xboole_0(X0,X1)
% 11.73/2.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.73/2.01      inference(prop_impl,[status(thm)],[c_3]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_8,plain,
% 11.73/2.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.73/2.01      inference(cnf_transformation,[],[f26]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_169,plain,
% 11.73/2.01      ( X0 != X1
% 11.73/2.01      | k4_xboole_0(X2,X0) != X3
% 11.73/2.01      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
% 11.73/2.01      inference(resolution_lifted,[status(thm)],[c_70,c_8]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_170,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.73/2.01      inference(unflattening,[status(thm)],[c_169]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.73/2.01      inference(cnf_transformation,[],[f30]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1483,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_170,c_1]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_0,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.73/2.01      inference(cnf_transformation,[],[f29]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1522,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1483,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_7,plain,
% 11.73/2.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.73/2.01      inference(cnf_transformation,[],[f25]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_163,plain,
% 11.73/2.01      ( X0 != X1
% 11.73/2.01      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
% 11.73/2.01      | k1_xboole_0 != X2 ),
% 11.73/2.01      inference(resolution_lifted,[status(thm)],[c_70,c_7]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_164,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.73/2.01      inference(unflattening,[status(thm)],[c_163]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_685,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_164,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1526,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_1522,c_685]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_4,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 11.73/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1653,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1526,c_4]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_756,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_4011,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_756,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_28443,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1653,c_4011]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_6,plain,
% 11.73/2.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.73/2.01      inference(cnf_transformation,[],[f23]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_420,plain,
% 11.73/2.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.73/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_5,plain,
% 11.73/2.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.73/2.01      inference(cnf_transformation,[],[f34]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_421,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.73/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.73/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1690,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_420,c_421]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_18600,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1653,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_3946,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_756]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_27155,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_3946,c_1526]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_751,plain,
% 11.73/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_420]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1693,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_751,c_421]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_27180,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_27155,c_1693]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_28960,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(light_normalisation,
% 11.73/2.01                [status(thm)],
% 11.73/2.01                [c_28443,c_1690,c_18600,c_27180]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_750,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_28688,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_4011,c_750]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_28762,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_28688,c_27180]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_28966,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_28960,c_28762]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_28981,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_28966,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_30525,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_28981,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_10,negated_conjecture,
% 11.73/2.01      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
% 11.73/2.01      inference(cnf_transformation,[],[f27]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_419,plain,
% 11.73/2.01      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 11.73/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1691,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = sK0 ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_419,c_421]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2429,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1691,c_4]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2883,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2429,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2892,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(sK0,X0) ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_2883,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_4370,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,X0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_2892]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_30817,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_30525,c_4370]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2431,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1691,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2445,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = sK0 ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_2431,c_1691]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2448,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k5_xboole_0(sK0,sK0))) = k1_xboole_0 ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2445,c_170]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2468,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_2448,c_2445]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_767,plain,
% 11.73/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_5562,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)),X0))))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0)))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2468,c_767]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2453,plain,
% 11.73/2.01      ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2445,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2464,plain,
% 11.73/2.01      ( k5_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_2453,c_2445]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1655,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1526,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_686,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_164,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_687,plain,
% 11.73/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_686,c_164]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1662,plain,
% 11.73/2.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_1655,c_687]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2465,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_2464,c_685,c_1662]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_3510,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2468,c_4]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_3533,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_3510,c_2465]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_5746,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 11.73/2.01      inference(light_normalisation,
% 11.73/2.01                [status(thm)],
% 11.73/2.01                [c_5562,c_2465,c_2468,c_3533]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1150,plain,
% 11.73/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_4,c_751]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2438,plain,
% 11.73/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1691,c_1150]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2713,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2438,c_421]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_1482,plain,
% 11.73/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_170,c_0]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_5008,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_2713,c_1482]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_5058,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_5008,c_2713]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_11853,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_5058]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_13095,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_11853,c_1]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_13502,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_13095]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_13031,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),sK0)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_1,c_11853]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_13234,plain,
% 11.73/2.01      ( k5_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),k1_xboole_0) = k4_xboole_0(sK0,X0) ),
% 11.73/2.01      inference(demodulation,[status(thm)],[c_13031,c_685,c_1690]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_13531,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_13502,c_13234]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_14090,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,X0) ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_5746,c_13531]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_14219,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_14090,c_2892]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_14225,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 11.73/2.01      inference(light_normalisation,
% 11.73/2.01                [status(thm)],
% 11.73/2.01                [c_14219,c_2431,c_2468]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_31003,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_30817,c_14225]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_31368,plain,
% 11.73/2.01      ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) = iProver_top ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_31003,c_751]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_31469,plain,
% 11.73/2.01      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_31368,c_2465]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2865,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 11.73/2.01      inference(superposition,[status(thm)],[c_170,c_2429]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2919,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 11.73/2.01      inference(light_normalisation,[status(thm)],[c_2865,c_2465,c_2468]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_2,plain,
% 11.73/2.01      ( r1_xboole_0(X0,X1)
% 11.73/2.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.73/2.01      inference(cnf_transformation,[],[f31]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_68,plain,
% 11.73/2.01      ( r1_xboole_0(X0,X1)
% 11.73/2.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.73/2.01      inference(prop_impl,[status(thm)],[c_2]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_9,negated_conjecture,
% 11.73/2.01      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 11.73/2.01      inference(cnf_transformation,[],[f28]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_175,plain,
% 11.73/2.01      ( ~ r1_tarski(sK0,sK1)
% 11.73/2.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 11.73/2.01      | sK2 != X1
% 11.73/2.01      | sK0 != X0 ),
% 11.73/2.01      inference(resolution_lifted,[status(thm)],[c_68,c_9]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_176,plain,
% 11.73/2.01      ( ~ r1_tarski(sK0,sK1)
% 11.73/2.01      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 11.73/2.01      inference(unflattening,[status(thm)],[c_175]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(c_177,plain,
% 11.73/2.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
% 11.73/2.01      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.73/2.01      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 11.73/2.01  
% 11.73/2.01  cnf(contradiction,plain,
% 11.73/2.01      ( $false ),
% 11.73/2.01      inference(minisat,[status(thm)],[c_31469,c_2919,c_177]) ).
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/2.01  
% 11.73/2.01  ------                               Statistics
% 11.73/2.01  
% 11.73/2.01  ------ General
% 11.73/2.01  
% 11.73/2.01  abstr_ref_over_cycles:                  0
% 11.73/2.01  abstr_ref_under_cycles:                 0
% 11.73/2.01  gc_basic_clause_elim:                   0
% 11.73/2.01  forced_gc_time:                         0
% 11.73/2.01  parsing_time:                           0.012
% 11.73/2.01  unif_index_cands_time:                  0.
% 11.73/2.01  unif_index_add_time:                    0.
% 11.73/2.01  orderings_time:                         0.
% 11.73/2.01  out_proof_time:                         0.009
% 11.73/2.01  total_time:                             1.126
% 11.73/2.01  num_of_symbols:                         39
% 11.73/2.01  num_of_terms:                           55506
% 11.73/2.01  
% 11.73/2.01  ------ Preprocessing
% 11.73/2.01  
% 11.73/2.01  num_of_splits:                          0
% 11.73/2.01  num_of_split_atoms:                     0
% 11.73/2.01  num_of_reused_defs:                     0
% 11.73/2.01  num_eq_ax_congr_red:                    2
% 11.73/2.01  num_of_sem_filtered_clauses:            1
% 11.73/2.01  num_of_subtypes:                        1
% 11.73/2.01  monotx_restored_types:                  0
% 11.73/2.01  sat_num_of_epr_types:                   0
% 11.73/2.01  sat_num_of_non_cyclic_types:            0
% 11.73/2.01  sat_guarded_non_collapsed_types:        1
% 11.73/2.01  num_pure_diseq_elim:                    0
% 11.73/2.01  simp_replaced_by:                       0
% 11.73/2.01  res_preprocessed:                       44
% 11.73/2.01  prep_upred:                             0
% 11.73/2.01  prep_unflattend:                        20
% 11.73/2.01  smt_new_axioms:                         0
% 11.73/2.01  pred_elim_cands:                        2
% 11.73/2.01  pred_elim:                              1
% 11.73/2.01  pred_elim_cl:                           0
% 11.73/2.01  pred_elim_cycles:                       3
% 11.73/2.01  merged_defs:                            2
% 11.73/2.01  merged_defs_ncl:                        0
% 11.73/2.01  bin_hyper_res:                          2
% 11.73/2.01  prep_cycles:                            3
% 11.73/2.01  pred_elim_time:                         0.003
% 11.73/2.01  splitting_time:                         0.
% 11.73/2.01  sem_filter_time:                        0.
% 11.73/2.01  monotx_time:                            0.
% 11.73/2.01  subtype_inf_time:                       0.
% 11.73/2.01  
% 11.73/2.01  ------ Problem properties
% 11.73/2.01  
% 11.73/2.01  clauses:                                11
% 11.73/2.01  conjectures:                            1
% 11.73/2.01  epr:                                    1
% 11.73/2.01  horn:                                   11
% 11.73/2.01  ground:                                 3
% 11.73/2.01  unary:                                  7
% 11.73/2.01  binary:                                 4
% 11.73/2.01  lits:                                   15
% 11.73/2.01  lits_eq:                                9
% 11.73/2.01  fd_pure:                                0
% 11.73/2.01  fd_pseudo:                              0
% 11.73/2.01  fd_cond:                                0
% 11.73/2.01  fd_pseudo_cond:                         0
% 11.73/2.01  ac_symbols:                             0
% 11.73/2.01  
% 11.73/2.01  ------ Propositional Solver
% 11.73/2.01  
% 11.73/2.01  prop_solver_calls:                      29
% 11.73/2.01  prop_fast_solver_calls:                 356
% 11.73/2.01  smt_solver_calls:                       0
% 11.73/2.01  smt_fast_solver_calls:                  0
% 11.73/2.01  prop_num_of_clauses:                    8255
% 11.73/2.01  prop_preprocess_simplified:             6601
% 11.73/2.01  prop_fo_subsumed:                       0
% 11.73/2.01  prop_solver_time:                       0.
% 11.73/2.01  smt_solver_time:                        0.
% 11.73/2.01  smt_fast_solver_time:                   0.
% 11.73/2.01  prop_fast_solver_time:                  0.
% 11.73/2.01  prop_unsat_core_time:                   0.
% 11.73/2.01  
% 11.73/2.01  ------ QBF
% 11.73/2.01  
% 11.73/2.01  qbf_q_res:                              0
% 11.73/2.01  qbf_num_tautologies:                    0
% 11.73/2.01  qbf_prep_cycles:                        0
% 11.73/2.01  
% 11.73/2.01  ------ BMC1
% 11.73/2.01  
% 11.73/2.01  bmc1_current_bound:                     -1
% 11.73/2.01  bmc1_last_solved_bound:                 -1
% 11.73/2.01  bmc1_unsat_core_size:                   -1
% 11.73/2.01  bmc1_unsat_core_parents_size:           -1
% 11.73/2.01  bmc1_merge_next_fun:                    0
% 11.73/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.73/2.01  
% 11.73/2.01  ------ Instantiation
% 11.73/2.01  
% 11.73/2.01  inst_num_of_clauses:                    1180
% 11.73/2.01  inst_num_in_passive:                    351
% 11.73/2.01  inst_num_in_active:                     644
% 11.73/2.01  inst_num_in_unprocessed:                195
% 11.73/2.01  inst_num_of_loops:                      700
% 11.73/2.01  inst_num_of_learning_restarts:          0
% 11.73/2.01  inst_num_moves_active_passive:          50
% 11.73/2.01  inst_lit_activity:                      0
% 11.73/2.01  inst_lit_activity_moves:                0
% 11.73/2.01  inst_num_tautologies:                   0
% 11.73/2.01  inst_num_prop_implied:                  0
% 11.73/2.01  inst_num_existing_simplified:           0
% 11.73/2.01  inst_num_eq_res_simplified:             0
% 11.73/2.01  inst_num_child_elim:                    0
% 11.73/2.01  inst_num_of_dismatching_blockings:      2624
% 11.73/2.01  inst_num_of_non_proper_insts:           3644
% 11.73/2.01  inst_num_of_duplicates:                 0
% 11.73/2.01  inst_inst_num_from_inst_to_res:         0
% 11.73/2.01  inst_dismatching_checking_time:         0.
% 11.73/2.01  
% 11.73/2.01  ------ Resolution
% 11.73/2.01  
% 11.73/2.01  res_num_of_clauses:                     0
% 11.73/2.01  res_num_in_passive:                     0
% 11.73/2.01  res_num_in_active:                      0
% 11.73/2.01  res_num_of_loops:                       47
% 11.73/2.01  res_forward_subset_subsumed:            298
% 11.73/2.01  res_backward_subset_subsumed:           36
% 11.73/2.01  res_forward_subsumed:                   0
% 11.73/2.01  res_backward_subsumed:                  0
% 11.73/2.01  res_forward_subsumption_resolution:     0
% 11.73/2.01  res_backward_subsumption_resolution:    0
% 11.73/2.01  res_clause_to_clause_subsumption:       36212
% 11.73/2.01  res_orphan_elimination:                 0
% 11.73/2.01  res_tautology_del:                      185
% 11.73/2.01  res_num_eq_res_simplified:              0
% 11.73/2.01  res_num_sel_changes:                    0
% 11.73/2.01  res_moves_from_active_to_pass:          0
% 11.73/2.01  
% 11.73/2.01  ------ Superposition
% 11.73/2.01  
% 11.73/2.01  sup_time_total:                         0.
% 11.73/2.01  sup_time_generating:                    0.
% 11.73/2.01  sup_time_sim_full:                      0.
% 11.73/2.01  sup_time_sim_immed:                     0.
% 11.73/2.01  
% 11.73/2.01  sup_num_of_clauses:                     2353
% 11.73/2.01  sup_num_in_active:                      114
% 11.73/2.01  sup_num_in_passive:                     2239
% 11.73/2.01  sup_num_of_loops:                       139
% 11.73/2.01  sup_fw_superposition:                   5354
% 11.73/2.01  sup_bw_superposition:                   5384
% 11.73/2.01  sup_immediate_simplified:               5455
% 11.73/2.01  sup_given_eliminated:                   13
% 11.73/2.01  comparisons_done:                       0
% 11.73/2.01  comparisons_avoided:                    0
% 11.73/2.01  
% 11.73/2.01  ------ Simplifications
% 11.73/2.01  
% 11.73/2.01  
% 11.73/2.01  sim_fw_subset_subsumed:                 0
% 11.73/2.01  sim_bw_subset_subsumed:                 0
% 11.73/2.01  sim_fw_subsumed:                        939
% 11.73/2.01  sim_bw_subsumed:                        114
% 11.73/2.01  sim_fw_subsumption_res:                 0
% 11.73/2.01  sim_bw_subsumption_res:                 0
% 11.73/2.01  sim_tautology_del:                      0
% 11.73/2.01  sim_eq_tautology_del:                   1273
% 11.73/2.01  sim_eq_res_simp:                        0
% 11.73/2.01  sim_fw_demodulated:                     3682
% 11.73/2.01  sim_bw_demodulated:                     172
% 11.73/2.01  sim_light_normalised:                   2787
% 11.73/2.01  sim_joinable_taut:                      0
% 11.73/2.01  sim_joinable_simp:                      0
% 11.73/2.01  sim_ac_normalised:                      0
% 11.73/2.01  sim_smt_subsumption:                    0
% 11.73/2.01  
%------------------------------------------------------------------------------
