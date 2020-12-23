%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:14 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  112 (10787 expanded)
%              Number of clauses        :   79 (2892 expanded)
%              Number of leaves         :   11 (3031 expanded)
%              Depth                    :   32
%              Number of atoms          :  128 (14420 expanded)
%              Number of equality atoms :  111 (10971 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2)
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2)
        & r1_tarski(X2,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2)
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2)
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f25,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f21,f21])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24,f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f22,f21,f21])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f26,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f24,f21])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_55,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_56,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_55])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_154,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),sK1) = k4_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_56,c_3])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_76,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_6,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_73,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_6,c_5])).

cnf(c_143,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ),
    inference(superposition,[status(thm)],[c_76,c_73])).

cnf(c_144,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_143,c_73])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_144,c_5])).

cnf(c_3490,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK1)))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_154,c_145])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_49,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k4_xboole_0(X1,X2)) = X1
    | k4_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_50,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(unflattening,[status(thm)],[c_49])).

cnf(c_102,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_76,c_50])).

cnf(c_136,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_73])).

cnf(c_149,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_136,c_50,c_76])).

cnf(c_1130,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_102,c_149])).

cnf(c_1136,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1130,c_3])).

cnf(c_265,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_154,c_0])).

cnf(c_305,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))) ),
    inference(superposition,[status(thm)],[c_154,c_265])).

cnf(c_374,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2))) ),
    inference(superposition,[status(thm)],[c_154,c_305])).

cnf(c_490,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2)))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2))) ),
    inference(superposition,[status(thm)],[c_374,c_0])).

cnf(c_266,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) = k4_xboole_0(X0,k5_xboole_0(sK1,k4_xboole_0(X1,sK1))) ),
    inference(superposition,[status(thm)],[c_154,c_3])).

cnf(c_267,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
    inference(demodulation,[status(thm)],[c_266,c_3])).

cnf(c_261,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_154,c_4])).

cnf(c_270,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_261,c_154,c_265])).

cnf(c_386,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_305,c_76])).

cnf(c_392,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_386,c_267,c_270])).

cnf(c_393,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_392,c_154])).

cnf(c_415,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X0),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK1),X0))))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1)) ),
    inference(superposition,[status(thm)],[c_393,c_73])).

cnf(c_432,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1)) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_415,c_73])).

cnf(c_493,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))) = k4_xboole_0(k4_xboole_0(X0,sK2),sK1) ),
    inference(demodulation,[status(thm)],[c_490,c_154,c_267,c_270,c_432])).

cnf(c_494,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))) = k4_xboole_0(X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_493,c_154])).

cnf(c_1315,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_1136,c_494])).

cnf(c_2143,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK2))) = k4_xboole_0(k4_xboole_0(X0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1136,c_1315])).

cnf(c_2184,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK2))) = k4_xboole_0(X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2143,c_154])).

cnf(c_411,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_154,c_393])).

cnf(c_435,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_411,c_393])).

cnf(c_436,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_435,c_154])).

cnf(c_445,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X0),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK1),X0))))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_436,c_73])).

cnf(c_465,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),X1)) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_445,c_73])).

cnf(c_1404,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1136,c_0])).

cnf(c_1433,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_1404,c_149])).

cnf(c_2185,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),sK2) = k4_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_2184,c_267,c_465,c_1433])).

cnf(c_2216,plain,
    ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_2185,c_3])).

cnf(c_3607,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X1,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_3490,c_2216])).

cnf(c_1381,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_1136])).

cnf(c_1455,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1381,c_4])).

cnf(c_4064,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))),k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK2),sK1)))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))) ),
    inference(superposition,[status(thm)],[c_3607,c_1455])).

cnf(c_4139,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4064,c_154,c_265,c_270])).

cnf(c_4081,plain,
    ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK2),sK1))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_3607,c_4])).

cnf(c_4110,plain,
    ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_4081,c_154,c_265])).

cnf(c_5075,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))) = k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))) ),
    inference(superposition,[status(thm)],[c_4110,c_4])).

cnf(c_3542,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3))))) ),
    inference(superposition,[status(thm)],[c_145,c_145])).

cnf(c_3562,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_3542,c_145])).

cnf(c_5199,plain,
    ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_5075,c_3562])).

cnf(c_5295,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4139,c_4139,c_5199])).

cnf(c_5345,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,sK1))) ),
    inference(superposition,[status(thm)],[c_5295,c_73])).

cnf(c_3457,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_145])).

cnf(c_1405,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_1136,c_3])).

cnf(c_1432,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_1405,c_3])).

cnf(c_2361,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) ),
    inference(superposition,[status(thm)],[c_1432,c_73])).

cnf(c_2402,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_2361,c_73])).

cnf(c_3641,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_3457,c_2402])).

cnf(c_86,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_50])).

cnf(c_4066,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK2),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_3607,c_86])).

cnf(c_4134,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))),k4_xboole_0(X0,sK1)) = k4_xboole_0(X0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4066,c_154,c_265,c_270])).

cnf(c_5238,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,sK1)) = k4_xboole_0(X0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4134,c_4134,c_5199])).

cnf(c_5357,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_5345,c_4,c_3641,c_5238])).

cnf(c_5640,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_5357])).

cnf(c_7,negated_conjecture,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_74,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_7,c_5,c_73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5640,c_74])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.43/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/1.00  
% 3.43/1.00  ------  iProver source info
% 3.43/1.00  
% 3.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/1.00  git: non_committed_changes: false
% 3.43/1.00  git: last_make_outside_of_git: false
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    --mode clausify
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         false
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     num_symb
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       true
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     false
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   []
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_full_bw                           [BwDemod]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  ------ Parsing...
% 3.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.43/1.00  ------ Proving...
% 3.43/1.00  ------ Problem Properties 
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  clauses                                 8
% 3.43/1.00  conjectures                             1
% 3.43/1.00  EPR                                     0
% 3.43/1.00  Horn                                    8
% 3.43/1.00  unary                                   8
% 3.43/1.00  binary                                  0
% 3.43/1.00  lits                                    8
% 3.43/1.00  lits eq                                 8
% 3.43/1.00  fd_pure                                 0
% 3.43/1.00  fd_pseudo                               0
% 3.43/1.00  fd_cond                                 0
% 3.43/1.00  fd_pseudo_cond                          0
% 3.43/1.00  AC symbols                              0
% 3.43/1.00  
% 3.43/1.00  ------ Schedule UEQ
% 3.43/1.00  
% 3.43/1.00  ------ pure equality problem: resolution off 
% 3.43/1.00  
% 3.43/1.00  ------ Option_UEQ Time Limit: Unbounded
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  Current options:
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    --mode clausify
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    false
% 3.43/1.00  --inst_sos_flag                         false
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     num_symb
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       false
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    active
% 3.43/1.00  --sup_prop_simpl_new                    false
% 3.43/1.00  --sup_prop_simpl_given                  false
% 3.43/1.00  --sup_fun_splitting                     true
% 3.43/1.00  --sup_smt_interval                      10000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         1
% 3.43/1.00  --comb_sup_mult                         1
% 3.43/1.00  --comb_inst_mult                        1000000
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ Proving...
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS status Theorem for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  fof(f2,axiom,(
% 3.43/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f12,plain,(
% 3.43/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.43/1.00    inference(ennf_transformation,[],[f2])).
% 3.43/1.00  
% 3.43/1.00  fof(f17,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f12])).
% 3.43/1.00  
% 3.43/1.00  fof(f9,axiom,(
% 3.43/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f24,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f9])).
% 3.43/1.00  
% 3.43/1.00  fof(f28,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f17,f24])).
% 3.43/1.00  
% 3.43/1.00  fof(f10,conjecture,(
% 3.43/1.00    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f11,negated_conjecture,(
% 3.43/1.00    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2))),
% 3.43/1.00    inference(negated_conjecture,[],[f10])).
% 3.43/1.00  
% 3.43/1.00  fof(f13,plain,(
% 3.43/1.00    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2) & r1_tarski(X2,X1))),
% 3.43/1.00    inference(ennf_transformation,[],[f11])).
% 3.43/1.00  
% 3.43/1.00  fof(f14,plain,(
% 3.43/1.00    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2) & r1_tarski(X2,X1)) => (k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) & r1_tarski(sK2,sK1))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f15,plain,(
% 3.43/1.00    k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) & r1_tarski(sK2,sK1)),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 3.43/1.00  
% 3.43/1.00  fof(f25,plain,(
% 3.43/1.00    r1_tarski(sK2,sK1)),
% 3.43/1.00    inference(cnf_transformation,[],[f15])).
% 3.43/1.00  
% 3.43/1.00  fof(f4,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f19,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f4])).
% 3.43/1.00  
% 3.43/1.00  fof(f29,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f19,f24])).
% 3.43/1.00  
% 3.43/1.00  fof(f1,axiom,(
% 3.43/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f16,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f1])).
% 3.43/1.00  
% 3.43/1.00  fof(f6,axiom,(
% 3.43/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f21,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f6])).
% 3.43/1.00  
% 3.43/1.00  fof(f27,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f16,f21,f21])).
% 3.43/1.00  
% 3.43/1.00  fof(f5,axiom,(
% 3.43/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f20,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f5])).
% 3.43/1.00  
% 3.43/1.00  fof(f30,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f20,f21])).
% 3.43/1.00  
% 3.43/1.00  fof(f8,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f23,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f8])).
% 3.43/1.00  
% 3.43/1.00  fof(f32,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1)))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f23,f24,f21])).
% 3.43/1.00  
% 3.43/1.00  fof(f7,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f22,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f7])).
% 3.43/1.00  
% 3.43/1.00  fof(f31,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f22,f21,f21])).
% 3.43/1.00  
% 3.43/1.00  fof(f3,axiom,(
% 3.43/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f18,plain,(
% 3.43/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f3])).
% 3.43/1.00  
% 3.43/1.00  fof(f26,plain,(
% 3.43/1.00    k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2)),
% 3.43/1.00    inference(cnf_transformation,[],[f15])).
% 3.43/1.00  
% 3.43/1.00  fof(f33,plain,(
% 3.43/1.00    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 3.43/1.00    inference(definition_unfolding,[],[f26,f24,f21])).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1,plain,
% 3.43/1.00      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 3.43/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8,negated_conjecture,
% 3.43/1.00      ( r1_tarski(sK2,sK1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_55,plain,
% 3.43/1.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | sK1 != X1 | sK2 != X0 ),
% 3.43/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_56,plain,
% 3.43/1.00      ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
% 3.43/1.00      inference(unflattening,[status(thm)],[c_55]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.43/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_154,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),sK1) = k4_xboole_0(X0,sK1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_56,c_3]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_0,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_76,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.43/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_73,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_6,c_5]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_143,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_76,c_73]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_144,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_143,c_73]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_145,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_144,c_5]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3490,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK1)))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_154,c_145]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2,plain,
% 3.43/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f18]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_49,plain,
% 3.43/1.00      ( X0 != X1
% 3.43/1.00      | k5_xboole_0(X2,k4_xboole_0(X1,X2)) = X1
% 3.43/1.00      | k4_xboole_0(X0,X3) != X2 ),
% 3.43/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_50,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.43/1.00      inference(unflattening,[status(thm)],[c_49]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_102,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) = X0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_76,c_50]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_136,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_0,c_73]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_149,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_136,c_50,c_76]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1130,plain,
% 3.43/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_102,c_149]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1136,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1130,c_3]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_265,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_154,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_305,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_154,c_265]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_374,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_154,c_305]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_490,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2)))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),sK2))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_374,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_266,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) = k4_xboole_0(X0,k5_xboole_0(sK1,k4_xboole_0(X1,sK1))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_154,c_3]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_267,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_266,c_3]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_261,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK2),sK1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_154,c_4]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_270,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,sK1) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_261,c_154,c_265]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_386,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),sK2)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_305,c_76]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_392,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_386,c_267,c_270]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_393,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_392,c_154]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_415,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X0),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK1),X0))))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_393,c_73]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_432,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1)) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,X1)) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_415,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_493,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))) = k4_xboole_0(k4_xboole_0(X0,sK2),sK1) ),
% 3.43/1.01      inference(demodulation,
% 3.43/1.01                [status(thm)],
% 3.43/1.01                [c_490,c_154,c_267,c_270,c_432]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_494,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK2))) = k4_xboole_0(X0,sK1) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_493,c_154]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1315,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(X0,sK1) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_1136,c_494]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_2143,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK2))) = k4_xboole_0(k4_xboole_0(X0,sK2),sK1) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_1136,c_1315]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_2184,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK2))) = k4_xboole_0(X0,sK1) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_2143,c_154]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_411,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_154,c_393]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_435,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_411,c_393]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_436,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X0) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_435,c_154]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_445,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X0),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK1),X0))))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),X1)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_436,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_465,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK2),X1)) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,X1)) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_445,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1404,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_1136,c_0]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1433,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_1404,c_149]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_2185,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),sK2) = k4_xboole_0(X0,sK1) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_2184,c_267,c_465,c_1433]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_2216,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_2185,c_3]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_3607,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X1,sK1))) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_3490,c_2216]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1381,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_4,c_1136]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1455,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_1381,c_4]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4064,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))),k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK2),sK1)))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_3607,c_1455]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4139,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,sK1) ),
% 3.43/1.01      inference(light_normalisation,
% 3.43/1.01                [status(thm)],
% 3.43/1.01                [c_4064,c_154,c_265,c_270]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4081,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK2),sK1))) = k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_3607,c_4]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4110,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_4081,c_154,c_265]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5075,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK2))))) = k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_4110,c_4]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_3542,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X3))))) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_145,c_145]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_3562,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_3542,c_145]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5199,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_5075,c_3562]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5295,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,sK1) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_4139,c_4139,c_5199]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5345,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,sK1))) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_5295,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_3457,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_0,c_145]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1405,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_1136,c_3]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1432,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_1405,c_3]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_2361,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X0,X1),X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_1432,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_2402,plain,
% 3.43/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_2361,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_3641,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_3457,c_2402]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_86,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_4,c_50]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4066,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK2),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,sK2) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_3607,c_86]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4134,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK2,k4_xboole_0(X0,sK1))),k4_xboole_0(X0,sK1)) = k4_xboole_0(X0,sK2) ),
% 3.43/1.01      inference(light_normalisation,
% 3.43/1.01                [status(thm)],
% 3.43/1.01                [c_4066,c_154,c_265,c_270]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5238,plain,
% 3.43/1.01      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,sK1)) = k4_xboole_0(X0,sK2) ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_4134,c_4134,c_5199]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5357,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,sK2) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_5345,c_4,c_3641,c_5238]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5640,plain,
% 3.43/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
% 3.43/1.01      inference(instantiation,[status(thm)],[c_5357]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_7,negated_conjecture,
% 3.43/1.01      ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
% 3.43/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_74,plain,
% 3.43/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_7,c_5,c_73]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(contradiction,plain,
% 3.43/1.01      ( $false ),
% 3.43/1.01      inference(minisat,[status(thm)],[c_5640,c_74]) ).
% 3.43/1.01  
% 3.43/1.01  
% 3.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/1.01  
% 3.43/1.01  ------                               Statistics
% 3.43/1.01  
% 3.43/1.01  ------ General
% 3.43/1.01  
% 3.43/1.01  abstr_ref_over_cycles:                  0
% 3.43/1.01  abstr_ref_under_cycles:                 0
% 3.43/1.01  gc_basic_clause_elim:                   0
% 3.43/1.01  forced_gc_time:                         0
% 3.43/1.01  parsing_time:                           0.007
% 3.43/1.01  unif_index_cands_time:                  0.
% 3.43/1.01  unif_index_add_time:                    0.
% 3.43/1.01  orderings_time:                         0.
% 3.43/1.01  out_proof_time:                         0.008
% 3.43/1.01  total_time:                             0.239
% 3.43/1.01  num_of_symbols:                         38
% 3.43/1.01  num_of_terms:                           10633
% 3.43/1.01  
% 3.43/1.01  ------ Preprocessing
% 3.43/1.01  
% 3.43/1.01  num_of_splits:                          0
% 3.43/1.01  num_of_split_atoms:                     1
% 3.43/1.01  num_of_reused_defs:                     0
% 3.43/1.01  num_eq_ax_congr_red:                    0
% 3.43/1.01  num_of_sem_filtered_clauses:            0
% 3.43/1.01  num_of_subtypes:                        0
% 3.43/1.01  monotx_restored_types:                  0
% 3.43/1.01  sat_num_of_epr_types:                   0
% 3.43/1.01  sat_num_of_non_cyclic_types:            0
% 3.43/1.01  sat_guarded_non_collapsed_types:        0
% 3.43/1.01  num_pure_diseq_elim:                    0
% 3.43/1.01  simp_replaced_by:                       0
% 3.43/1.01  res_preprocessed:                       29
% 3.43/1.01  prep_upred:                             0
% 3.43/1.01  prep_unflattend:                        4
% 3.43/1.01  smt_new_axioms:                         0
% 3.43/1.01  pred_elim_cands:                        0
% 3.43/1.01  pred_elim:                              1
% 3.43/1.01  pred_elim_cl:                           1
% 3.43/1.01  pred_elim_cycles:                       2
% 3.43/1.01  merged_defs:                            0
% 3.43/1.01  merged_defs_ncl:                        0
% 3.43/1.01  bin_hyper_res:                          0
% 3.43/1.01  prep_cycles:                            3
% 3.43/1.01  pred_elim_time:                         0.
% 3.43/1.01  splitting_time:                         0.
% 3.43/1.01  sem_filter_time:                        0.
% 3.43/1.01  monotx_time:                            0.
% 3.43/1.01  subtype_inf_time:                       0.
% 3.43/1.01  
% 3.43/1.01  ------ Problem properties
% 3.43/1.01  
% 3.43/1.01  clauses:                                8
% 3.43/1.01  conjectures:                            1
% 3.43/1.01  epr:                                    0
% 3.43/1.01  horn:                                   8
% 3.43/1.01  ground:                                 2
% 3.43/1.01  unary:                                  8
% 3.43/1.01  binary:                                 0
% 3.43/1.01  lits:                                   8
% 3.43/1.01  lits_eq:                                8
% 3.43/1.01  fd_pure:                                0
% 3.43/1.01  fd_pseudo:                              0
% 3.43/1.01  fd_cond:                                0
% 3.43/1.01  fd_pseudo_cond:                         0
% 3.43/1.01  ac_symbols:                             0
% 3.43/1.01  
% 3.43/1.01  ------ Propositional Solver
% 3.43/1.01  
% 3.43/1.01  prop_solver_calls:                      17
% 3.43/1.01  prop_fast_solver_calls:                 74
% 3.43/1.01  smt_solver_calls:                       0
% 3.43/1.01  smt_fast_solver_calls:                  0
% 3.43/1.01  prop_num_of_clauses:                    161
% 3.43/1.01  prop_preprocess_simplified:             406
% 3.43/1.01  prop_fo_subsumed:                       0
% 3.43/1.01  prop_solver_time:                       0.
% 3.43/1.01  smt_solver_time:                        0.
% 3.43/1.01  smt_fast_solver_time:                   0.
% 3.43/1.01  prop_fast_solver_time:                  0.
% 3.43/1.01  prop_unsat_core_time:                   0.
% 3.43/1.01  
% 3.43/1.01  ------ QBF
% 3.43/1.01  
% 3.43/1.01  qbf_q_res:                              0
% 3.43/1.01  qbf_num_tautologies:                    0
% 3.43/1.01  qbf_prep_cycles:                        0
% 3.43/1.01  
% 3.43/1.01  ------ BMC1
% 3.43/1.01  
% 3.43/1.01  bmc1_current_bound:                     -1
% 3.43/1.01  bmc1_last_solved_bound:                 -1
% 3.43/1.01  bmc1_unsat_core_size:                   -1
% 3.43/1.01  bmc1_unsat_core_parents_size:           -1
% 3.43/1.01  bmc1_merge_next_fun:                    0
% 3.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.43/1.01  
% 3.43/1.01  ------ Instantiation
% 3.43/1.01  
% 3.43/1.01  inst_num_of_clauses:                    0
% 3.43/1.01  inst_num_in_passive:                    0
% 3.43/1.01  inst_num_in_active:                     0
% 3.43/1.01  inst_num_in_unprocessed:                0
% 3.43/1.01  inst_num_of_loops:                      0
% 3.43/1.01  inst_num_of_learning_restarts:          0
% 3.43/1.01  inst_num_moves_active_passive:          0
% 3.43/1.01  inst_lit_activity:                      0
% 3.43/1.01  inst_lit_activity_moves:                0
% 3.43/1.01  inst_num_tautologies:                   0
% 3.43/1.01  inst_num_prop_implied:                  0
% 3.43/1.01  inst_num_existing_simplified:           0
% 3.43/1.01  inst_num_eq_res_simplified:             0
% 3.43/1.01  inst_num_child_elim:                    0
% 3.43/1.01  inst_num_of_dismatching_blockings:      0
% 3.43/1.01  inst_num_of_non_proper_insts:           0
% 3.43/1.01  inst_num_of_duplicates:                 0
% 3.43/1.01  inst_inst_num_from_inst_to_res:         0
% 3.43/1.01  inst_dismatching_checking_time:         0.
% 3.43/1.01  
% 3.43/1.01  ------ Resolution
% 3.43/1.01  
% 3.43/1.01  res_num_of_clauses:                     0
% 3.43/1.01  res_num_in_passive:                     0
% 3.43/1.01  res_num_in_active:                      0
% 3.43/1.01  res_num_of_loops:                       32
% 3.43/1.01  res_forward_subset_subsumed:            0
% 3.43/1.01  res_backward_subset_subsumed:           0
% 3.43/1.01  res_forward_subsumed:                   0
% 3.43/1.01  res_backward_subsumed:                  0
% 3.43/1.01  res_forward_subsumption_resolution:     0
% 3.43/1.01  res_backward_subsumption_resolution:    0
% 3.43/1.01  res_clause_to_clause_subsumption:       8904
% 3.43/1.01  res_orphan_elimination:                 0
% 3.43/1.01  res_tautology_del:                      0
% 3.43/1.01  res_num_eq_res_simplified:              0
% 3.43/1.01  res_num_sel_changes:                    0
% 3.43/1.01  res_moves_from_active_to_pass:          0
% 3.43/1.01  
% 3.43/1.01  ------ Superposition
% 3.43/1.01  
% 3.43/1.01  sup_time_total:                         0.
% 3.43/1.01  sup_time_generating:                    0.
% 3.43/1.01  sup_time_sim_full:                      0.
% 3.43/1.01  sup_time_sim_immed:                     0.
% 3.43/1.01  
% 3.43/1.01  sup_num_of_clauses:                     770
% 3.43/1.01  sup_num_in_active:                      57
% 3.43/1.01  sup_num_in_passive:                     713
% 3.43/1.01  sup_num_of_loops:                       79
% 3.43/1.01  sup_fw_superposition:                   1237
% 3.43/1.01  sup_bw_superposition:                   1625
% 3.43/1.01  sup_immediate_simplified:               2009
% 3.43/1.01  sup_given_eliminated:                   6
% 3.43/1.01  comparisons_done:                       0
% 3.43/1.01  comparisons_avoided:                    0
% 3.43/1.01  
% 3.43/1.01  ------ Simplifications
% 3.43/1.01  
% 3.43/1.01  
% 3.43/1.01  sim_fw_subset_subsumed:                 0
% 3.43/1.01  sim_bw_subset_subsumed:                 0
% 3.43/1.01  sim_fw_subsumed:                        203
% 3.43/1.01  sim_bw_subsumed:                        26
% 3.43/1.01  sim_fw_subsumption_res:                 0
% 3.43/1.01  sim_bw_subsumption_res:                 0
% 3.43/1.01  sim_tautology_del:                      0
% 3.43/1.01  sim_eq_tautology_del:                   656
% 3.43/1.01  sim_eq_res_simp:                        0
% 3.43/1.01  sim_fw_demodulated:                     1742
% 3.43/1.01  sim_bw_demodulated:                     71
% 3.43/1.01  sim_light_normalised:                   834
% 3.43/1.01  sim_joinable_taut:                      0
% 3.43/1.01  sim_joinable_simp:                      0
% 3.43/1.01  sim_ac_normalised:                      0
% 3.43/1.01  sim_smt_subsumption:                    0
% 3.43/1.01  
%------------------------------------------------------------------------------
