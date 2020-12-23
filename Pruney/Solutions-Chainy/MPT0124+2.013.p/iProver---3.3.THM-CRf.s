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
% DateTime   : Thu Dec  3 11:26:14 EST 2020

% Result     : Theorem 47.02s
% Output     : CNFRefutation 47.02s
% Verified   : 
% Statistics : Number of formulae       :  156 (17615 expanded)
%              Number of clauses        :  112 (4411 expanded)
%              Number of leaves         :   17 (5359 expanded)
%              Depth                    :   39
%              Number of atoms          :  185 (19753 expanded)
%              Number of equality atoms :  162 (17183 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f32,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f27,f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31,f27])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f27,f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f29,f31,f27])).

fof(f33,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f33,f31,f27])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_180,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_181,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_787,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_180,c_181])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1337,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_787,c_4])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_182,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_470,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_182])).

cnf(c_790,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_470,c_181])).

cnf(c_1,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_206,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_9,c_7])).

cnf(c_21088,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_790,c_1,c_7,c_206])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_958,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_21165,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_21088,c_958])).

cnf(c_21276,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_21165,c_6])).

cnf(c_21459,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_21276,c_4])).

cnf(c_21616,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_21459,c_4])).

cnf(c_36624,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_1337,c_21616])).

cnf(c_37202,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),X1) ),
    inference(demodulation,[status(thm)],[c_36624,c_21616])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_183,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2349,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_180,c_183])).

cnf(c_3050,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),sK1) = k4_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_2349,c_4])).

cnf(c_37204,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
    inference(light_normalisation,[status(thm)],[c_37202,c_3050])).

cnf(c_8,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1060,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_161092,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK2,sK1),sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_37204,c_1060])).

cnf(c_38184,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_37204,c_0])).

cnf(c_38217,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))),sK2) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_37204,c_958])).

cnf(c_21110,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))) = X0 ),
    inference(superposition,[status(thm)],[c_958,c_21088])).

cnf(c_21337,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_21110,c_6])).

cnf(c_22363,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_21337,c_6])).

cnf(c_38295,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_38217,c_7,c_21616,c_22363])).

cnf(c_38349,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_38184,c_38295])).

cnf(c_22325,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X1,sK1)))) = X0 ),
    inference(superposition,[status(thm)],[c_1337,c_21337])).

cnf(c_25580,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_22325,c_6])).

cnf(c_38351,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_38349,c_25580])).

cnf(c_38352,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_38351,c_1337])).

cnf(c_39229,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_38352,c_206])).

cnf(c_39596,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(demodulation,[status(thm)],[c_39229,c_1,c_22363])).

cnf(c_39597,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_39596,c_6])).

cnf(c_980,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_70457,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) ),
    inference(superposition,[status(thm)],[c_39597,c_980])).

cnf(c_72026,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2) ),
    inference(demodulation,[status(thm)],[c_70457,c_7,c_21088,c_21616])).

cnf(c_15172,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK2))),sK1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_958,c_3050])).

cnf(c_75097,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(X1,X1),X1)),sK1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X0),sK2))),sK1) ),
    inference(superposition,[status(thm)],[c_72026,c_15172])).

cnf(c_44819,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),X0) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_39597,c_958])).

cnf(c_44930,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),X0) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_44819,c_7,c_21088,c_21276,c_21616])).

cnf(c_70458,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,sK2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,sK2))))) ),
    inference(superposition,[status(thm)],[c_44930,c_980])).

cnf(c_72023,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_70458,c_7,c_21088,c_21616])).

cnf(c_73356,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1337,c_72023])).

cnf(c_75996,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_73356,c_21616])).

cnf(c_463,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_17082,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK2))),sK1))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_15172,c_463])).

cnf(c_17314,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK2))),sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_17082,c_7])).

cnf(c_17315,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK2),sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_17314,c_6,c_7])).

cnf(c_17316,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_17315,c_3050])).

cnf(c_21403,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_21276])).

cnf(c_21731,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_21403,c_6])).

cnf(c_37665,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_21731,c_8])).

cnf(c_48290,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) = sK1 ),
    inference(superposition,[status(thm)],[c_17316,c_37665])).

cnf(c_48479,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_48290,c_6,c_21088])).

cnf(c_57032,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,X1)),sK1) = k4_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_48479,c_4])).

cnf(c_57436,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_57032])).

cnf(c_58068,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(X0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_57436,c_4])).

cnf(c_58248,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_58068,c_4,c_21276])).

cnf(c_76039,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_75996,c_58248])).

cnf(c_76868,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),sK1) ),
    inference(demodulation,[status(thm)],[c_75097,c_76039])).

cnf(c_76870,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),sK1) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_76868,c_7,c_21088,c_57032,c_57436])).

cnf(c_44748,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_39597])).

cnf(c_102810,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_44748,c_958])).

cnf(c_102972,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_102810,c_7,c_21088,c_58248])).

cnf(c_103373,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))) ),
    inference(superposition,[status(thm)],[c_102972,c_980])).

cnf(c_105018,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k4_xboole_0(X1,sK2),X1) ),
    inference(demodulation,[status(thm)],[c_103373,c_7,c_21088,c_21616])).

cnf(c_116370,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),sK2),sK1) ),
    inference(superposition,[status(thm)],[c_105018,c_57032])).

cnf(c_74829,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),sK2))),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(sK2,X1),sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_72026,c_15172])).

cnf(c_3531,plain,
    ( k4_xboole_0(X0,k5_xboole_0(sK1,k4_xboole_0(X1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) ),
    inference(superposition,[status(thm)],[c_3050,c_4])).

cnf(c_3547,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
    inference(demodulation,[status(thm)],[c_3531,c_4])).

cnf(c_809,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_823,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_809,c_4])).

cnf(c_11989,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),sK2) ),
    inference(superposition,[status(thm)],[c_3547,c_823])).

cnf(c_12220,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),sK2) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
    inference(demodulation,[status(thm)],[c_11989,c_6])).

cnf(c_75825,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(X0,X0),sK2) ),
    inference(superposition,[status(thm)],[c_73356,c_12220])).

cnf(c_76371,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_75825,c_58248])).

cnf(c_77531,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(sK2,X1),sK2)),sK1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),sK1) ),
    inference(light_normalisation,[status(thm)],[c_74829,c_76371])).

cnf(c_77532,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(sK1,sK1)),sK1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),sK1) ),
    inference(demodulation,[status(thm)],[c_77531,c_76039])).

cnf(c_77534,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),sK1) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_77532,c_7,c_21088,c_57032,c_57436])).

cnf(c_117299,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),sK2),sK1) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_116370,c_3050,c_21276,c_77534])).

cnf(c_119621,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),sK2),sK1),sK1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_117299,c_77534])).

cnf(c_120076,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_119621,c_3050,c_21276])).

cnf(c_44117,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_37665])).

cnf(c_120911,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(X1,X1)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_120076,c_44117])).

cnf(c_121940,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X1,X1)) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_120911,c_6])).

cnf(c_162011,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_161092,c_76870,c_121940])).

cnf(c_93,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2415,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X2,X3))
    | k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2))) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_93])).

cnf(c_92,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_508,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_93,c_92])).

cnf(c_8970,plain,
    ( X0 = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2)))
    | X0 != k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(resolution,[status(thm)],[c_2415,c_508])).

cnf(c_10,negated_conjecture,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_94966,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_8970,c_10])).

cnf(c_94,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_897,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X1,X3) = k4_xboole_0(X0,X2) ),
    inference(resolution,[status(thm)],[c_94,c_508])).

cnf(c_96913,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2
    | sK0 != sK0 ),
    inference(resolution,[status(thm)],[c_94966,c_897])).

cnf(c_96914,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_96913])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_162011,c_96914])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:57:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 47.02/6.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.02/6.49  
% 47.02/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.02/6.49  
% 47.02/6.49  ------  iProver source info
% 47.02/6.49  
% 47.02/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.02/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.02/6.49  git: non_committed_changes: false
% 47.02/6.49  git: last_make_outside_of_git: false
% 47.02/6.49  
% 47.02/6.49  ------ 
% 47.02/6.49  ------ Parsing...
% 47.02/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.02/6.49  
% 47.02/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 47.02/6.49  
% 47.02/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.02/6.49  
% 47.02/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.02/6.49  ------ Proving...
% 47.02/6.49  ------ Problem Properties 
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  clauses                                 12
% 47.02/6.49  conjectures                             2
% 47.02/6.49  EPR                                     1
% 47.02/6.49  Horn                                    12
% 47.02/6.49  unary                                   10
% 47.02/6.49  binary                                  2
% 47.02/6.49  lits                                    14
% 47.02/6.49  lits eq                                 10
% 47.02/6.49  fd_pure                                 0
% 47.02/6.49  fd_pseudo                               0
% 47.02/6.49  fd_cond                                 0
% 47.02/6.49  fd_pseudo_cond                          0
% 47.02/6.49  AC symbols                              0
% 47.02/6.49  
% 47.02/6.49  ------ Input Options Time Limit: Unbounded
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  ------ 
% 47.02/6.49  Current options:
% 47.02/6.49  ------ 
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  ------ Proving...
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  % SZS status Theorem for theBenchmark.p
% 47.02/6.49  
% 47.02/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.02/6.49  
% 47.02/6.49  fof(f13,conjecture,(
% 47.02/6.49    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f14,negated_conjecture,(
% 47.02/6.49    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 47.02/6.49    inference(negated_conjecture,[],[f13])).
% 47.02/6.49  
% 47.02/6.49  fof(f17,plain,(
% 47.02/6.49    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 47.02/6.49    inference(ennf_transformation,[],[f14])).
% 47.02/6.49  
% 47.02/6.49  fof(f18,plain,(
% 47.02/6.49    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 47.02/6.49    introduced(choice_axiom,[])).
% 47.02/6.49  
% 47.02/6.49  fof(f19,plain,(
% 47.02/6.49    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 47.02/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 47.02/6.49  
% 47.02/6.49  fof(f32,plain,(
% 47.02/6.49    r1_tarski(sK2,sK1)),
% 47.02/6.49    inference(cnf_transformation,[],[f19])).
% 47.02/6.49  
% 47.02/6.49  fof(f6,axiom,(
% 47.02/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f16,plain,(
% 47.02/6.49    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 47.02/6.49    inference(ennf_transformation,[],[f6])).
% 47.02/6.49  
% 47.02/6.49  fof(f25,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 47.02/6.49    inference(cnf_transformation,[],[f16])).
% 47.02/6.49  
% 47.02/6.49  fof(f12,axiom,(
% 47.02/6.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f31,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 47.02/6.49    inference(cnf_transformation,[],[f12])).
% 47.02/6.49  
% 47.02/6.49  fof(f39,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 47.02/6.49    inference(definition_unfolding,[],[f25,f31])).
% 47.02/6.49  
% 47.02/6.49  fof(f5,axiom,(
% 47.02/6.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f24,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 47.02/6.49    inference(cnf_transformation,[],[f5])).
% 47.02/6.49  
% 47.02/6.49  fof(f38,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 47.02/6.49    inference(definition_unfolding,[],[f24,f31])).
% 47.02/6.49  
% 47.02/6.49  fof(f7,axiom,(
% 47.02/6.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f26,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 47.02/6.49    inference(cnf_transformation,[],[f7])).
% 47.02/6.49  
% 47.02/6.49  fof(f8,axiom,(
% 47.02/6.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f27,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 47.02/6.49    inference(cnf_transformation,[],[f8])).
% 47.02/6.49  
% 47.02/6.49  fof(f40,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 47.02/6.49    inference(definition_unfolding,[],[f26,f27])).
% 47.02/6.49  
% 47.02/6.49  fof(f4,axiom,(
% 47.02/6.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f23,plain,(
% 47.02/6.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 47.02/6.49    inference(cnf_transformation,[],[f4])).
% 47.02/6.49  
% 47.02/6.49  fof(f37,plain,(
% 47.02/6.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 47.02/6.49    inference(definition_unfolding,[],[f23,f27])).
% 47.02/6.49  
% 47.02/6.49  fof(f2,axiom,(
% 47.02/6.49    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f21,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 47.02/6.49    inference(cnf_transformation,[],[f2])).
% 47.02/6.49  
% 47.02/6.49  fof(f35,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) )),
% 47.02/6.49    inference(definition_unfolding,[],[f21,f27,f31])).
% 47.02/6.49  
% 47.02/6.49  fof(f9,axiom,(
% 47.02/6.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f28,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 47.02/6.49    inference(cnf_transformation,[],[f9])).
% 47.02/6.49  
% 47.02/6.49  fof(f41,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 47.02/6.49    inference(definition_unfolding,[],[f28,f27,f27])).
% 47.02/6.49  
% 47.02/6.49  fof(f11,axiom,(
% 47.02/6.49    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f30,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 47.02/6.49    inference(cnf_transformation,[],[f11])).
% 47.02/6.49  
% 47.02/6.49  fof(f43,plain,(
% 47.02/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1)))) )),
% 47.02/6.49    inference(definition_unfolding,[],[f30,f31,f27])).
% 47.02/6.49  
% 47.02/6.49  fof(f1,axiom,(
% 47.02/6.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f20,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 47.02/6.49    inference(cnf_transformation,[],[f1])).
% 47.02/6.49  
% 47.02/6.49  fof(f34,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 47.02/6.49    inference(definition_unfolding,[],[f20,f27,f27])).
% 47.02/6.49  
% 47.02/6.49  fof(f3,axiom,(
% 47.02/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f15,plain,(
% 47.02/6.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 47.02/6.49    inference(ennf_transformation,[],[f3])).
% 47.02/6.49  
% 47.02/6.49  fof(f22,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 47.02/6.49    inference(cnf_transformation,[],[f15])).
% 47.02/6.49  
% 47.02/6.49  fof(f36,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 47.02/6.49    inference(definition_unfolding,[],[f22,f31])).
% 47.02/6.49  
% 47.02/6.49  fof(f10,axiom,(
% 47.02/6.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 47.02/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.02/6.49  
% 47.02/6.49  fof(f29,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 47.02/6.49    inference(cnf_transformation,[],[f10])).
% 47.02/6.49  
% 47.02/6.49  fof(f42,plain,(
% 47.02/6.49    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 47.02/6.49    inference(definition_unfolding,[],[f29,f31,f27])).
% 47.02/6.49  
% 47.02/6.49  fof(f33,plain,(
% 47.02/6.49    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 47.02/6.49    inference(cnf_transformation,[],[f19])).
% 47.02/6.49  
% 47.02/6.49  fof(f44,plain,(
% 47.02/6.49    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 47.02/6.49    inference(definition_unfolding,[],[f33,f31,f27])).
% 47.02/6.49  
% 47.02/6.49  cnf(c_11,negated_conjecture,
% 47.02/6.49      ( r1_tarski(sK2,sK1) ),
% 47.02/6.49      inference(cnf_transformation,[],[f32]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_180,plain,
% 47.02/6.49      ( r1_tarski(sK2,sK1) = iProver_top ),
% 47.02/6.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_5,plain,
% 47.02/6.49      ( ~ r1_tarski(X0,X1)
% 47.02/6.49      | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
% 47.02/6.49      inference(cnf_transformation,[],[f39]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_181,plain,
% 47.02/6.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1
% 47.02/6.49      | r1_tarski(X0,X1) != iProver_top ),
% 47.02/6.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_787,plain,
% 47.02/6.49      ( k5_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_180,c_181]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_4,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.02/6.49      inference(cnf_transformation,[],[f38]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_1337,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_787,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_6,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 47.02/6.49      inference(cnf_transformation,[],[f40]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_3,plain,
% 47.02/6.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 47.02/6.49      inference(cnf_transformation,[],[f37]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_182,plain,
% 47.02/6.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 47.02/6.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_470,plain,
% 47.02/6.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_6,c_182]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_790,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_470,c_181]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_1,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 47.02/6.49      inference(cnf_transformation,[],[f35]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_7,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 47.02/6.49      inference(cnf_transformation,[],[f41]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_9,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 47.02/6.49      inference(cnf_transformation,[],[f43]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_206,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_9,c_7]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21088,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_790,c_1,c_7,c_206]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_0,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 47.02/6.49      inference(cnf_transformation,[],[f34]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_958,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21165,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) = k4_xboole_0(X0,X1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_21088,c_958]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21276,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_21165,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21459,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_21276,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21616,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_21459,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_36624,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK2)),X1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_1337,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_37202,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),sK1),X1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_36624,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_2,plain,
% 47.02/6.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 47.02/6.49      inference(cnf_transformation,[],[f36]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_183,plain,
% 47.02/6.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 47.02/6.49      | r1_tarski(X0,X1) != iProver_top ),
% 47.02/6.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_2349,plain,
% 47.02/6.49      ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_180,c_183]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_3050,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK2),sK1) = k4_xboole_0(X0,sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_2349,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_37204,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_37202,c_3050]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_8,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 47.02/6.49      inference(cnf_transformation,[],[f42]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_1060,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X1 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_161092,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK2,sK1),sK1)) = sK2 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_37204,c_1060]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_38184,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_37204,c_0]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_38217,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))),sK2) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_37204,c_958]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21110,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))) = X0 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_958,c_21088]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21337,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = X0 ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_21110,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_22363,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_21337,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_38295,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_38217,c_7,c_21616,c_22363]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_38349,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1))) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_38184,c_38295]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_22325,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X1,sK1)))) = X0 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_1337,c_21337]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_25580,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK1)) = k4_xboole_0(sK1,sK2) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_22325,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_38351,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_38349,c_25580]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_38352,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),sK2) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_38351,c_1337]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_39229,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_38352,c_206]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_39596,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_39229,c_1,c_22363]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_39597,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X0)) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_39596,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_980,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_70457,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(k4_xboole_0(sK2,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_39597,c_980]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_72026,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k4_xboole_0(sK2,X1),sK2) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_70457,c_7,c_21088,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_15172,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK2))),sK1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_958,c_3050]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_75097,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(X1,X1),X1)),sK1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,X0),sK2))),sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_72026,c_15172]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_44819,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),X0) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_39597,c_958]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_44930,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK2,sK2),X0) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(demodulation,
% 47.02/6.49                [status(thm)],
% 47.02/6.49                [c_44819,c_7,c_21088,c_21276,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_70458,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,sK2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,sK2))))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_44930,c_980]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_72023,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X1,X1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_70458,c_7,c_21088,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_73356,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,X0) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_1337,c_72023]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_75996,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_73356,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_463,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_17082,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK2))),sK1))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_15172,c_463]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_17314,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sK2))),sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_17082,c_7]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_17315,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,sK2),sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_17314,c_6,c_7]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_17316,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_17315,c_3050]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21403,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_6,c_21276]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_21731,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_21403,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_37665,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_21731,c_8]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_48290,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) = sK1 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_17316,c_37665]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_48479,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = sK1 ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_48290,c_6,c_21088]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_57032,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,X1)),sK1) = k4_xboole_0(X0,sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_48479,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_57436,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_6,c_57032]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_58068,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(X0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_57436,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_58248,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(X0,sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_58068,c_4,c_21276]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_76039,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_75996,c_58248]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_76868,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK1,sK1)),sK1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_75097,c_76039]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_76870,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK2,X0),sK1) = k4_xboole_0(sK2,sK2) ),
% 47.02/6.49      inference(demodulation,
% 47.02/6.49                [status(thm)],
% 47.02/6.49                [c_76868,c_7,c_21088,c_57032,c_57436]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_44748,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_0,c_39597]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_102810,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),k4_xboole_0(X0,sK2)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_44748,c_958]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_102972,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(demodulation,
% 47.02/6.49                [status(thm)],
% 47.02/6.49                [c_102810,c_7,c_21088,c_58248]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_103373,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1)))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_102972,c_980]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_105018,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k4_xboole_0(X1,sK2),X1) ),
% 47.02/6.49      inference(demodulation,
% 47.02/6.49                [status(thm)],
% 47.02/6.49                [c_103373,c_7,c_21088,c_21616]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_116370,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),X0),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X1),sK2),sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_105018,c_57032]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_74829,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),sK2))),sK1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(sK2,X1),sK2)),sK1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_72026,c_15172]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_3531,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k5_xboole_0(sK1,k4_xboole_0(X1,sK1))) = k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_3050,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_3547,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X1,sK2)) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_3531,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_809,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_823,plain,
% 47.02/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_809,c_4]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_11989,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(k4_xboole_0(X0,sK1),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),sK2) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_3547,c_823]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_12220,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK1),X1),sK2) = k4_xboole_0(k4_xboole_0(X0,sK1),X1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_11989,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_75825,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(X0,X0),sK2) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_73356,c_12220]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_76371,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X0),sK2) = k4_xboole_0(sK1,sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_75825,c_58248]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_77531,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(sK2,X1),sK2)),sK1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),sK1) ),
% 47.02/6.49      inference(light_normalisation,[status(thm)],[c_74829,c_76371]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_77532,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(sK1,sK1)),sK1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))),sK1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_77531,c_76039]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_77534,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(X0,X0),sK1) = k4_xboole_0(X0,X0) ),
% 47.02/6.49      inference(demodulation,
% 47.02/6.49                [status(thm)],
% 47.02/6.49                [c_77532,c_7,c_21088,c_57032,c_57436]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_117299,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),sK2),sK1) = k4_xboole_0(X1,X1) ),
% 47.02/6.49      inference(demodulation,
% 47.02/6.49                [status(thm)],
% 47.02/6.49                [c_116370,c_3050,c_21276,c_77534]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_119621,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,X0),sK2),sK1),sK1) = k4_xboole_0(X1,X1) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_117299,c_77534]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_120076,plain,
% 47.02/6.49      ( k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(X1,X1) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_119621,c_3050,c_21276]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_44117,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_0,c_37665]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_120911,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(X1,X1)) = k4_xboole_0(sK1,X0) ),
% 47.02/6.49      inference(superposition,[status(thm)],[c_120076,c_44117]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_121940,plain,
% 47.02/6.49      ( k5_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X1,X1)) = k4_xboole_0(sK1,X0) ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_120911,c_6]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_162011,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 47.02/6.49      inference(demodulation,[status(thm)],[c_161092,c_76870,c_121940]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_93,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_2415,plain,
% 47.02/6.49      ( X0 != k4_xboole_0(X1,k4_xboole_0(X2,X3))
% 47.02/6.49      | k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2))) = X0 ),
% 47.02/6.49      inference(resolution,[status(thm)],[c_9,c_93]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_92,plain,( X0 = X0 ),theory(equality) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_508,plain,
% 47.02/6.49      ( X0 != X1 | X1 = X0 ),
% 47.02/6.49      inference(resolution,[status(thm)],[c_93,c_92]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_8970,plain,
% 47.02/6.49      ( X0 = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2)))
% 47.02/6.49      | X0 != k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
% 47.02/6.49      inference(resolution,[status(thm)],[c_2415,c_508]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_10,negated_conjecture,
% 47.02/6.49      ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
% 47.02/6.49      inference(cnf_transformation,[],[f44]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_94966,plain,
% 47.02/6.49      ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 47.02/6.49      inference(resolution,[status(thm)],[c_8970,c_10]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_94,plain,
% 47.02/6.49      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 47.02/6.49      theory(equality) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_897,plain,
% 47.02/6.49      ( X0 != X1 | X2 != X3 | k4_xboole_0(X1,X3) = k4_xboole_0(X0,X2) ),
% 47.02/6.49      inference(resolution,[status(thm)],[c_94,c_508]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_96913,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 | sK0 != sK0 ),
% 47.02/6.49      inference(resolution,[status(thm)],[c_94966,c_897]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(c_96914,plain,
% 47.02/6.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 ),
% 47.02/6.49      inference(equality_resolution_simp,[status(thm)],[c_96913]) ).
% 47.02/6.49  
% 47.02/6.49  cnf(contradiction,plain,
% 47.02/6.49      ( $false ),
% 47.02/6.49      inference(minisat,[status(thm)],[c_162011,c_96914]) ).
% 47.02/6.49  
% 47.02/6.49  
% 47.02/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.02/6.49  
% 47.02/6.49  ------                               Statistics
% 47.02/6.49  
% 47.02/6.49  ------ Selected
% 47.02/6.49  
% 47.02/6.49  total_time:                             5.874
% 47.02/6.49  
%------------------------------------------------------------------------------
