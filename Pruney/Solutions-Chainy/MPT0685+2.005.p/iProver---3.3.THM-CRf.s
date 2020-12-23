%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:27 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 283 expanded)
%              Number of clauses        :   38 ( 102 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  113 ( 402 expanded)
%              Number of equality atoms :   79 ( 254 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f39,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f21,f37,f37])).

fof(f34,plain,(
    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(definition_unfolding,[],[f34,f37])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_183,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_184,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X1,X0),X2) = k10_relat_1(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_187,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1213,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_184,c_187])).

cnf(c_3510,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
    inference(superposition,[status(thm)],[c_183,c_1213])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_185,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_601,plain,
    ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_183,c_185])).

cnf(c_3519,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3510,c_601])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_186,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1185,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_184,c_186])).

cnf(c_1871,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_184,c_1185])).

cnf(c_600,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_184,c_185])).

cnf(c_1881,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_1871,c_600])).

cnf(c_4,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1882,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1881,c_4])).

cnf(c_7,plain,
    ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_342,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_0,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_610,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_342,c_0])).

cnf(c_618,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_342,c_610])).

cnf(c_1370,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_618,c_600])).

cnf(c_1371,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1370,c_600])).

cnf(c_2200,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_1882,c_1371])).

cnf(c_2656,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1882,c_2200])).

cnf(c_8,negated_conjecture,
    ( k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_611,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),k6_relat_1(sK0))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_342,c_8])).

cnf(c_868,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_600,c_611])).

cnf(c_2204,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1882,c_868])).

cnf(c_2660,plain,
    ( k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2656,c_2204])).

cnf(c_3704,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_3519,c_2660])).

cnf(c_76,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_414,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3704,c_414])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:44:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.63/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/1.00  
% 2.63/1.00  ------  iProver source info
% 2.63/1.00  
% 2.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/1.00  git: non_committed_changes: false
% 2.63/1.00  git: last_make_outside_of_git: false
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     num_symb
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       true
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  ------ Parsing...
% 2.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/1.00  ------ Proving...
% 2.63/1.00  ------ Problem Properties 
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  clauses                                 10
% 2.63/1.00  conjectures                             2
% 2.63/1.00  EPR                                     1
% 2.63/1.00  Horn                                    10
% 2.63/1.00  unary                                   7
% 2.63/1.00  binary                                  1
% 2.63/1.00  lits                                    15
% 2.63/1.00  lits eq                                 8
% 2.63/1.00  fd_pure                                 0
% 2.63/1.00  fd_pseudo                               0
% 2.63/1.00  fd_cond                                 0
% 2.63/1.00  fd_pseudo_cond                          0
% 2.63/1.00  AC symbols                              0
% 2.63/1.00  
% 2.63/1.00  ------ Schedule dynamic 5 is on 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  Current options:
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     none
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       false
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ Proving...
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS status Theorem for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  fof(f12,conjecture,(
% 2.63/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f13,negated_conjecture,(
% 2.63/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.63/1.00    inference(negated_conjecture,[],[f12])).
% 2.63/1.00  
% 2.63/1.00  fof(f18,plain,(
% 2.63/1.00    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2))),
% 2.63/1.00    inference(ennf_transformation,[],[f13])).
% 2.63/1.00  
% 2.63/1.00  fof(f19,plain,(
% 2.63/1.00    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2)) => (k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) & v1_relat_1(sK2))),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f20,plain,(
% 2.63/1.00    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) & v1_relat_1(sK2)),
% 2.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 2.63/1.00  
% 2.63/1.00  fof(f33,plain,(
% 2.63/1.00    v1_relat_1(sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f20])).
% 2.63/1.00  
% 2.63/1.00  fof(f10,axiom,(
% 2.63/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f14,plain,(
% 2.63/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.63/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.63/1.00  
% 2.63/1.00  fof(f31,plain,(
% 2.63/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f14])).
% 2.63/1.00  
% 2.63/1.00  fof(f6,axiom,(
% 2.63/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f15,plain,(
% 2.63/1.00    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.63/1.00    inference(ennf_transformation,[],[f6])).
% 2.63/1.00  
% 2.63/1.00  fof(f26,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f15])).
% 2.63/1.00  
% 2.63/1.00  fof(f9,axiom,(
% 2.63/1.00    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f17,plain,(
% 2.63/1.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.63/1.01    inference(ennf_transformation,[],[f9])).
% 2.63/1.01  
% 2.63/1.01  fof(f30,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.63/1.01    inference(cnf_transformation,[],[f17])).
% 2.63/1.01  
% 2.63/1.01  fof(f7,axiom,(
% 2.63/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f16,plain,(
% 2.63/1.01    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.63/1.01    inference(ennf_transformation,[],[f7])).
% 2.63/1.01  
% 2.63/1.01  fof(f27,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.63/1.01    inference(cnf_transformation,[],[f16])).
% 2.63/1.01  
% 2.63/1.01  fof(f8,axiom,(
% 2.63/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f28,plain,(
% 2.63/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.63/1.01    inference(cnf_transformation,[],[f8])).
% 2.63/1.01  
% 2.63/1.01  fof(f11,axiom,(
% 2.63/1.01    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f32,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.63/1.01    inference(cnf_transformation,[],[f11])).
% 2.63/1.01  
% 2.63/1.01  fof(f5,axiom,(
% 2.63/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f25,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.63/1.01    inference(cnf_transformation,[],[f5])).
% 2.63/1.01  
% 2.63/1.01  fof(f2,axiom,(
% 2.63/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f22,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.63/1.01    inference(cnf_transformation,[],[f2])).
% 2.63/1.01  
% 2.63/1.01  fof(f3,axiom,(
% 2.63/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f23,plain,(
% 2.63/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.63/1.01    inference(cnf_transformation,[],[f3])).
% 2.63/1.01  
% 2.63/1.01  fof(f4,axiom,(
% 2.63/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f24,plain,(
% 2.63/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.63/1.01    inference(cnf_transformation,[],[f4])).
% 2.63/1.01  
% 2.63/1.01  fof(f35,plain,(
% 2.63/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.63/1.01    inference(definition_unfolding,[],[f23,f24])).
% 2.63/1.01  
% 2.63/1.01  fof(f36,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.63/1.01    inference(definition_unfolding,[],[f22,f35])).
% 2.63/1.01  
% 2.63/1.01  fof(f37,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.63/1.01    inference(definition_unfolding,[],[f25,f36])).
% 2.63/1.01  
% 2.63/1.01  fof(f39,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.63/1.01    inference(definition_unfolding,[],[f32,f37])).
% 2.63/1.01  
% 2.63/1.01  fof(f1,axiom,(
% 2.63/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.63/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.01  
% 2.63/1.01  fof(f21,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.63/1.01    inference(cnf_transformation,[],[f1])).
% 2.63/1.01  
% 2.63/1.01  fof(f38,plain,(
% 2.63/1.01    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 2.63/1.01    inference(definition_unfolding,[],[f21,f37,f37])).
% 2.63/1.01  
% 2.63/1.01  fof(f34,plain,(
% 2.63/1.01    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.63/1.01    inference(cnf_transformation,[],[f20])).
% 2.63/1.01  
% 2.63/1.01  fof(f40,plain,(
% 2.63/1.01    k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.63/1.01    inference(definition_unfolding,[],[f34,f37])).
% 2.63/1.01  
% 2.63/1.01  cnf(c_9,negated_conjecture,
% 2.63/1.01      ( v1_relat_1(sK2) ),
% 2.63/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_183,plain,
% 2.63/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_6,plain,
% 2.63/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_184,plain,
% 2.63/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1,plain,
% 2.63/1.01      ( ~ v1_relat_1(X0)
% 2.63/1.01      | ~ v1_relat_1(X1)
% 2.63/1.01      | k10_relat_1(k5_relat_1(X1,X0),X2) = k10_relat_1(X1,k10_relat_1(X0,X2)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f26]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_187,plain,
% 2.63/1.01      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 2.63/1.01      | v1_relat_1(X1) != iProver_top
% 2.63/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1213,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
% 2.63/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_184,c_187]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3510,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_183,c_1213]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_5,plain,
% 2.63/1.01      ( ~ v1_relat_1(X0)
% 2.63/1.01      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 2.63/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_185,plain,
% 2.63/1.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 2.63/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_601,plain,
% 2.63/1.01      ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_183,c_185]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3519,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_3510,c_601]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2,plain,
% 2.63/1.01      ( ~ v1_relat_1(X0)
% 2.63/1.01      | ~ v1_relat_1(X1)
% 2.63/1.01      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f27]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_186,plain,
% 2.63/1.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 2.63/1.01      | v1_relat_1(X1) != iProver_top
% 2.63/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1185,plain,
% 2.63/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 2.63/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_184,c_186]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1871,plain,
% 2.63/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_184,c_1185]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_600,plain,
% 2.63/1.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_184,c_185]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1881,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_1871,c_600]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_4,plain,
% 2.63/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.63/1.01      inference(cnf_transformation,[],[f28]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1882,plain,
% 2.63/1.01      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1881,c_4]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_7,plain,
% 2.63/1.01      ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_342,plain,
% 2.63/1.01      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_0,plain,
% 2.63/1.01      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_610,plain,
% 2.63/1.01      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_342,c_0]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_618,plain,
% 2.63/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_342,c_610]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1370,plain,
% 2.63/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_618,c_600]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1371,plain,
% 2.63/1.01      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1370,c_600]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2200,plain,
% 2.63/1.01      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1882,c_1371]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2656,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X1),X0) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1882,c_2200]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_8,negated_conjecture,
% 2.63/1.01      ( k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_611,plain,
% 2.63/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),k6_relat_1(sK0))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_342,c_8]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_868,plain,
% 2.63/1.01      ( k1_relat_1(k7_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_600,c_611]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2204,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1882,c_868]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2660,plain,
% 2.63/1.01      ( k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_2656,c_2204]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3704,plain,
% 2.63/1.01      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_3519,c_2660]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_76,plain,( X0 = X0 ),theory(equality) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_414,plain,
% 2.63/1.01      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_76]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(contradiction,plain,
% 2.63/1.01      ( $false ),
% 2.63/1.01      inference(minisat,[status(thm)],[c_3704,c_414]) ).
% 2.63/1.01  
% 2.63/1.01  
% 2.63/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.01  
% 2.63/1.01  ------                               Statistics
% 2.63/1.01  
% 2.63/1.01  ------ General
% 2.63/1.01  
% 2.63/1.01  abstr_ref_over_cycles:                  0
% 2.63/1.01  abstr_ref_under_cycles:                 0
% 2.63/1.01  gc_basic_clause_elim:                   0
% 2.63/1.01  forced_gc_time:                         0
% 2.63/1.01  parsing_time:                           0.014
% 2.63/1.01  unif_index_cands_time:                  0.
% 2.63/1.01  unif_index_add_time:                    0.
% 2.63/1.01  orderings_time:                         0.
% 2.63/1.01  out_proof_time:                         0.01
% 2.63/1.01  total_time:                             0.205
% 2.63/1.01  num_of_symbols:                         43
% 2.63/1.01  num_of_terms:                           5499
% 2.63/1.01  
% 2.63/1.01  ------ Preprocessing
% 2.63/1.01  
% 2.63/1.01  num_of_splits:                          0
% 2.63/1.01  num_of_split_atoms:                     0
% 2.63/1.01  num_of_reused_defs:                     0
% 2.63/1.01  num_eq_ax_congr_red:                    0
% 2.63/1.01  num_of_sem_filtered_clauses:            1
% 2.63/1.01  num_of_subtypes:                        0
% 2.63/1.01  monotx_restored_types:                  0
% 2.63/1.01  sat_num_of_epr_types:                   0
% 2.63/1.01  sat_num_of_non_cyclic_types:            0
% 2.63/1.01  sat_guarded_non_collapsed_types:        0
% 2.63/1.01  num_pure_diseq_elim:                    0
% 2.63/1.01  simp_replaced_by:                       0
% 2.63/1.01  res_preprocessed:                       53
% 2.63/1.01  prep_upred:                             0
% 2.63/1.01  prep_unflattend:                        0
% 2.63/1.01  smt_new_axioms:                         0
% 2.63/1.01  pred_elim_cands:                        1
% 2.63/1.01  pred_elim:                              0
% 2.63/1.01  pred_elim_cl:                           0
% 2.63/1.01  pred_elim_cycles:                       1
% 2.63/1.01  merged_defs:                            0
% 2.63/1.01  merged_defs_ncl:                        0
% 2.63/1.01  bin_hyper_res:                          0
% 2.63/1.01  prep_cycles:                            3
% 2.63/1.01  pred_elim_time:                         0.
% 2.63/1.01  splitting_time:                         0.
% 2.63/1.01  sem_filter_time:                        0.
% 2.63/1.01  monotx_time:                            0.001
% 2.63/1.01  subtype_inf_time:                       0.
% 2.63/1.01  
% 2.63/1.01  ------ Problem properties
% 2.63/1.01  
% 2.63/1.01  clauses:                                10
% 2.63/1.01  conjectures:                            2
% 2.63/1.01  epr:                                    1
% 2.63/1.01  horn:                                   10
% 2.63/1.01  ground:                                 2
% 2.63/1.01  unary:                                  7
% 2.63/1.01  binary:                                 1
% 2.63/1.01  lits:                                   15
% 2.63/1.01  lits_eq:                                8
% 2.63/1.01  fd_pure:                                0
% 2.63/1.01  fd_pseudo:                              0
% 2.63/1.01  fd_cond:                                0
% 2.63/1.01  fd_pseudo_cond:                         0
% 2.63/1.01  ac_symbols:                             0
% 2.63/1.01  
% 2.63/1.01  ------ Propositional Solver
% 2.63/1.01  
% 2.63/1.01  prop_solver_calls:                      24
% 2.63/1.01  prop_fast_solver_calls:                 292
% 2.63/1.01  smt_solver_calls:                       0
% 2.63/1.01  smt_fast_solver_calls:                  0
% 2.63/1.01  prop_num_of_clauses:                    2004
% 2.63/1.01  prop_preprocess_simplified:             3957
% 2.63/1.01  prop_fo_subsumed:                       0
% 2.63/1.01  prop_solver_time:                       0.
% 2.63/1.01  smt_solver_time:                        0.
% 2.63/1.01  smt_fast_solver_time:                   0.
% 2.63/1.01  prop_fast_solver_time:                  0.
% 2.63/1.01  prop_unsat_core_time:                   0.
% 2.63/1.01  
% 2.63/1.01  ------ QBF
% 2.63/1.01  
% 2.63/1.01  qbf_q_res:                              0
% 2.63/1.01  qbf_num_tautologies:                    0
% 2.63/1.01  qbf_prep_cycles:                        0
% 2.63/1.01  
% 2.63/1.01  ------ BMC1
% 2.63/1.01  
% 2.63/1.01  bmc1_current_bound:                     -1
% 2.63/1.01  bmc1_last_solved_bound:                 -1
% 2.63/1.01  bmc1_unsat_core_size:                   -1
% 2.63/1.01  bmc1_unsat_core_parents_size:           -1
% 2.63/1.01  bmc1_merge_next_fun:                    0
% 2.63/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.01  
% 2.63/1.01  ------ Instantiation
% 2.63/1.01  
% 2.63/1.01  inst_num_of_clauses:                    606
% 2.63/1.01  inst_num_in_passive:                    101
% 2.63/1.01  inst_num_in_active:                     317
% 2.63/1.01  inst_num_in_unprocessed:                189
% 2.63/1.01  inst_num_of_loops:                      320
% 2.63/1.01  inst_num_of_learning_restarts:          0
% 2.63/1.01  inst_num_moves_active_passive:          0
% 2.63/1.01  inst_lit_activity:                      0
% 2.63/1.01  inst_lit_activity_moves:                0
% 2.63/1.01  inst_num_tautologies:                   0
% 2.63/1.01  inst_num_prop_implied:                  0
% 2.63/1.01  inst_num_existing_simplified:           0
% 2.63/1.01  inst_num_eq_res_simplified:             0
% 2.63/1.01  inst_num_child_elim:                    0
% 2.63/1.01  inst_num_of_dismatching_blockings:      53
% 2.63/1.01  inst_num_of_non_proper_insts:           386
% 2.63/1.01  inst_num_of_duplicates:                 0
% 2.63/1.01  inst_inst_num_from_inst_to_res:         0
% 2.63/1.01  inst_dismatching_checking_time:         0.
% 2.63/1.01  
% 2.63/1.01  ------ Resolution
% 2.63/1.01  
% 2.63/1.01  res_num_of_clauses:                     0
% 2.63/1.01  res_num_in_passive:                     0
% 2.63/1.01  res_num_in_active:                      0
% 2.63/1.01  res_num_of_loops:                       56
% 2.63/1.01  res_forward_subset_subsumed:            43
% 2.63/1.01  res_backward_subset_subsumed:           6
% 2.63/1.01  res_forward_subsumed:                   0
% 2.63/1.01  res_backward_subsumed:                  0
% 2.63/1.01  res_forward_subsumption_resolution:     0
% 2.63/1.01  res_backward_subsumption_resolution:    0
% 2.63/1.01  res_clause_to_clause_subsumption:       208
% 2.63/1.01  res_orphan_elimination:                 0
% 2.63/1.01  res_tautology_del:                      39
% 2.63/1.01  res_num_eq_res_simplified:              0
% 2.63/1.01  res_num_sel_changes:                    0
% 2.63/1.01  res_moves_from_active_to_pass:          0
% 2.63/1.01  
% 2.63/1.01  ------ Superposition
% 2.63/1.01  
% 2.63/1.01  sup_time_total:                         0.
% 2.63/1.01  sup_time_generating:                    0.
% 2.63/1.01  sup_time_sim_full:                      0.
% 2.63/1.01  sup_time_sim_immed:                     0.
% 2.63/1.01  
% 2.63/1.01  sup_num_of_clauses:                     100
% 2.63/1.01  sup_num_in_active:                      41
% 2.63/1.01  sup_num_in_passive:                     59
% 2.63/1.01  sup_num_of_loops:                       62
% 2.63/1.01  sup_fw_superposition:                   85
% 2.63/1.01  sup_bw_superposition:                   108
% 2.63/1.01  sup_immediate_simplified:               80
% 2.63/1.01  sup_given_eliminated:                   2
% 2.63/1.01  comparisons_done:                       0
% 2.63/1.01  comparisons_avoided:                    0
% 2.63/1.01  
% 2.63/1.01  ------ Simplifications
% 2.63/1.01  
% 2.63/1.01  
% 2.63/1.01  sim_fw_subset_subsumed:                 0
% 2.63/1.01  sim_bw_subset_subsumed:                 0
% 2.63/1.01  sim_fw_subsumed:                        19
% 2.63/1.01  sim_bw_subsumed:                        0
% 2.63/1.01  sim_fw_subsumption_res:                 0
% 2.63/1.01  sim_bw_subsumption_res:                 0
% 2.63/1.01  sim_tautology_del:                      0
% 2.63/1.01  sim_eq_tautology_del:                   7
% 2.63/1.01  sim_eq_res_simp:                        0
% 2.63/1.01  sim_fw_demodulated:                     20
% 2.63/1.01  sim_bw_demodulated:                     26
% 2.63/1.01  sim_light_normalised:                   60
% 2.63/1.01  sim_joinable_taut:                      0
% 2.63/1.01  sim_joinable_simp:                      0
% 2.63/1.01  sim_ac_normalised:                      0
% 2.63/1.01  sim_smt_subsumption:                    0
% 2.63/1.01  
%------------------------------------------------------------------------------
