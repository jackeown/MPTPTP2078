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
% DateTime   : Thu Dec  3 11:22:50 EST 2020

% Result     : Theorem 51.20s
% Output     : CNFRefutation 51.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 289 expanded)
%              Number of clauses        :   56 ( 142 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :   95 ( 315 expanded)
%              Number of equality atoms :   79 ( 277 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f31,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_332,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_545,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_332])).

cnf(c_996,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_545,c_7])).

cnf(c_997,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_996,c_3])).

cnf(c_4,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1047,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X0,X0))) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_997,c_4])).

cnf(c_530,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_535,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_536,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_530,c_535])).

cnf(c_1049,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1047,c_3,c_536])).

cnf(c_1141,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1049,c_3])).

cnf(c_2215,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1141])).

cnf(c_3189,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_7,c_2215])).

cnf(c_1130,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_1049])).

cnf(c_1249,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1130,c_3])).

cnf(c_2351,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1249])).

cnf(c_2379,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2351,c_7])).

cnf(c_3233,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3189,c_2379])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_151,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_152,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1057,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_151,c_152])).

cnf(c_336,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_337,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_336,c_7])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_150,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_421,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_151,c_150])).

cnf(c_974,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_337,c_421])).

cnf(c_1959,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_974])).

cnf(c_2471,plain,
    ( k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X0),X0) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1959,c_152])).

cnf(c_2472,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2471,c_1130])).

cnf(c_2477,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_2472])).

cnf(c_2690,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1057,c_2477])).

cnf(c_2793,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_2690,c_4])).

cnf(c_218708,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3233,c_2793])).

cnf(c_1059,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_421,c_152])).

cnf(c_219719,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_218708,c_1059])).

cnf(c_224106,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_219719,c_8])).

cnf(c_221,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_546,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_332])).

cnf(c_554,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_546,c_332])).

cnf(c_1733,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_554])).

cnf(c_1749,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1733,c_9])).

cnf(c_55342,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_221,c_1749])).

cnf(c_55614,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_55342,c_9,c_221])).

cnf(c_224437,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_224106,c_55614])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_226821,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_224437,c_11])).

cnf(c_226823,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_226821])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.20/6.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.20/6.99  
% 51.20/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.20/6.99  
% 51.20/6.99  ------  iProver source info
% 51.20/6.99  
% 51.20/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.20/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.20/6.99  git: non_committed_changes: false
% 51.20/6.99  git: last_make_outside_of_git: false
% 51.20/6.99  
% 51.20/6.99  ------ 
% 51.20/6.99  
% 51.20/6.99  ------ Input Options
% 51.20/6.99  
% 51.20/6.99  --out_options                           all
% 51.20/6.99  --tptp_safe_out                         true
% 51.20/6.99  --problem_path                          ""
% 51.20/6.99  --include_path                          ""
% 51.20/6.99  --clausifier                            res/vclausify_rel
% 51.20/6.99  --clausifier_options                    ""
% 51.20/6.99  --stdin                                 false
% 51.20/6.99  --stats_out                             all
% 51.20/6.99  
% 51.20/6.99  ------ General Options
% 51.20/6.99  
% 51.20/6.99  --fof                                   false
% 51.20/6.99  --time_out_real                         305.
% 51.20/6.99  --time_out_virtual                      -1.
% 51.20/6.99  --symbol_type_check                     false
% 51.20/6.99  --clausify_out                          false
% 51.20/6.99  --sig_cnt_out                           false
% 51.20/6.99  --trig_cnt_out                          false
% 51.20/6.99  --trig_cnt_out_tolerance                1.
% 51.20/6.99  --trig_cnt_out_sk_spl                   false
% 51.20/6.99  --abstr_cl_out                          false
% 51.20/6.99  
% 51.20/6.99  ------ Global Options
% 51.20/6.99  
% 51.20/6.99  --schedule                              default
% 51.20/6.99  --add_important_lit                     false
% 51.20/6.99  --prop_solver_per_cl                    1000
% 51.20/6.99  --min_unsat_core                        false
% 51.20/6.99  --soft_assumptions                      false
% 51.20/6.99  --soft_lemma_size                       3
% 51.20/6.99  --prop_impl_unit_size                   0
% 51.20/6.99  --prop_impl_unit                        []
% 51.20/6.99  --share_sel_clauses                     true
% 51.20/6.99  --reset_solvers                         false
% 51.20/6.99  --bc_imp_inh                            [conj_cone]
% 51.20/6.99  --conj_cone_tolerance                   3.
% 51.20/6.99  --extra_neg_conj                        none
% 51.20/6.99  --large_theory_mode                     true
% 51.20/6.99  --prolific_symb_bound                   200
% 51.20/6.99  --lt_threshold                          2000
% 51.20/6.99  --clause_weak_htbl                      true
% 51.20/6.99  --gc_record_bc_elim                     false
% 51.20/6.99  
% 51.20/6.99  ------ Preprocessing Options
% 51.20/6.99  
% 51.20/6.99  --preprocessing_flag                    true
% 51.20/6.99  --time_out_prep_mult                    0.1
% 51.20/6.99  --splitting_mode                        input
% 51.20/6.99  --splitting_grd                         true
% 51.20/6.99  --splitting_cvd                         false
% 51.20/6.99  --splitting_cvd_svl                     false
% 51.20/6.99  --splitting_nvd                         32
% 51.20/6.99  --sub_typing                            true
% 51.20/6.99  --prep_gs_sim                           true
% 51.20/6.99  --prep_unflatten                        true
% 51.20/6.99  --prep_res_sim                          true
% 51.20/6.99  --prep_upred                            true
% 51.20/6.99  --prep_sem_filter                       exhaustive
% 51.20/6.99  --prep_sem_filter_out                   false
% 51.20/6.99  --pred_elim                             true
% 51.20/6.99  --res_sim_input                         true
% 51.20/6.99  --eq_ax_congr_red                       true
% 51.20/6.99  --pure_diseq_elim                       true
% 51.20/6.99  --brand_transform                       false
% 51.20/6.99  --non_eq_to_eq                          false
% 51.20/6.99  --prep_def_merge                        true
% 51.20/6.99  --prep_def_merge_prop_impl              false
% 51.20/6.99  --prep_def_merge_mbd                    true
% 51.20/6.99  --prep_def_merge_tr_red                 false
% 51.20/6.99  --prep_def_merge_tr_cl                  false
% 51.20/6.99  --smt_preprocessing                     true
% 51.20/6.99  --smt_ac_axioms                         fast
% 51.20/6.99  --preprocessed_out                      false
% 51.20/6.99  --preprocessed_stats                    false
% 51.20/6.99  
% 51.20/6.99  ------ Abstraction refinement Options
% 51.20/6.99  
% 51.20/6.99  --abstr_ref                             []
% 51.20/6.99  --abstr_ref_prep                        false
% 51.20/6.99  --abstr_ref_until_sat                   false
% 51.20/6.99  --abstr_ref_sig_restrict                funpre
% 51.20/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.20/6.99  --abstr_ref_under                       []
% 51.20/6.99  
% 51.20/6.99  ------ SAT Options
% 51.20/6.99  
% 51.20/6.99  --sat_mode                              false
% 51.20/6.99  --sat_fm_restart_options                ""
% 51.20/6.99  --sat_gr_def                            false
% 51.20/6.99  --sat_epr_types                         true
% 51.20/6.99  --sat_non_cyclic_types                  false
% 51.20/6.99  --sat_finite_models                     false
% 51.20/6.99  --sat_fm_lemmas                         false
% 51.20/6.99  --sat_fm_prep                           false
% 51.20/6.99  --sat_fm_uc_incr                        true
% 51.20/6.99  --sat_out_model                         small
% 51.20/6.99  --sat_out_clauses                       false
% 51.20/6.99  
% 51.20/6.99  ------ QBF Options
% 51.20/6.99  
% 51.20/6.99  --qbf_mode                              false
% 51.20/6.99  --qbf_elim_univ                         false
% 51.20/6.99  --qbf_dom_inst                          none
% 51.20/6.99  --qbf_dom_pre_inst                      false
% 51.20/6.99  --qbf_sk_in                             false
% 51.20/6.99  --qbf_pred_elim                         true
% 51.20/6.99  --qbf_split                             512
% 51.20/6.99  
% 51.20/6.99  ------ BMC1 Options
% 51.20/6.99  
% 51.20/6.99  --bmc1_incremental                      false
% 51.20/6.99  --bmc1_axioms                           reachable_all
% 51.20/6.99  --bmc1_min_bound                        0
% 51.20/6.99  --bmc1_max_bound                        -1
% 51.20/6.99  --bmc1_max_bound_default                -1
% 51.20/6.99  --bmc1_symbol_reachability              true
% 51.20/6.99  --bmc1_property_lemmas                  false
% 51.20/6.99  --bmc1_k_induction                      false
% 51.20/6.99  --bmc1_non_equiv_states                 false
% 51.20/6.99  --bmc1_deadlock                         false
% 51.20/6.99  --bmc1_ucm                              false
% 51.20/6.99  --bmc1_add_unsat_core                   none
% 51.20/6.99  --bmc1_unsat_core_children              false
% 51.20/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.20/6.99  --bmc1_out_stat                         full
% 51.20/6.99  --bmc1_ground_init                      false
% 51.20/6.99  --bmc1_pre_inst_next_state              false
% 51.20/6.99  --bmc1_pre_inst_state                   false
% 51.20/6.99  --bmc1_pre_inst_reach_state             false
% 51.20/6.99  --bmc1_out_unsat_core                   false
% 51.20/6.99  --bmc1_aig_witness_out                  false
% 51.20/6.99  --bmc1_verbose                          false
% 51.20/6.99  --bmc1_dump_clauses_tptp                false
% 51.20/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.20/6.99  --bmc1_dump_file                        -
% 51.20/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.20/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.20/6.99  --bmc1_ucm_extend_mode                  1
% 51.20/6.99  --bmc1_ucm_init_mode                    2
% 51.20/6.99  --bmc1_ucm_cone_mode                    none
% 51.20/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.20/6.99  --bmc1_ucm_relax_model                  4
% 51.20/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.20/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.20/6.99  --bmc1_ucm_layered_model                none
% 51.20/6.99  --bmc1_ucm_max_lemma_size               10
% 51.20/6.99  
% 51.20/6.99  ------ AIG Options
% 51.20/6.99  
% 51.20/6.99  --aig_mode                              false
% 51.20/6.99  
% 51.20/6.99  ------ Instantiation Options
% 51.20/6.99  
% 51.20/6.99  --instantiation_flag                    true
% 51.20/6.99  --inst_sos_flag                         true
% 51.20/6.99  --inst_sos_phase                        true
% 51.20/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.20/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.20/6.99  --inst_lit_sel_side                     num_symb
% 51.20/6.99  --inst_solver_per_active                1400
% 51.20/6.99  --inst_solver_calls_frac                1.
% 51.20/6.99  --inst_passive_queue_type               priority_queues
% 51.20/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.20/6.99  --inst_passive_queues_freq              [25;2]
% 51.20/6.99  --inst_dismatching                      true
% 51.20/6.99  --inst_eager_unprocessed_to_passive     true
% 51.20/6.99  --inst_prop_sim_given                   true
% 51.20/6.99  --inst_prop_sim_new                     false
% 51.20/6.99  --inst_subs_new                         false
% 51.20/6.99  --inst_eq_res_simp                      false
% 51.20/6.99  --inst_subs_given                       false
% 51.20/6.99  --inst_orphan_elimination               true
% 51.20/6.99  --inst_learning_loop_flag               true
% 51.20/6.99  --inst_learning_start                   3000
% 51.20/6.99  --inst_learning_factor                  2
% 51.20/6.99  --inst_start_prop_sim_after_learn       3
% 51.20/6.99  --inst_sel_renew                        solver
% 51.20/6.99  --inst_lit_activity_flag                true
% 51.20/6.99  --inst_restr_to_given                   false
% 51.20/6.99  --inst_activity_threshold               500
% 51.20/6.99  --inst_out_proof                        true
% 51.20/6.99  
% 51.20/6.99  ------ Resolution Options
% 51.20/6.99  
% 51.20/6.99  --resolution_flag                       true
% 51.20/6.99  --res_lit_sel                           adaptive
% 51.20/6.99  --res_lit_sel_side                      none
% 51.20/6.99  --res_ordering                          kbo
% 51.20/6.99  --res_to_prop_solver                    active
% 51.20/6.99  --res_prop_simpl_new                    false
% 51.20/6.99  --res_prop_simpl_given                  true
% 51.20/6.99  --res_passive_queue_type                priority_queues
% 51.20/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.20/6.99  --res_passive_queues_freq               [15;5]
% 51.20/6.99  --res_forward_subs                      full
% 51.20/6.99  --res_backward_subs                     full
% 51.20/6.99  --res_forward_subs_resolution           true
% 51.20/6.99  --res_backward_subs_resolution          true
% 51.20/6.99  --res_orphan_elimination                true
% 51.20/6.99  --res_time_limit                        2.
% 51.20/6.99  --res_out_proof                         true
% 51.20/6.99  
% 51.20/6.99  ------ Superposition Options
% 51.20/6.99  
% 51.20/6.99  --superposition_flag                    true
% 51.20/6.99  --sup_passive_queue_type                priority_queues
% 51.20/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.20/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.20/6.99  --demod_completeness_check              fast
% 51.20/6.99  --demod_use_ground                      true
% 51.20/6.99  --sup_to_prop_solver                    passive
% 51.20/6.99  --sup_prop_simpl_new                    true
% 51.20/6.99  --sup_prop_simpl_given                  true
% 51.20/6.99  --sup_fun_splitting                     true
% 51.20/6.99  --sup_smt_interval                      50000
% 51.20/6.99  
% 51.20/6.99  ------ Superposition Simplification Setup
% 51.20/6.99  
% 51.20/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.20/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.20/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.20/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.20/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.20/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.20/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.20/6.99  --sup_immed_triv                        [TrivRules]
% 51.20/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.20/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.20/6.99  --sup_immed_bw_main                     []
% 51.20/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.20/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.20/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.20/6.99  --sup_input_bw                          []
% 51.20/6.99  
% 51.20/6.99  ------ Combination Options
% 51.20/6.99  
% 51.20/6.99  --comb_res_mult                         3
% 51.20/6.99  --comb_sup_mult                         2
% 51.20/6.99  --comb_inst_mult                        10
% 51.20/6.99  
% 51.20/6.99  ------ Debug Options
% 51.20/6.99  
% 51.20/6.99  --dbg_backtrace                         false
% 51.20/6.99  --dbg_dump_prop_clauses                 false
% 51.20/6.99  --dbg_dump_prop_clauses_file            -
% 51.20/6.99  --dbg_out_stat                          false
% 51.20/6.99  ------ Parsing...
% 51.20/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.20/6.99  
% 51.20/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.20/6.99  
% 51.20/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.20/6.99  
% 51.20/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.20/6.99  ------ Proving...
% 51.20/6.99  ------ Problem Properties 
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  clauses                                 12
% 51.20/6.99  conjectures                             1
% 51.20/6.99  EPR                                     0
% 51.20/6.99  Horn                                    12
% 51.20/6.99  unary                                   9
% 51.20/6.99  binary                                  3
% 51.20/6.99  lits                                    15
% 51.20/6.99  lits eq                                 10
% 51.20/6.99  fd_pure                                 0
% 51.20/6.99  fd_pseudo                               0
% 51.20/6.99  fd_cond                                 0
% 51.20/6.99  fd_pseudo_cond                          0
% 51.20/6.99  AC symbols                              0
% 51.20/6.99  
% 51.20/6.99  ------ Schedule dynamic 5 is on 
% 51.20/6.99  
% 51.20/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  ------ 
% 51.20/6.99  Current options:
% 51.20/6.99  ------ 
% 51.20/6.99  
% 51.20/6.99  ------ Input Options
% 51.20/6.99  
% 51.20/6.99  --out_options                           all
% 51.20/6.99  --tptp_safe_out                         true
% 51.20/6.99  --problem_path                          ""
% 51.20/6.99  --include_path                          ""
% 51.20/6.99  --clausifier                            res/vclausify_rel
% 51.20/6.99  --clausifier_options                    ""
% 51.20/6.99  --stdin                                 false
% 51.20/6.99  --stats_out                             all
% 51.20/6.99  
% 51.20/6.99  ------ General Options
% 51.20/6.99  
% 51.20/6.99  --fof                                   false
% 51.20/6.99  --time_out_real                         305.
% 51.20/6.99  --time_out_virtual                      -1.
% 51.20/6.99  --symbol_type_check                     false
% 51.20/6.99  --clausify_out                          false
% 51.20/6.99  --sig_cnt_out                           false
% 51.20/6.99  --trig_cnt_out                          false
% 51.20/6.99  --trig_cnt_out_tolerance                1.
% 51.20/6.99  --trig_cnt_out_sk_spl                   false
% 51.20/6.99  --abstr_cl_out                          false
% 51.20/6.99  
% 51.20/6.99  ------ Global Options
% 51.20/6.99  
% 51.20/6.99  --schedule                              default
% 51.20/6.99  --add_important_lit                     false
% 51.20/6.99  --prop_solver_per_cl                    1000
% 51.20/6.99  --min_unsat_core                        false
% 51.20/6.99  --soft_assumptions                      false
% 51.20/6.99  --soft_lemma_size                       3
% 51.20/6.99  --prop_impl_unit_size                   0
% 51.20/6.99  --prop_impl_unit                        []
% 51.20/6.99  --share_sel_clauses                     true
% 51.20/6.99  --reset_solvers                         false
% 51.20/6.99  --bc_imp_inh                            [conj_cone]
% 51.20/6.99  --conj_cone_tolerance                   3.
% 51.20/6.99  --extra_neg_conj                        none
% 51.20/6.99  --large_theory_mode                     true
% 51.20/6.99  --prolific_symb_bound                   200
% 51.20/6.99  --lt_threshold                          2000
% 51.20/6.99  --clause_weak_htbl                      true
% 51.20/6.99  --gc_record_bc_elim                     false
% 51.20/6.99  
% 51.20/6.99  ------ Preprocessing Options
% 51.20/6.99  
% 51.20/6.99  --preprocessing_flag                    true
% 51.20/6.99  --time_out_prep_mult                    0.1
% 51.20/6.99  --splitting_mode                        input
% 51.20/6.99  --splitting_grd                         true
% 51.20/6.99  --splitting_cvd                         false
% 51.20/6.99  --splitting_cvd_svl                     false
% 51.20/6.99  --splitting_nvd                         32
% 51.20/6.99  --sub_typing                            true
% 51.20/6.99  --prep_gs_sim                           true
% 51.20/6.99  --prep_unflatten                        true
% 51.20/6.99  --prep_res_sim                          true
% 51.20/6.99  --prep_upred                            true
% 51.20/6.99  --prep_sem_filter                       exhaustive
% 51.20/6.99  --prep_sem_filter_out                   false
% 51.20/6.99  --pred_elim                             true
% 51.20/6.99  --res_sim_input                         true
% 51.20/6.99  --eq_ax_congr_red                       true
% 51.20/6.99  --pure_diseq_elim                       true
% 51.20/6.99  --brand_transform                       false
% 51.20/6.99  --non_eq_to_eq                          false
% 51.20/6.99  --prep_def_merge                        true
% 51.20/6.99  --prep_def_merge_prop_impl              false
% 51.20/6.99  --prep_def_merge_mbd                    true
% 51.20/6.99  --prep_def_merge_tr_red                 false
% 51.20/6.99  --prep_def_merge_tr_cl                  false
% 51.20/6.99  --smt_preprocessing                     true
% 51.20/6.99  --smt_ac_axioms                         fast
% 51.20/6.99  --preprocessed_out                      false
% 51.20/6.99  --preprocessed_stats                    false
% 51.20/6.99  
% 51.20/6.99  ------ Abstraction refinement Options
% 51.20/6.99  
% 51.20/6.99  --abstr_ref                             []
% 51.20/6.99  --abstr_ref_prep                        false
% 51.20/6.99  --abstr_ref_until_sat                   false
% 51.20/6.99  --abstr_ref_sig_restrict                funpre
% 51.20/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.20/6.99  --abstr_ref_under                       []
% 51.20/6.99  
% 51.20/6.99  ------ SAT Options
% 51.20/6.99  
% 51.20/6.99  --sat_mode                              false
% 51.20/6.99  --sat_fm_restart_options                ""
% 51.20/6.99  --sat_gr_def                            false
% 51.20/6.99  --sat_epr_types                         true
% 51.20/6.99  --sat_non_cyclic_types                  false
% 51.20/6.99  --sat_finite_models                     false
% 51.20/6.99  --sat_fm_lemmas                         false
% 51.20/6.99  --sat_fm_prep                           false
% 51.20/6.99  --sat_fm_uc_incr                        true
% 51.20/6.99  --sat_out_model                         small
% 51.20/6.99  --sat_out_clauses                       false
% 51.20/6.99  
% 51.20/6.99  ------ QBF Options
% 51.20/6.99  
% 51.20/6.99  --qbf_mode                              false
% 51.20/6.99  --qbf_elim_univ                         false
% 51.20/6.99  --qbf_dom_inst                          none
% 51.20/6.99  --qbf_dom_pre_inst                      false
% 51.20/6.99  --qbf_sk_in                             false
% 51.20/6.99  --qbf_pred_elim                         true
% 51.20/6.99  --qbf_split                             512
% 51.20/6.99  
% 51.20/6.99  ------ BMC1 Options
% 51.20/6.99  
% 51.20/6.99  --bmc1_incremental                      false
% 51.20/6.99  --bmc1_axioms                           reachable_all
% 51.20/6.99  --bmc1_min_bound                        0
% 51.20/6.99  --bmc1_max_bound                        -1
% 51.20/6.99  --bmc1_max_bound_default                -1
% 51.20/6.99  --bmc1_symbol_reachability              true
% 51.20/6.99  --bmc1_property_lemmas                  false
% 51.20/6.99  --bmc1_k_induction                      false
% 51.20/6.99  --bmc1_non_equiv_states                 false
% 51.20/6.99  --bmc1_deadlock                         false
% 51.20/6.99  --bmc1_ucm                              false
% 51.20/6.99  --bmc1_add_unsat_core                   none
% 51.20/6.99  --bmc1_unsat_core_children              false
% 51.20/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.20/6.99  --bmc1_out_stat                         full
% 51.20/6.99  --bmc1_ground_init                      false
% 51.20/6.99  --bmc1_pre_inst_next_state              false
% 51.20/6.99  --bmc1_pre_inst_state                   false
% 51.20/6.99  --bmc1_pre_inst_reach_state             false
% 51.20/6.99  --bmc1_out_unsat_core                   false
% 51.20/6.99  --bmc1_aig_witness_out                  false
% 51.20/6.99  --bmc1_verbose                          false
% 51.20/6.99  --bmc1_dump_clauses_tptp                false
% 51.20/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.20/6.99  --bmc1_dump_file                        -
% 51.20/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.20/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.20/6.99  --bmc1_ucm_extend_mode                  1
% 51.20/6.99  --bmc1_ucm_init_mode                    2
% 51.20/6.99  --bmc1_ucm_cone_mode                    none
% 51.20/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.20/6.99  --bmc1_ucm_relax_model                  4
% 51.20/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.20/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.20/6.99  --bmc1_ucm_layered_model                none
% 51.20/6.99  --bmc1_ucm_max_lemma_size               10
% 51.20/6.99  
% 51.20/6.99  ------ AIG Options
% 51.20/6.99  
% 51.20/6.99  --aig_mode                              false
% 51.20/6.99  
% 51.20/6.99  ------ Instantiation Options
% 51.20/6.99  
% 51.20/6.99  --instantiation_flag                    true
% 51.20/6.99  --inst_sos_flag                         true
% 51.20/6.99  --inst_sos_phase                        true
% 51.20/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.20/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.20/6.99  --inst_lit_sel_side                     none
% 51.20/6.99  --inst_solver_per_active                1400
% 51.20/6.99  --inst_solver_calls_frac                1.
% 51.20/6.99  --inst_passive_queue_type               priority_queues
% 51.20/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.20/6.99  --inst_passive_queues_freq              [25;2]
% 51.20/6.99  --inst_dismatching                      true
% 51.20/6.99  --inst_eager_unprocessed_to_passive     true
% 51.20/6.99  --inst_prop_sim_given                   true
% 51.20/6.99  --inst_prop_sim_new                     false
% 51.20/6.99  --inst_subs_new                         false
% 51.20/6.99  --inst_eq_res_simp                      false
% 51.20/6.99  --inst_subs_given                       false
% 51.20/6.99  --inst_orphan_elimination               true
% 51.20/6.99  --inst_learning_loop_flag               true
% 51.20/6.99  --inst_learning_start                   3000
% 51.20/6.99  --inst_learning_factor                  2
% 51.20/6.99  --inst_start_prop_sim_after_learn       3
% 51.20/6.99  --inst_sel_renew                        solver
% 51.20/6.99  --inst_lit_activity_flag                true
% 51.20/6.99  --inst_restr_to_given                   false
% 51.20/6.99  --inst_activity_threshold               500
% 51.20/6.99  --inst_out_proof                        true
% 51.20/6.99  
% 51.20/6.99  ------ Resolution Options
% 51.20/6.99  
% 51.20/6.99  --resolution_flag                       false
% 51.20/6.99  --res_lit_sel                           adaptive
% 51.20/6.99  --res_lit_sel_side                      none
% 51.20/6.99  --res_ordering                          kbo
% 51.20/6.99  --res_to_prop_solver                    active
% 51.20/6.99  --res_prop_simpl_new                    false
% 51.20/6.99  --res_prop_simpl_given                  true
% 51.20/6.99  --res_passive_queue_type                priority_queues
% 51.20/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.20/6.99  --res_passive_queues_freq               [15;5]
% 51.20/6.99  --res_forward_subs                      full
% 51.20/6.99  --res_backward_subs                     full
% 51.20/6.99  --res_forward_subs_resolution           true
% 51.20/6.99  --res_backward_subs_resolution          true
% 51.20/6.99  --res_orphan_elimination                true
% 51.20/6.99  --res_time_limit                        2.
% 51.20/6.99  --res_out_proof                         true
% 51.20/6.99  
% 51.20/6.99  ------ Superposition Options
% 51.20/6.99  
% 51.20/6.99  --superposition_flag                    true
% 51.20/6.99  --sup_passive_queue_type                priority_queues
% 51.20/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.20/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.20/6.99  --demod_completeness_check              fast
% 51.20/6.99  --demod_use_ground                      true
% 51.20/6.99  --sup_to_prop_solver                    passive
% 51.20/6.99  --sup_prop_simpl_new                    true
% 51.20/6.99  --sup_prop_simpl_given                  true
% 51.20/6.99  --sup_fun_splitting                     true
% 51.20/6.99  --sup_smt_interval                      50000
% 51.20/6.99  
% 51.20/6.99  ------ Superposition Simplification Setup
% 51.20/6.99  
% 51.20/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.20/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.20/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.20/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.20/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.20/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.20/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.20/6.99  --sup_immed_triv                        [TrivRules]
% 51.20/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.20/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.20/6.99  --sup_immed_bw_main                     []
% 51.20/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.20/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.20/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.20/6.99  --sup_input_bw                          []
% 51.20/6.99  
% 51.20/6.99  ------ Combination Options
% 51.20/6.99  
% 51.20/6.99  --comb_res_mult                         3
% 51.20/6.99  --comb_sup_mult                         2
% 51.20/6.99  --comb_inst_mult                        10
% 51.20/6.99  
% 51.20/6.99  ------ Debug Options
% 51.20/6.99  
% 51.20/6.99  --dbg_backtrace                         false
% 51.20/6.99  --dbg_dump_prop_clauses                 false
% 51.20/6.99  --dbg_dump_prop_clauses_file            -
% 51.20/6.99  --dbg_out_stat                          false
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  ------ Proving...
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  % SZS status Theorem for theBenchmark.p
% 51.20/6.99  
% 51.20/6.99   Resolution empty clause
% 51.20/6.99  
% 51.20/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.20/6.99  
% 51.20/6.99  fof(f8,axiom,(
% 51.20/6.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f27,plain,(
% 51.20/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.20/6.99    inference(cnf_transformation,[],[f8])).
% 51.20/6.99  
% 51.20/6.99  fof(f1,axiom,(
% 51.20/6.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f20,plain,(
% 51.20/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f1])).
% 51.20/6.99  
% 51.20/6.99  fof(f4,axiom,(
% 51.20/6.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f23,plain,(
% 51.20/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 51.20/6.99    inference(cnf_transformation,[],[f4])).
% 51.20/6.99  
% 51.20/6.99  fof(f9,axiom,(
% 51.20/6.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f28,plain,(
% 51.20/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f9])).
% 51.20/6.99  
% 51.20/6.99  fof(f5,axiom,(
% 51.20/6.99    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f24,plain,(
% 51.20/6.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 51.20/6.99    inference(cnf_transformation,[],[f5])).
% 51.20/6.99  
% 51.20/6.99  fof(f2,axiom,(
% 51.20/6.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f21,plain,(
% 51.20/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f2])).
% 51.20/6.99  
% 51.20/6.99  fof(f7,axiom,(
% 51.20/6.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f26,plain,(
% 51.20/6.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f7])).
% 51.20/6.99  
% 51.20/6.99  fof(f6,axiom,(
% 51.20/6.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f15,plain,(
% 51.20/6.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.20/6.99    inference(ennf_transformation,[],[f6])).
% 51.20/6.99  
% 51.20/6.99  fof(f25,plain,(
% 51.20/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f15])).
% 51.20/6.99  
% 51.20/6.99  fof(f11,axiom,(
% 51.20/6.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f16,plain,(
% 51.20/6.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.20/6.99    inference(ennf_transformation,[],[f11])).
% 51.20/6.99  
% 51.20/6.99  fof(f30,plain,(
% 51.20/6.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f16])).
% 51.20/6.99  
% 51.20/6.99  fof(f10,axiom,(
% 51.20/6.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f29,plain,(
% 51.20/6.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 51.20/6.99    inference(cnf_transformation,[],[f10])).
% 51.20/6.99  
% 51.20/6.99  fof(f12,conjecture,(
% 51.20/6.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.20/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.20/6.99  
% 51.20/6.99  fof(f13,negated_conjecture,(
% 51.20/6.99    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.20/6.99    inference(negated_conjecture,[],[f12])).
% 51.20/6.99  
% 51.20/6.99  fof(f17,plain,(
% 51.20/6.99    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.20/6.99    inference(ennf_transformation,[],[f13])).
% 51.20/6.99  
% 51.20/6.99  fof(f18,plain,(
% 51.20/6.99    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 51.20/6.99    introduced(choice_axiom,[])).
% 51.20/6.99  
% 51.20/6.99  fof(f19,plain,(
% 51.20/6.99    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 51.20/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 51.20/6.99  
% 51.20/6.99  fof(f31,plain,(
% 51.20/6.99    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 51.20/6.99    inference(cnf_transformation,[],[f19])).
% 51.20/6.99  
% 51.20/6.99  cnf(c_7,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.20/6.99      inference(cnf_transformation,[],[f27]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_0,plain,
% 51.20/6.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 51.20/6.99      inference(cnf_transformation,[],[f20]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_3,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 51.20/6.99      inference(cnf_transformation,[],[f23]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_8,plain,
% 51.20/6.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.20/6.99      inference(cnf_transformation,[],[f28]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_332,plain,
% 51.20/6.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_545,plain,
% 51.20/6.99      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_3,c_332]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_996,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_545,c_7]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_997,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 51.20/6.99      inference(light_normalisation,[status(thm)],[c_996,c_3]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_4,plain,
% 51.20/6.99      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 51.20/6.99      inference(cnf_transformation,[],[f24]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1047,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X0,X0))) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_997,c_4]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_530,plain,
% 51.20/6.99      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1,plain,
% 51.20/6.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.20/6.99      inference(cnf_transformation,[],[f21]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_535,plain,
% 51.20/6.99      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_536,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_530,c_535]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1049,plain,
% 51.20/6.99      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_1047,c_3,c_536]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1141,plain,
% 51.20/6.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_1049,c_3]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2215,plain,
% 51.20/6.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_0,c_1141]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_3189,plain,
% 51.20/6.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_7,c_2215]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1130,plain,
% 51.20/6.99      ( k3_xboole_0(k2_xboole_0(X0,X1),X1) = X1 ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_0,c_1049]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1249,plain,
% 51.20/6.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_1130,c_3]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2351,plain,
% 51.20/6.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_7,c_1249]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2379,plain,
% 51.20/6.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.20/6.99      inference(light_normalisation,[status(thm)],[c_2351,c_7]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_3233,plain,
% 51.20/6.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 51.20/6.99      inference(light_normalisation,[status(thm)],[c_3189,c_2379]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_6,plain,
% 51.20/6.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.20/6.99      inference(cnf_transformation,[],[f26]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_151,plain,
% 51.20/6.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 51.20/6.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_5,plain,
% 51.20/6.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.20/6.99      inference(cnf_transformation,[],[f25]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_152,plain,
% 51.20/6.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.20/6.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1057,plain,
% 51.20/6.99      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_151,c_152]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_336,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_337,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.20/6.99      inference(light_normalisation,[status(thm)],[c_336,c_7]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_10,plain,
% 51.20/6.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 51.20/6.99      inference(cnf_transformation,[],[f30]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_150,plain,
% 51.20/6.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 51.20/6.99      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 51.20/6.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_421,plain,
% 51.20/6.99      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_151,c_150]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_974,plain,
% 51.20/6.99      ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_337,c_421]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1959,plain,
% 51.20/6.99      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X0),X0) = iProver_top ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_3,c_974]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2471,plain,
% 51.20/6.99      ( k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X0),X0) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_1959,c_152]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2472,plain,
% 51.20/6.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_2471,c_1130]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2477,plain,
% 51.20/6.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_1,c_2472]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2690,plain,
% 51.20/6.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_1057,c_2477]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_2793,plain,
% 51.20/6.99      ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_2690,c_4]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_218708,plain,
% 51.20/6.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_3233,c_2793]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1059,plain,
% 51.20/6.99      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_421,c_152]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_219719,plain,
% 51.20/6.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 51.20/6.99      inference(light_normalisation,[status(thm)],[c_218708,c_1059]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_224106,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_219719,c_8]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_221,plain,
% 51.20/6.99      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_9,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.20/6.99      inference(cnf_transformation,[],[f29]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_546,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_7,c_332]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_554,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_546,c_332]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1733,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_9,c_554]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_1749,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.20/6.99      inference(light_normalisation,[status(thm)],[c_1733,c_9]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_55342,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X1))) ),
% 51.20/6.99      inference(superposition,[status(thm)],[c_221,c_1749]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_55614,plain,
% 51.20/6.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,X1) ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_55342,c_9,c_221]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_224437,plain,
% 51.20/6.99      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_224106,c_55614]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_11,negated_conjecture,
% 51.20/6.99      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
% 51.20/6.99      inference(cnf_transformation,[],[f31]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_226821,plain,
% 51.20/6.99      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 51.20/6.99      inference(demodulation,[status(thm)],[c_224437,c_11]) ).
% 51.20/6.99  
% 51.20/6.99  cnf(c_226823,plain,
% 51.20/6.99      ( $false ),
% 51.20/6.99      inference(equality_resolution_simp,[status(thm)],[c_226821]) ).
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.20/6.99  
% 51.20/6.99  ------                               Statistics
% 51.20/6.99  
% 51.20/6.99  ------ General
% 51.20/6.99  
% 51.20/6.99  abstr_ref_over_cycles:                  0
% 51.20/6.99  abstr_ref_under_cycles:                 0
% 51.20/6.99  gc_basic_clause_elim:                   0
% 51.20/6.99  forced_gc_time:                         0
% 51.20/6.99  parsing_time:                           0.013
% 51.20/6.99  unif_index_cands_time:                  0.
% 51.20/6.99  unif_index_add_time:                    0.
% 51.20/6.99  orderings_time:                         0.
% 51.20/6.99  out_proof_time:                         0.008
% 51.20/6.99  total_time:                             6.198
% 51.20/6.99  num_of_symbols:                         38
% 51.20/6.99  num_of_terms:                           287551
% 51.20/6.99  
% 51.20/6.99  ------ Preprocessing
% 51.20/6.99  
% 51.20/6.99  num_of_splits:                          0
% 51.20/6.99  num_of_split_atoms:                     1
% 51.20/6.99  num_of_reused_defs:                     0
% 51.20/6.99  num_eq_ax_congr_red:                    2
% 51.20/6.99  num_of_sem_filtered_clauses:            1
% 51.20/6.99  num_of_subtypes:                        0
% 51.20/6.99  monotx_restored_types:                  0
% 51.20/6.99  sat_num_of_epr_types:                   0
% 51.20/6.99  sat_num_of_non_cyclic_types:            0
% 51.20/6.99  sat_guarded_non_collapsed_types:        0
% 51.20/6.99  num_pure_diseq_elim:                    0
% 51.20/6.99  simp_replaced_by:                       0
% 51.20/6.99  res_preprocessed:                       49
% 51.20/6.99  prep_upred:                             0
% 51.20/6.99  prep_unflattend:                        0
% 51.20/6.99  smt_new_axioms:                         0
% 51.20/6.99  pred_elim_cands:                        1
% 51.20/6.99  pred_elim:                              0
% 51.20/6.99  pred_elim_cl:                           0
% 51.20/6.99  pred_elim_cycles:                       1
% 51.20/6.99  merged_defs:                            0
% 51.20/6.99  merged_defs_ncl:                        0
% 51.20/6.99  bin_hyper_res:                          0
% 51.20/6.99  prep_cycles:                            3
% 51.20/6.99  pred_elim_time:                         0.
% 51.20/6.99  splitting_time:                         0.
% 51.20/6.99  sem_filter_time:                        0.
% 51.20/6.99  monotx_time:                            0.001
% 51.20/6.99  subtype_inf_time:                       0.
% 51.20/6.99  
% 51.20/6.99  ------ Problem properties
% 51.20/6.99  
% 51.20/6.99  clauses:                                12
% 51.20/6.99  conjectures:                            1
% 51.20/6.99  epr:                                    0
% 51.20/6.99  horn:                                   12
% 51.20/6.99  ground:                                 1
% 51.20/6.99  unary:                                  9
% 51.20/6.99  binary:                                 3
% 51.20/6.99  lits:                                   15
% 51.20/6.99  lits_eq:                                10
% 51.20/6.99  fd_pure:                                0
% 51.20/6.99  fd_pseudo:                              0
% 51.20/6.99  fd_cond:                                0
% 51.20/6.99  fd_pseudo_cond:                         0
% 51.20/6.99  ac_symbols:                             0
% 51.20/6.99  
% 51.20/6.99  ------ Propositional Solver
% 51.20/6.99  
% 51.20/6.99  prop_solver_calls:                      48
% 51.20/6.99  prop_fast_solver_calls:                 824
% 51.20/6.99  smt_solver_calls:                       0
% 51.20/6.99  smt_fast_solver_calls:                  0
% 51.20/6.99  prop_num_of_clauses:                    47548
% 51.20/6.99  prop_preprocess_simplified:             51395
% 51.20/6.99  prop_fo_subsumed:                       2
% 51.20/6.99  prop_solver_time:                       0.
% 51.20/6.99  smt_solver_time:                        0.
% 51.20/6.99  smt_fast_solver_time:                   0.
% 51.20/6.99  prop_fast_solver_time:                  0.
% 51.20/6.99  prop_unsat_core_time:                   0.
% 51.20/6.99  
% 51.20/6.99  ------ QBF
% 51.20/6.99  
% 51.20/6.99  qbf_q_res:                              0
% 51.20/6.99  qbf_num_tautologies:                    0
% 51.20/6.99  qbf_prep_cycles:                        0
% 51.20/6.99  
% 51.20/6.99  ------ BMC1
% 51.20/6.99  
% 51.20/6.99  bmc1_current_bound:                     -1
% 51.20/6.99  bmc1_last_solved_bound:                 -1
% 51.20/6.99  bmc1_unsat_core_size:                   -1
% 51.20/6.99  bmc1_unsat_core_parents_size:           -1
% 51.20/6.99  bmc1_merge_next_fun:                    0
% 51.20/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.20/6.99  
% 51.20/6.99  ------ Instantiation
% 51.20/6.99  
% 51.20/6.99  inst_num_of_clauses:                    8169
% 51.20/6.99  inst_num_in_passive:                    4954
% 51.20/6.99  inst_num_in_active:                     1913
% 51.20/6.99  inst_num_in_unprocessed:                1302
% 51.20/6.99  inst_num_of_loops:                      2550
% 51.20/6.99  inst_num_of_learning_restarts:          0
% 51.20/6.99  inst_num_moves_active_passive:          631
% 51.20/6.99  inst_lit_activity:                      0
% 51.20/6.99  inst_lit_activity_moves:                2
% 51.20/6.99  inst_num_tautologies:                   0
% 51.20/6.99  inst_num_prop_implied:                  0
% 51.20/6.99  inst_num_existing_simplified:           0
% 51.20/6.99  inst_num_eq_res_simplified:             0
% 51.20/6.99  inst_num_child_elim:                    0
% 51.20/6.99  inst_num_of_dismatching_blockings:      8960
% 51.20/6.99  inst_num_of_non_proper_insts:           9119
% 51.20/6.99  inst_num_of_duplicates:                 0
% 51.20/6.99  inst_inst_num_from_inst_to_res:         0
% 51.20/6.99  inst_dismatching_checking_time:         0.
% 51.20/6.99  
% 51.20/6.99  ------ Resolution
% 51.20/6.99  
% 51.20/6.99  res_num_of_clauses:                     0
% 51.20/6.99  res_num_in_passive:                     0
% 51.20/6.99  res_num_in_active:                      0
% 51.20/6.99  res_num_of_loops:                       52
% 51.20/6.99  res_forward_subset_subsumed:            3610
% 51.20/6.99  res_backward_subset_subsumed:           0
% 51.20/6.99  res_forward_subsumed:                   0
% 51.20/6.99  res_backward_subsumed:                  0
% 51.20/6.99  res_forward_subsumption_resolution:     0
% 51.20/6.99  res_backward_subsumption_resolution:    0
% 51.20/6.99  res_clause_to_clause_subsumption:       400254
% 51.20/6.99  res_orphan_elimination:                 0
% 51.20/6.99  res_tautology_del:                      1096
% 51.20/6.99  res_num_eq_res_simplified:              0
% 51.20/6.99  res_num_sel_changes:                    0
% 51.20/6.99  res_moves_from_active_to_pass:          0
% 51.20/6.99  
% 51.20/6.99  ------ Superposition
% 51.20/6.99  
% 51.20/6.99  sup_time_total:                         0.
% 51.20/6.99  sup_time_generating:                    0.
% 51.20/6.99  sup_time_sim_full:                      0.
% 51.20/6.99  sup_time_sim_immed:                     0.
% 51.20/6.99  
% 51.20/6.99  sup_num_of_clauses:                     15403
% 51.20/6.99  sup_num_in_active:                      461
% 51.20/6.99  sup_num_in_passive:                     14942
% 51.20/6.99  sup_num_of_loops:                       509
% 51.20/6.99  sup_fw_superposition:                   63184
% 51.20/6.99  sup_bw_superposition:                   46100
% 51.20/6.99  sup_immediate_simplified:               50865
% 51.20/6.99  sup_given_eliminated:                   4
% 51.20/6.99  comparisons_done:                       0
% 51.20/6.99  comparisons_avoided:                    0
% 51.20/6.99  
% 51.20/6.99  ------ Simplifications
% 51.20/6.99  
% 51.20/6.99  
% 51.20/6.99  sim_fw_subset_subsumed:                 92
% 51.20/6.99  sim_bw_subset_subsumed:                 66
% 51.20/6.99  sim_fw_subsumed:                        10627
% 51.20/6.99  sim_bw_subsumed:                        112
% 51.20/6.99  sim_fw_subsumption_res:                 0
% 51.20/6.99  sim_bw_subsumption_res:                 0
% 51.20/6.99  sim_tautology_del:                      130
% 51.20/6.99  sim_eq_tautology_del:                   9689
% 51.20/6.99  sim_eq_res_simp:                        0
% 51.20/6.99  sim_fw_demodulated:                     26519
% 51.20/6.99  sim_bw_demodulated:                     214
% 51.20/6.99  sim_light_normalised:                   22149
% 51.20/6.99  sim_joinable_taut:                      0
% 51.20/6.99  sim_joinable_simp:                      0
% 51.20/6.99  sim_ac_normalised:                      0
% 51.20/6.99  sim_smt_subsumption:                    0
% 51.20/6.99  
%------------------------------------------------------------------------------
