%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:49 EST 2020

% Result     : Theorem 43.58s
% Output     : CNFRefutation 43.58s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 312 expanded)
%              Number of clauses        :   54 ( 156 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :   97 ( 349 expanded)
%              Number of equality atoms :   84 ( 303 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).

fof(f34,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_306,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_439,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_306])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_307,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_529,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_439,c_307])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_780,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_529,c_5])).

cnf(c_6,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_855,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_780,c_6])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_436,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_11,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_634,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_10])).

cnf(c_635,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_634,c_10])).

cnf(c_851,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_635,c_6])).

cnf(c_856,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_855,c_436,c_851])).

cnf(c_1061,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_856,c_5])).

cnf(c_2301,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1061])).

cnf(c_3349,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_9,c_2301])).

cnf(c_629,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_310,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1605,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_306,c_310])).

cnf(c_1961,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1605,c_9])).

cnf(c_1964,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1961,c_635])).

cnf(c_2157,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_629,c_1964])).

cnf(c_3394,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3349,c_2157])).

cnf(c_3358,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1964,c_2301])).

cnf(c_3391,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3358,c_1964])).

cnf(c_3484,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3391,c_6])).

cnf(c_200968,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3394,c_3484])).

cnf(c_854,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_780,c_6])).

cnf(c_848,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_635,c_6])).

cnf(c_857,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_854,c_5,c_848])).

cnf(c_1118,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_857])).

cnf(c_202049,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_200968,c_1118])).

cnf(c_204653,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_202049,c_11])).

cnf(c_12,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1288,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_9,c_629])).

cnf(c_1298,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1288,c_629])).

cnf(c_2896,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_12,c_1298])).

cnf(c_2924,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2896,c_12])).

cnf(c_63510,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_436,c_2924])).

cnf(c_63819,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_63510,c_12,c_436])).

cnf(c_204992,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_204653,c_63819])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_208361,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_204992,c_13])).

cnf(c_146,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_332,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_208361,c_332])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.58/6.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.58/6.01  
% 43.58/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.58/6.01  
% 43.58/6.01  ------  iProver source info
% 43.58/6.01  
% 43.58/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.58/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.58/6.01  git: non_committed_changes: false
% 43.58/6.01  git: last_make_outside_of_git: false
% 43.58/6.01  
% 43.58/6.01  ------ 
% 43.58/6.01  
% 43.58/6.01  ------ Input Options
% 43.58/6.01  
% 43.58/6.01  --out_options                           all
% 43.58/6.01  --tptp_safe_out                         true
% 43.58/6.01  --problem_path                          ""
% 43.58/6.01  --include_path                          ""
% 43.58/6.01  --clausifier                            res/vclausify_rel
% 43.58/6.01  --clausifier_options                    ""
% 43.58/6.01  --stdin                                 false
% 43.58/6.01  --stats_out                             all
% 43.58/6.01  
% 43.58/6.01  ------ General Options
% 43.58/6.01  
% 43.58/6.01  --fof                                   false
% 43.58/6.01  --time_out_real                         305.
% 43.58/6.01  --time_out_virtual                      -1.
% 43.58/6.01  --symbol_type_check                     false
% 43.58/6.01  --clausify_out                          false
% 43.58/6.01  --sig_cnt_out                           false
% 43.58/6.01  --trig_cnt_out                          false
% 43.58/6.01  --trig_cnt_out_tolerance                1.
% 43.58/6.01  --trig_cnt_out_sk_spl                   false
% 43.58/6.01  --abstr_cl_out                          false
% 43.58/6.01  
% 43.58/6.01  ------ Global Options
% 43.58/6.01  
% 43.58/6.01  --schedule                              default
% 43.58/6.01  --add_important_lit                     false
% 43.58/6.01  --prop_solver_per_cl                    1000
% 43.58/6.01  --min_unsat_core                        false
% 43.58/6.01  --soft_assumptions                      false
% 43.58/6.01  --soft_lemma_size                       3
% 43.58/6.01  --prop_impl_unit_size                   0
% 43.58/6.01  --prop_impl_unit                        []
% 43.58/6.01  --share_sel_clauses                     true
% 43.58/6.01  --reset_solvers                         false
% 43.58/6.01  --bc_imp_inh                            [conj_cone]
% 43.58/6.01  --conj_cone_tolerance                   3.
% 43.58/6.01  --extra_neg_conj                        none
% 43.58/6.01  --large_theory_mode                     true
% 43.58/6.01  --prolific_symb_bound                   200
% 43.58/6.01  --lt_threshold                          2000
% 43.58/6.01  --clause_weak_htbl                      true
% 43.58/6.01  --gc_record_bc_elim                     false
% 43.58/6.01  
% 43.58/6.01  ------ Preprocessing Options
% 43.58/6.01  
% 43.58/6.01  --preprocessing_flag                    true
% 43.58/6.01  --time_out_prep_mult                    0.1
% 43.58/6.01  --splitting_mode                        input
% 43.58/6.01  --splitting_grd                         true
% 43.58/6.01  --splitting_cvd                         false
% 43.58/6.01  --splitting_cvd_svl                     false
% 43.58/6.01  --splitting_nvd                         32
% 43.58/6.01  --sub_typing                            true
% 43.58/6.01  --prep_gs_sim                           true
% 43.58/6.01  --prep_unflatten                        true
% 43.58/6.01  --prep_res_sim                          true
% 43.58/6.01  --prep_upred                            true
% 43.58/6.01  --prep_sem_filter                       exhaustive
% 43.58/6.01  --prep_sem_filter_out                   false
% 43.58/6.01  --pred_elim                             true
% 43.58/6.01  --res_sim_input                         true
% 43.58/6.01  --eq_ax_congr_red                       true
% 43.58/6.01  --pure_diseq_elim                       true
% 43.58/6.01  --brand_transform                       false
% 43.58/6.01  --non_eq_to_eq                          false
% 43.58/6.01  --prep_def_merge                        true
% 43.58/6.01  --prep_def_merge_prop_impl              false
% 43.58/6.01  --prep_def_merge_mbd                    true
% 43.58/6.01  --prep_def_merge_tr_red                 false
% 43.58/6.01  --prep_def_merge_tr_cl                  false
% 43.58/6.01  --smt_preprocessing                     true
% 43.58/6.01  --smt_ac_axioms                         fast
% 43.58/6.01  --preprocessed_out                      false
% 43.58/6.01  --preprocessed_stats                    false
% 43.58/6.01  
% 43.58/6.01  ------ Abstraction refinement Options
% 43.58/6.01  
% 43.58/6.01  --abstr_ref                             []
% 43.58/6.01  --abstr_ref_prep                        false
% 43.58/6.01  --abstr_ref_until_sat                   false
% 43.58/6.01  --abstr_ref_sig_restrict                funpre
% 43.58/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.58/6.01  --abstr_ref_under                       []
% 43.58/6.01  
% 43.58/6.01  ------ SAT Options
% 43.58/6.01  
% 43.58/6.01  --sat_mode                              false
% 43.58/6.01  --sat_fm_restart_options                ""
% 43.58/6.01  --sat_gr_def                            false
% 43.58/6.01  --sat_epr_types                         true
% 43.58/6.01  --sat_non_cyclic_types                  false
% 43.58/6.01  --sat_finite_models                     false
% 43.58/6.01  --sat_fm_lemmas                         false
% 43.58/6.01  --sat_fm_prep                           false
% 43.58/6.01  --sat_fm_uc_incr                        true
% 43.58/6.01  --sat_out_model                         small
% 43.58/6.01  --sat_out_clauses                       false
% 43.58/6.01  
% 43.58/6.01  ------ QBF Options
% 43.58/6.01  
% 43.58/6.01  --qbf_mode                              false
% 43.58/6.01  --qbf_elim_univ                         false
% 43.58/6.01  --qbf_dom_inst                          none
% 43.58/6.01  --qbf_dom_pre_inst                      false
% 43.58/6.01  --qbf_sk_in                             false
% 43.58/6.01  --qbf_pred_elim                         true
% 43.58/6.01  --qbf_split                             512
% 43.58/6.01  
% 43.58/6.01  ------ BMC1 Options
% 43.58/6.01  
% 43.58/6.01  --bmc1_incremental                      false
% 43.58/6.01  --bmc1_axioms                           reachable_all
% 43.58/6.01  --bmc1_min_bound                        0
% 43.58/6.01  --bmc1_max_bound                        -1
% 43.58/6.01  --bmc1_max_bound_default                -1
% 43.58/6.01  --bmc1_symbol_reachability              true
% 43.58/6.01  --bmc1_property_lemmas                  false
% 43.58/6.01  --bmc1_k_induction                      false
% 43.58/6.01  --bmc1_non_equiv_states                 false
% 43.58/6.01  --bmc1_deadlock                         false
% 43.58/6.01  --bmc1_ucm                              false
% 43.58/6.01  --bmc1_add_unsat_core                   none
% 43.58/6.01  --bmc1_unsat_core_children              false
% 43.58/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.58/6.01  --bmc1_out_stat                         full
% 43.58/6.01  --bmc1_ground_init                      false
% 43.58/6.01  --bmc1_pre_inst_next_state              false
% 43.58/6.01  --bmc1_pre_inst_state                   false
% 43.58/6.01  --bmc1_pre_inst_reach_state             false
% 43.58/6.01  --bmc1_out_unsat_core                   false
% 43.58/6.01  --bmc1_aig_witness_out                  false
% 43.58/6.01  --bmc1_verbose                          false
% 43.58/6.01  --bmc1_dump_clauses_tptp                false
% 43.58/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.58/6.01  --bmc1_dump_file                        -
% 43.58/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.58/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.58/6.01  --bmc1_ucm_extend_mode                  1
% 43.58/6.01  --bmc1_ucm_init_mode                    2
% 43.58/6.01  --bmc1_ucm_cone_mode                    none
% 43.58/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.58/6.01  --bmc1_ucm_relax_model                  4
% 43.58/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.58/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.58/6.01  --bmc1_ucm_layered_model                none
% 43.58/6.01  --bmc1_ucm_max_lemma_size               10
% 43.58/6.01  
% 43.58/6.01  ------ AIG Options
% 43.58/6.01  
% 43.58/6.01  --aig_mode                              false
% 43.58/6.01  
% 43.58/6.01  ------ Instantiation Options
% 43.58/6.01  
% 43.58/6.01  --instantiation_flag                    true
% 43.58/6.01  --inst_sos_flag                         true
% 43.58/6.01  --inst_sos_phase                        true
% 43.58/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.58/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.58/6.01  --inst_lit_sel_side                     num_symb
% 43.58/6.01  --inst_solver_per_active                1400
% 43.58/6.01  --inst_solver_calls_frac                1.
% 43.58/6.01  --inst_passive_queue_type               priority_queues
% 43.58/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.58/6.01  --inst_passive_queues_freq              [25;2]
% 43.58/6.01  --inst_dismatching                      true
% 43.58/6.01  --inst_eager_unprocessed_to_passive     true
% 43.58/6.01  --inst_prop_sim_given                   true
% 43.58/6.01  --inst_prop_sim_new                     false
% 43.58/6.01  --inst_subs_new                         false
% 43.58/6.01  --inst_eq_res_simp                      false
% 43.58/6.01  --inst_subs_given                       false
% 43.58/6.01  --inst_orphan_elimination               true
% 43.58/6.01  --inst_learning_loop_flag               true
% 43.58/6.01  --inst_learning_start                   3000
% 43.58/6.01  --inst_learning_factor                  2
% 43.58/6.01  --inst_start_prop_sim_after_learn       3
% 43.58/6.01  --inst_sel_renew                        solver
% 43.58/6.01  --inst_lit_activity_flag                true
% 43.58/6.01  --inst_restr_to_given                   false
% 43.58/6.01  --inst_activity_threshold               500
% 43.58/6.01  --inst_out_proof                        true
% 43.58/6.01  
% 43.58/6.01  ------ Resolution Options
% 43.58/6.01  
% 43.58/6.01  --resolution_flag                       true
% 43.58/6.01  --res_lit_sel                           adaptive
% 43.58/6.01  --res_lit_sel_side                      none
% 43.58/6.01  --res_ordering                          kbo
% 43.58/6.01  --res_to_prop_solver                    active
% 43.58/6.01  --res_prop_simpl_new                    false
% 43.58/6.01  --res_prop_simpl_given                  true
% 43.58/6.01  --res_passive_queue_type                priority_queues
% 43.58/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.58/6.01  --res_passive_queues_freq               [15;5]
% 43.58/6.01  --res_forward_subs                      full
% 43.58/6.01  --res_backward_subs                     full
% 43.58/6.01  --res_forward_subs_resolution           true
% 43.58/6.01  --res_backward_subs_resolution          true
% 43.58/6.01  --res_orphan_elimination                true
% 43.58/6.01  --res_time_limit                        2.
% 43.58/6.01  --res_out_proof                         true
% 43.58/6.01  
% 43.58/6.01  ------ Superposition Options
% 43.58/6.01  
% 43.58/6.01  --superposition_flag                    true
% 43.58/6.01  --sup_passive_queue_type                priority_queues
% 43.58/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.58/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.58/6.01  --demod_completeness_check              fast
% 43.58/6.01  --demod_use_ground                      true
% 43.58/6.01  --sup_to_prop_solver                    passive
% 43.58/6.01  --sup_prop_simpl_new                    true
% 43.58/6.01  --sup_prop_simpl_given                  true
% 43.58/6.01  --sup_fun_splitting                     true
% 43.58/6.01  --sup_smt_interval                      50000
% 43.58/6.01  
% 43.58/6.01  ------ Superposition Simplification Setup
% 43.58/6.01  
% 43.58/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.58/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.58/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.58/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.58/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.58/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.58/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.58/6.01  --sup_immed_triv                        [TrivRules]
% 43.58/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.58/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.58/6.01  --sup_immed_bw_main                     []
% 43.58/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.58/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.58/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.58/6.01  --sup_input_bw                          []
% 43.58/6.01  
% 43.58/6.01  ------ Combination Options
% 43.58/6.01  
% 43.58/6.01  --comb_res_mult                         3
% 43.58/6.01  --comb_sup_mult                         2
% 43.58/6.01  --comb_inst_mult                        10
% 43.58/6.01  
% 43.58/6.01  ------ Debug Options
% 43.58/6.01  
% 43.58/6.01  --dbg_backtrace                         false
% 43.58/6.01  --dbg_dump_prop_clauses                 false
% 43.58/6.01  --dbg_dump_prop_clauses_file            -
% 43.58/6.01  --dbg_out_stat                          false
% 43.58/6.01  ------ Parsing...
% 43.58/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.58/6.01  
% 43.58/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.58/6.01  
% 43.58/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.58/6.01  
% 43.58/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.58/6.01  ------ Proving...
% 43.58/6.01  ------ Problem Properties 
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  clauses                                 14
% 43.58/6.01  conjectures                             1
% 43.58/6.01  EPR                                     0
% 43.58/6.01  Horn                                    14
% 43.58/6.01  unary                                   10
% 43.58/6.01  binary                                  4
% 43.58/6.01  lits                                    18
% 43.58/6.01  lits eq                                 13
% 43.58/6.01  fd_pure                                 0
% 43.58/6.01  fd_pseudo                               0
% 43.58/6.01  fd_cond                                 0
% 43.58/6.01  fd_pseudo_cond                          0
% 43.58/6.01  AC symbols                              0
% 43.58/6.01  
% 43.58/6.01  ------ Schedule dynamic 5 is on 
% 43.58/6.01  
% 43.58/6.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  ------ 
% 43.58/6.01  Current options:
% 43.58/6.01  ------ 
% 43.58/6.01  
% 43.58/6.01  ------ Input Options
% 43.58/6.01  
% 43.58/6.01  --out_options                           all
% 43.58/6.01  --tptp_safe_out                         true
% 43.58/6.01  --problem_path                          ""
% 43.58/6.01  --include_path                          ""
% 43.58/6.01  --clausifier                            res/vclausify_rel
% 43.58/6.01  --clausifier_options                    ""
% 43.58/6.01  --stdin                                 false
% 43.58/6.01  --stats_out                             all
% 43.58/6.01  
% 43.58/6.01  ------ General Options
% 43.58/6.01  
% 43.58/6.01  --fof                                   false
% 43.58/6.01  --time_out_real                         305.
% 43.58/6.01  --time_out_virtual                      -1.
% 43.58/6.01  --symbol_type_check                     false
% 43.58/6.01  --clausify_out                          false
% 43.58/6.01  --sig_cnt_out                           false
% 43.58/6.01  --trig_cnt_out                          false
% 43.58/6.01  --trig_cnt_out_tolerance                1.
% 43.58/6.01  --trig_cnt_out_sk_spl                   false
% 43.58/6.01  --abstr_cl_out                          false
% 43.58/6.01  
% 43.58/6.01  ------ Global Options
% 43.58/6.01  
% 43.58/6.01  --schedule                              default
% 43.58/6.01  --add_important_lit                     false
% 43.58/6.01  --prop_solver_per_cl                    1000
% 43.58/6.01  --min_unsat_core                        false
% 43.58/6.01  --soft_assumptions                      false
% 43.58/6.01  --soft_lemma_size                       3
% 43.58/6.01  --prop_impl_unit_size                   0
% 43.58/6.01  --prop_impl_unit                        []
% 43.58/6.01  --share_sel_clauses                     true
% 43.58/6.01  --reset_solvers                         false
% 43.58/6.01  --bc_imp_inh                            [conj_cone]
% 43.58/6.01  --conj_cone_tolerance                   3.
% 43.58/6.01  --extra_neg_conj                        none
% 43.58/6.01  --large_theory_mode                     true
% 43.58/6.01  --prolific_symb_bound                   200
% 43.58/6.01  --lt_threshold                          2000
% 43.58/6.01  --clause_weak_htbl                      true
% 43.58/6.01  --gc_record_bc_elim                     false
% 43.58/6.01  
% 43.58/6.01  ------ Preprocessing Options
% 43.58/6.01  
% 43.58/6.01  --preprocessing_flag                    true
% 43.58/6.01  --time_out_prep_mult                    0.1
% 43.58/6.01  --splitting_mode                        input
% 43.58/6.01  --splitting_grd                         true
% 43.58/6.01  --splitting_cvd                         false
% 43.58/6.01  --splitting_cvd_svl                     false
% 43.58/6.01  --splitting_nvd                         32
% 43.58/6.01  --sub_typing                            true
% 43.58/6.01  --prep_gs_sim                           true
% 43.58/6.01  --prep_unflatten                        true
% 43.58/6.01  --prep_res_sim                          true
% 43.58/6.01  --prep_upred                            true
% 43.58/6.01  --prep_sem_filter                       exhaustive
% 43.58/6.01  --prep_sem_filter_out                   false
% 43.58/6.01  --pred_elim                             true
% 43.58/6.01  --res_sim_input                         true
% 43.58/6.01  --eq_ax_congr_red                       true
% 43.58/6.01  --pure_diseq_elim                       true
% 43.58/6.01  --brand_transform                       false
% 43.58/6.01  --non_eq_to_eq                          false
% 43.58/6.01  --prep_def_merge                        true
% 43.58/6.01  --prep_def_merge_prop_impl              false
% 43.58/6.01  --prep_def_merge_mbd                    true
% 43.58/6.01  --prep_def_merge_tr_red                 false
% 43.58/6.01  --prep_def_merge_tr_cl                  false
% 43.58/6.01  --smt_preprocessing                     true
% 43.58/6.01  --smt_ac_axioms                         fast
% 43.58/6.01  --preprocessed_out                      false
% 43.58/6.01  --preprocessed_stats                    false
% 43.58/6.01  
% 43.58/6.01  ------ Abstraction refinement Options
% 43.58/6.01  
% 43.58/6.01  --abstr_ref                             []
% 43.58/6.01  --abstr_ref_prep                        false
% 43.58/6.01  --abstr_ref_until_sat                   false
% 43.58/6.01  --abstr_ref_sig_restrict                funpre
% 43.58/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.58/6.01  --abstr_ref_under                       []
% 43.58/6.01  
% 43.58/6.01  ------ SAT Options
% 43.58/6.01  
% 43.58/6.01  --sat_mode                              false
% 43.58/6.01  --sat_fm_restart_options                ""
% 43.58/6.01  --sat_gr_def                            false
% 43.58/6.01  --sat_epr_types                         true
% 43.58/6.01  --sat_non_cyclic_types                  false
% 43.58/6.01  --sat_finite_models                     false
% 43.58/6.01  --sat_fm_lemmas                         false
% 43.58/6.01  --sat_fm_prep                           false
% 43.58/6.01  --sat_fm_uc_incr                        true
% 43.58/6.01  --sat_out_model                         small
% 43.58/6.01  --sat_out_clauses                       false
% 43.58/6.01  
% 43.58/6.01  ------ QBF Options
% 43.58/6.01  
% 43.58/6.01  --qbf_mode                              false
% 43.58/6.01  --qbf_elim_univ                         false
% 43.58/6.01  --qbf_dom_inst                          none
% 43.58/6.01  --qbf_dom_pre_inst                      false
% 43.58/6.01  --qbf_sk_in                             false
% 43.58/6.01  --qbf_pred_elim                         true
% 43.58/6.01  --qbf_split                             512
% 43.58/6.01  
% 43.58/6.01  ------ BMC1 Options
% 43.58/6.01  
% 43.58/6.01  --bmc1_incremental                      false
% 43.58/6.01  --bmc1_axioms                           reachable_all
% 43.58/6.01  --bmc1_min_bound                        0
% 43.58/6.01  --bmc1_max_bound                        -1
% 43.58/6.01  --bmc1_max_bound_default                -1
% 43.58/6.01  --bmc1_symbol_reachability              true
% 43.58/6.01  --bmc1_property_lemmas                  false
% 43.58/6.01  --bmc1_k_induction                      false
% 43.58/6.01  --bmc1_non_equiv_states                 false
% 43.58/6.01  --bmc1_deadlock                         false
% 43.58/6.01  --bmc1_ucm                              false
% 43.58/6.01  --bmc1_add_unsat_core                   none
% 43.58/6.01  --bmc1_unsat_core_children              false
% 43.58/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.58/6.01  --bmc1_out_stat                         full
% 43.58/6.01  --bmc1_ground_init                      false
% 43.58/6.01  --bmc1_pre_inst_next_state              false
% 43.58/6.01  --bmc1_pre_inst_state                   false
% 43.58/6.01  --bmc1_pre_inst_reach_state             false
% 43.58/6.01  --bmc1_out_unsat_core                   false
% 43.58/6.01  --bmc1_aig_witness_out                  false
% 43.58/6.01  --bmc1_verbose                          false
% 43.58/6.01  --bmc1_dump_clauses_tptp                false
% 43.58/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.58/6.01  --bmc1_dump_file                        -
% 43.58/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.58/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.58/6.01  --bmc1_ucm_extend_mode                  1
% 43.58/6.01  --bmc1_ucm_init_mode                    2
% 43.58/6.01  --bmc1_ucm_cone_mode                    none
% 43.58/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.58/6.01  --bmc1_ucm_relax_model                  4
% 43.58/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.58/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.58/6.01  --bmc1_ucm_layered_model                none
% 43.58/6.01  --bmc1_ucm_max_lemma_size               10
% 43.58/6.01  
% 43.58/6.01  ------ AIG Options
% 43.58/6.01  
% 43.58/6.01  --aig_mode                              false
% 43.58/6.01  
% 43.58/6.01  ------ Instantiation Options
% 43.58/6.01  
% 43.58/6.01  --instantiation_flag                    true
% 43.58/6.01  --inst_sos_flag                         true
% 43.58/6.01  --inst_sos_phase                        true
% 43.58/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.58/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.58/6.01  --inst_lit_sel_side                     none
% 43.58/6.01  --inst_solver_per_active                1400
% 43.58/6.01  --inst_solver_calls_frac                1.
% 43.58/6.01  --inst_passive_queue_type               priority_queues
% 43.58/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.58/6.01  --inst_passive_queues_freq              [25;2]
% 43.58/6.01  --inst_dismatching                      true
% 43.58/6.01  --inst_eager_unprocessed_to_passive     true
% 43.58/6.01  --inst_prop_sim_given                   true
% 43.58/6.01  --inst_prop_sim_new                     false
% 43.58/6.01  --inst_subs_new                         false
% 43.58/6.01  --inst_eq_res_simp                      false
% 43.58/6.01  --inst_subs_given                       false
% 43.58/6.01  --inst_orphan_elimination               true
% 43.58/6.01  --inst_learning_loop_flag               true
% 43.58/6.01  --inst_learning_start                   3000
% 43.58/6.01  --inst_learning_factor                  2
% 43.58/6.01  --inst_start_prop_sim_after_learn       3
% 43.58/6.01  --inst_sel_renew                        solver
% 43.58/6.01  --inst_lit_activity_flag                true
% 43.58/6.01  --inst_restr_to_given                   false
% 43.58/6.01  --inst_activity_threshold               500
% 43.58/6.01  --inst_out_proof                        true
% 43.58/6.01  
% 43.58/6.01  ------ Resolution Options
% 43.58/6.01  
% 43.58/6.01  --resolution_flag                       false
% 43.58/6.01  --res_lit_sel                           adaptive
% 43.58/6.01  --res_lit_sel_side                      none
% 43.58/6.01  --res_ordering                          kbo
% 43.58/6.01  --res_to_prop_solver                    active
% 43.58/6.01  --res_prop_simpl_new                    false
% 43.58/6.01  --res_prop_simpl_given                  true
% 43.58/6.01  --res_passive_queue_type                priority_queues
% 43.58/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.58/6.01  --res_passive_queues_freq               [15;5]
% 43.58/6.01  --res_forward_subs                      full
% 43.58/6.01  --res_backward_subs                     full
% 43.58/6.01  --res_forward_subs_resolution           true
% 43.58/6.01  --res_backward_subs_resolution          true
% 43.58/6.01  --res_orphan_elimination                true
% 43.58/6.01  --res_time_limit                        2.
% 43.58/6.01  --res_out_proof                         true
% 43.58/6.01  
% 43.58/6.01  ------ Superposition Options
% 43.58/6.01  
% 43.58/6.01  --superposition_flag                    true
% 43.58/6.01  --sup_passive_queue_type                priority_queues
% 43.58/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.58/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.58/6.01  --demod_completeness_check              fast
% 43.58/6.01  --demod_use_ground                      true
% 43.58/6.01  --sup_to_prop_solver                    passive
% 43.58/6.01  --sup_prop_simpl_new                    true
% 43.58/6.01  --sup_prop_simpl_given                  true
% 43.58/6.01  --sup_fun_splitting                     true
% 43.58/6.01  --sup_smt_interval                      50000
% 43.58/6.01  
% 43.58/6.01  ------ Superposition Simplification Setup
% 43.58/6.01  
% 43.58/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.58/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.58/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.58/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.58/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.58/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.58/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.58/6.01  --sup_immed_triv                        [TrivRules]
% 43.58/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.58/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.58/6.01  --sup_immed_bw_main                     []
% 43.58/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.58/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.58/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.58/6.01  --sup_input_bw                          []
% 43.58/6.01  
% 43.58/6.01  ------ Combination Options
% 43.58/6.01  
% 43.58/6.01  --comb_res_mult                         3
% 43.58/6.01  --comb_sup_mult                         2
% 43.58/6.01  --comb_inst_mult                        10
% 43.58/6.01  
% 43.58/6.01  ------ Debug Options
% 43.58/6.01  
% 43.58/6.01  --dbg_backtrace                         false
% 43.58/6.01  --dbg_dump_prop_clauses                 false
% 43.58/6.01  --dbg_dump_prop_clauses_file            -
% 43.58/6.01  --dbg_out_stat                          false
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  ------ Proving...
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  % SZS status Theorem for theBenchmark.p
% 43.58/6.01  
% 43.58/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.58/6.01  
% 43.58/6.01  fof(f9,axiom,(
% 43.58/6.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f30,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 43.58/6.01    inference(cnf_transformation,[],[f9])).
% 43.58/6.01  
% 43.58/6.01  fof(f1,axiom,(
% 43.58/6.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f21,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f1])).
% 43.58/6.01  
% 43.58/6.01  fof(f10,axiom,(
% 43.58/6.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f31,plain,(
% 43.58/6.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.58/6.01    inference(cnf_transformation,[],[f10])).
% 43.58/6.01  
% 43.58/6.01  fof(f8,axiom,(
% 43.58/6.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f29,plain,(
% 43.58/6.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f8])).
% 43.58/6.01  
% 43.58/6.01  fof(f7,axiom,(
% 43.58/6.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f16,plain,(
% 43.58/6.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.58/6.01    inference(ennf_transformation,[],[f7])).
% 43.58/6.01  
% 43.58/6.01  fof(f28,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f16])).
% 43.58/6.01  
% 43.58/6.01  fof(f5,axiom,(
% 43.58/6.01    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f26,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 43.58/6.01    inference(cnf_transformation,[],[f5])).
% 43.58/6.01  
% 43.58/6.01  fof(f6,axiom,(
% 43.58/6.01    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f27,plain,(
% 43.58/6.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 43.58/6.01    inference(cnf_transformation,[],[f6])).
% 43.58/6.01  
% 43.58/6.01  fof(f2,axiom,(
% 43.58/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f22,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f2])).
% 43.58/6.01  
% 43.58/6.01  fof(f11,axiom,(
% 43.58/6.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f32,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f11])).
% 43.58/6.01  
% 43.58/6.01  fof(f3,axiom,(
% 43.58/6.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f18,plain,(
% 43.58/6.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 43.58/6.01    inference(nnf_transformation,[],[f3])).
% 43.58/6.01  
% 43.58/6.01  fof(f24,plain,(
% 43.58/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f18])).
% 43.58/6.01  
% 43.58/6.01  fof(f12,axiom,(
% 43.58/6.01    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f33,plain,(
% 43.58/6.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 43.58/6.01    inference(cnf_transformation,[],[f12])).
% 43.58/6.01  
% 43.58/6.01  fof(f13,conjecture,(
% 43.58/6.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.58/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.58/6.01  
% 43.58/6.01  fof(f14,negated_conjecture,(
% 43.58/6.01    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.58/6.01    inference(negated_conjecture,[],[f13])).
% 43.58/6.01  
% 43.58/6.01  fof(f17,plain,(
% 43.58/6.01    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.58/6.01    inference(ennf_transformation,[],[f14])).
% 43.58/6.01  
% 43.58/6.01  fof(f19,plain,(
% 43.58/6.01    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 43.58/6.01    introduced(choice_axiom,[])).
% 43.58/6.01  
% 43.58/6.01  fof(f20,plain,(
% 43.58/6.01    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 43.58/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).
% 43.58/6.01  
% 43.58/6.01  fof(f34,plain,(
% 43.58/6.01    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 43.58/6.01    inference(cnf_transformation,[],[f20])).
% 43.58/6.01  
% 43.58/6.01  cnf(c_9,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 43.58/6.01      inference(cnf_transformation,[],[f30]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_0,plain,
% 43.58/6.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 43.58/6.01      inference(cnf_transformation,[],[f21]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_10,plain,
% 43.58/6.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.58/6.01      inference(cnf_transformation,[],[f31]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_8,plain,
% 43.58/6.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 43.58/6.01      inference(cnf_transformation,[],[f29]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_306,plain,
% 43.58/6.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 43.58/6.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_439,plain,
% 43.58/6.01      ( r1_tarski(X0,X0) = iProver_top ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_10,c_306]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_7,plain,
% 43.58/6.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 43.58/6.01      inference(cnf_transformation,[],[f28]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_307,plain,
% 43.58/6.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 43.58/6.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_529,plain,
% 43.58/6.01      ( k3_xboole_0(X0,X0) = X0 ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_439,c_307]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_5,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 43.58/6.01      inference(cnf_transformation,[],[f26]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_780,plain,
% 43.58/6.01      ( k2_xboole_0(X0,X0) = X0 ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_529,c_5]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_6,plain,
% 43.58/6.01      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 43.58/6.01      inference(cnf_transformation,[],[f27]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_855,plain,
% 43.58/6.01      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_780,c_6]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1,plain,
% 43.58/6.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 43.58/6.01      inference(cnf_transformation,[],[f22]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_436,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_11,plain,
% 43.58/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 43.58/6.01      inference(cnf_transformation,[],[f32]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_634,plain,
% 43.58/6.01      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_11,c_10]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_635,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_634,c_10]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_851,plain,
% 43.58/6.01      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_635,c_6]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_856,plain,
% 43.58/6.01      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_855,c_436,c_851]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1061,plain,
% 43.58/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_856,c_5]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_2301,plain,
% 43.58/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_0,c_1061]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_3349,plain,
% 43.58/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_9,c_2301]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_629,plain,
% 43.58/6.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_2,plain,
% 43.58/6.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 43.58/6.01      inference(cnf_transformation,[],[f24]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_310,plain,
% 43.58/6.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 43.58/6.01      | r1_tarski(X0,X1) != iProver_top ),
% 43.58/6.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1605,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_306,c_310]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1961,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_1605,c_9]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1964,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_1961,c_635]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_2157,plain,
% 43.58/6.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_629,c_1964]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_3394,plain,
% 43.58/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_3349,c_2157]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_3358,plain,
% 43.58/6.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_1964,c_2301]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_3391,plain,
% 43.58/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_3358,c_1964]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_3484,plain,
% 43.58/6.01      ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_3391,c_6]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_200968,plain,
% 43.58/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_3394,c_3484]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_854,plain,
% 43.58/6.01      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_780,c_6]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_848,plain,
% 43.58/6.01      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_635,c_6]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_857,plain,
% 43.58/6.01      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_854,c_5,c_848]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1118,plain,
% 43.58/6.01      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_0,c_857]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_202049,plain,
% 43.58/6.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_200968,c_1118]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_204653,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_202049,c_11]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_12,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.58/6.01      inference(cnf_transformation,[],[f33]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1288,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_9,c_629]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_1298,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 43.58/6.01      inference(demodulation,[status(thm)],[c_1288,c_629]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_2896,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_12,c_1298]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_2924,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.58/6.01      inference(light_normalisation,[status(thm)],[c_2896,c_12]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_63510,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X1))) ),
% 43.58/6.01      inference(superposition,[status(thm)],[c_436,c_2924]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_63819,plain,
% 43.58/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,X1) ),
% 43.58/6.01      inference(demodulation,[status(thm)],[c_63510,c_12,c_436]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_204992,plain,
% 43.58/6.01      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 43.58/6.01      inference(demodulation,[status(thm)],[c_204653,c_63819]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_13,negated_conjecture,
% 43.58/6.01      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
% 43.58/6.01      inference(cnf_transformation,[],[f34]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_208361,plain,
% 43.58/6.01      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 43.58/6.01      inference(demodulation,[status(thm)],[c_204992,c_13]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_146,plain,( X0 = X0 ),theory(equality) ).
% 43.58/6.01  
% 43.58/6.01  cnf(c_332,plain,
% 43.58/6.01      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 43.58/6.01      inference(instantiation,[status(thm)],[c_146]) ).
% 43.58/6.01  
% 43.58/6.01  cnf(contradiction,plain,
% 43.58/6.01      ( $false ),
% 43.58/6.01      inference(minisat,[status(thm)],[c_208361,c_332]) ).
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.58/6.01  
% 43.58/6.01  ------                               Statistics
% 43.58/6.01  
% 43.58/6.01  ------ General
% 43.58/6.01  
% 43.58/6.01  abstr_ref_over_cycles:                  0
% 43.58/6.01  abstr_ref_under_cycles:                 0
% 43.58/6.01  gc_basic_clause_elim:                   0
% 43.58/6.01  forced_gc_time:                         0
% 43.58/6.01  parsing_time:                           0.007
% 43.58/6.01  unif_index_cands_time:                  0.
% 43.58/6.01  unif_index_add_time:                    0.
% 43.58/6.01  orderings_time:                         0.
% 43.58/6.01  out_proof_time:                         0.012
% 43.58/6.01  total_time:                             5.204
% 43.58/6.01  num_of_symbols:                         38
% 43.58/6.01  num_of_terms:                           255693
% 43.58/6.01  
% 43.58/6.01  ------ Preprocessing
% 43.58/6.01  
% 43.58/6.01  num_of_splits:                          0
% 43.58/6.01  num_of_split_atoms:                     0
% 43.58/6.01  num_of_reused_defs:                     0
% 43.58/6.01  num_eq_ax_congr_red:                    4
% 43.58/6.01  num_of_sem_filtered_clauses:            1
% 43.58/6.01  num_of_subtypes:                        0
% 43.58/6.01  monotx_restored_types:                  0
% 43.58/6.01  sat_num_of_epr_types:                   0
% 43.58/6.01  sat_num_of_non_cyclic_types:            0
% 43.58/6.01  sat_guarded_non_collapsed_types:        0
% 43.58/6.01  num_pure_diseq_elim:                    0
% 43.58/6.01  simp_replaced_by:                       0
% 43.58/6.01  res_preprocessed:                       55
% 43.58/6.01  prep_upred:                             0
% 43.58/6.01  prep_unflattend:                        6
% 43.58/6.01  smt_new_axioms:                         0
% 43.58/6.01  pred_elim_cands:                        1
% 43.58/6.01  pred_elim:                              0
% 43.58/6.01  pred_elim_cl:                           0
% 43.58/6.01  pred_elim_cycles:                       1
% 43.58/6.01  merged_defs:                            6
% 43.58/6.01  merged_defs_ncl:                        0
% 43.58/6.01  bin_hyper_res:                          6
% 43.58/6.01  prep_cycles:                            3
% 43.58/6.01  pred_elim_time:                         0.
% 43.58/6.01  splitting_time:                         0.
% 43.58/6.01  sem_filter_time:                        0.
% 43.58/6.01  monotx_time:                            0.
% 43.58/6.01  subtype_inf_time:                       0.
% 43.58/6.01  
% 43.58/6.01  ------ Problem properties
% 43.58/6.01  
% 43.58/6.01  clauses:                                14
% 43.58/6.01  conjectures:                            1
% 43.58/6.01  epr:                                    0
% 43.58/6.01  horn:                                   14
% 43.58/6.01  ground:                                 1
% 43.58/6.01  unary:                                  10
% 43.58/6.01  binary:                                 4
% 43.58/6.01  lits:                                   18
% 43.58/6.01  lits_eq:                                13
% 43.58/6.01  fd_pure:                                0
% 43.58/6.01  fd_pseudo:                              0
% 43.58/6.01  fd_cond:                                0
% 43.58/6.01  fd_pseudo_cond:                         0
% 43.58/6.01  ac_symbols:                             0
% 43.58/6.01  
% 43.58/6.01  ------ Propositional Solver
% 43.58/6.01  
% 43.58/6.01  prop_solver_calls:                      41
% 43.58/6.01  prop_fast_solver_calls:                 781
% 43.58/6.01  smt_solver_calls:                       0
% 43.58/6.01  smt_fast_solver_calls:                  0
% 43.58/6.01  prop_num_of_clauses:                    40900
% 43.58/6.01  prop_preprocess_simplified:             39626
% 43.58/6.01  prop_fo_subsumed:                       1
% 43.58/6.01  prop_solver_time:                       0.
% 43.58/6.01  smt_solver_time:                        0.
% 43.58/6.01  smt_fast_solver_time:                   0.
% 43.58/6.01  prop_fast_solver_time:                  0.
% 43.58/6.01  prop_unsat_core_time:                   0.005
% 43.58/6.01  
% 43.58/6.01  ------ QBF
% 43.58/6.01  
% 43.58/6.01  qbf_q_res:                              0
% 43.58/6.01  qbf_num_tautologies:                    0
% 43.58/6.01  qbf_prep_cycles:                        0
% 43.58/6.01  
% 43.58/6.01  ------ BMC1
% 43.58/6.01  
% 43.58/6.01  bmc1_current_bound:                     -1
% 43.58/6.01  bmc1_last_solved_bound:                 -1
% 43.58/6.01  bmc1_unsat_core_size:                   -1
% 43.58/6.01  bmc1_unsat_core_parents_size:           -1
% 43.58/6.01  bmc1_merge_next_fun:                    0
% 43.58/6.01  bmc1_unsat_core_clauses_time:           0.
% 43.58/6.01  
% 43.58/6.01  ------ Instantiation
% 43.58/6.01  
% 43.58/6.01  inst_num_of_clauses:                    7804
% 43.58/6.01  inst_num_in_passive:                    3836
% 43.58/6.01  inst_num_in_active:                     2148
% 43.58/6.01  inst_num_in_unprocessed:                1820
% 43.58/6.01  inst_num_of_loops:                      2530
% 43.58/6.01  inst_num_of_learning_restarts:          0
% 43.58/6.01  inst_num_moves_active_passive:          377
% 43.58/6.01  inst_lit_activity:                      0
% 43.58/6.01  inst_lit_activity_moves:                1
% 43.58/6.01  inst_num_tautologies:                   0
% 43.58/6.01  inst_num_prop_implied:                  0
% 43.58/6.01  inst_num_existing_simplified:           0
% 43.58/6.01  inst_num_eq_res_simplified:             0
% 43.58/6.01  inst_num_child_elim:                    0
% 43.58/6.01  inst_num_of_dismatching_blockings:      4018
% 43.58/6.01  inst_num_of_non_proper_insts:           8610
% 43.58/6.01  inst_num_of_duplicates:                 0
% 43.58/6.01  inst_inst_num_from_inst_to_res:         0
% 43.58/6.01  inst_dismatching_checking_time:         0.
% 43.58/6.01  
% 43.58/6.01  ------ Resolution
% 43.58/6.01  
% 43.58/6.01  res_num_of_clauses:                     0
% 43.58/6.01  res_num_in_passive:                     0
% 43.58/6.01  res_num_in_active:                      0
% 43.58/6.01  res_num_of_loops:                       58
% 43.58/6.01  res_forward_subset_subsumed:            2704
% 43.58/6.01  res_backward_subset_subsumed:           0
% 43.58/6.01  res_forward_subsumed:                   0
% 43.58/6.01  res_backward_subsumed:                  0
% 43.58/6.01  res_forward_subsumption_resolution:     0
% 43.58/6.01  res_backward_subsumption_resolution:    0
% 43.58/6.01  res_clause_to_clause_subsumption:       393920
% 43.58/6.01  res_orphan_elimination:                 0
% 43.58/6.01  res_tautology_del:                      658
% 43.58/6.01  res_num_eq_res_simplified:              0
% 43.58/6.01  res_num_sel_changes:                    0
% 43.58/6.01  res_moves_from_active_to_pass:          0
% 43.58/6.01  
% 43.58/6.01  ------ Superposition
% 43.58/6.01  
% 43.58/6.01  sup_time_total:                         0.
% 43.58/6.01  sup_time_generating:                    0.
% 43.58/6.01  sup_time_sim_full:                      0.
% 43.58/6.01  sup_time_sim_immed:                     0.
% 43.58/6.01  
% 43.58/6.01  sup_num_of_clauses:                     13266
% 43.58/6.01  sup_num_in_active:                      474
% 43.58/6.01  sup_num_in_passive:                     12792
% 43.58/6.01  sup_num_of_loops:                       504
% 43.58/6.01  sup_fw_superposition:                   67615
% 43.58/6.01  sup_bw_superposition:                   47070
% 43.58/6.01  sup_immediate_simplified:               48689
% 43.58/6.01  sup_given_eliminated:                   2
% 43.58/6.01  comparisons_done:                       0
% 43.58/6.01  comparisons_avoided:                    0
% 43.58/6.01  
% 43.58/6.01  ------ Simplifications
% 43.58/6.01  
% 43.58/6.01  
% 43.58/6.01  sim_fw_subset_subsumed:                 1
% 43.58/6.01  sim_bw_subset_subsumed:                 0
% 43.58/6.01  sim_fw_subsumed:                        9974
% 43.58/6.01  sim_bw_subsumed:                        60
% 43.58/6.01  sim_fw_subsumption_res:                 0
% 43.58/6.01  sim_bw_subsumption_res:                 0
% 43.58/6.01  sim_tautology_del:                      0
% 43.58/6.01  sim_eq_tautology_del:                   9778
% 43.58/6.01  sim_eq_res_simp:                        3
% 43.58/6.01  sim_fw_demodulated:                     22799
% 43.58/6.01  sim_bw_demodulated:                     274
% 43.58/6.01  sim_light_normalised:                   22618
% 43.58/6.01  sim_joinable_taut:                      0
% 43.58/6.01  sim_joinable_simp:                      0
% 43.58/6.01  sim_ac_normalised:                      0
% 43.58/6.01  sim_smt_subsumption:                    0
% 43.58/6.01  
%------------------------------------------------------------------------------
