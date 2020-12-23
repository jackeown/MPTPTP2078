%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:40 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 116 expanded)
%              Number of clauses        :   28 (  35 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 455 expanded)
%              Number of equality atoms :   55 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,sK4)
          | ~ r1_xboole_0(X1,k3_subset_1(X0,sK4)) )
        & ( r1_tarski(X1,sK4)
          | r1_xboole_0(X1,k3_subset_1(X0,sK4)) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK3,X2)
            | ~ r1_xboole_0(sK3,k3_subset_1(sK2,X2)) )
          & ( r1_tarski(sK3,X2)
            | r1_xboole_0(sK3,k3_subset_1(sK2,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ r1_tarski(sK3,sK4)
      | ~ r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) )
    & ( r1_tarski(sK3,sK4)
      | r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f48,f47])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f56])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f78,f56])).

fof(f16,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,
    ( r1_tarski(sK3,sK4)
    | r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1135,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1143,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1240,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1143,c_27])).

cnf(c_4883,plain,
    ( k6_subset_1(sK2,sK4) = k3_subset_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1135,c_1240])).

cnf(c_24,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1142,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5223,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4883,c_1142])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1140,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4193,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1135,c_1140])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X2)
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK2,sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4193,c_1138])).

cnf(c_4229,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4208])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X0,X2)
    | ~ r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK2,sK4)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4193,c_1139])).

cnf(c_4226,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4207])).

cnf(c_30,negated_conjecture,
    ( ~ r1_xboole_0(sK3,k3_subset_1(sK2,sK4))
    | ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,plain,
    ( r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( r1_xboole_0(sK3,k3_subset_1(sK2,sK4))
    | r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5223,c_4229,c_4226,c_37,c_36,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:25:22 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.52/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/0.97  
% 2.52/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.97  
% 2.52/0.97  ------  iProver source info
% 2.52/0.97  
% 2.52/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.97  git: non_committed_changes: false
% 2.52/0.97  git: last_make_outside_of_git: false
% 2.52/0.97  
% 2.52/0.97  ------ 
% 2.52/0.97  
% 2.52/0.97  ------ Input Options
% 2.52/0.97  
% 2.52/0.97  --out_options                           all
% 2.52/0.97  --tptp_safe_out                         true
% 2.52/0.97  --problem_path                          ""
% 2.52/0.97  --include_path                          ""
% 2.52/0.97  --clausifier                            res/vclausify_rel
% 2.52/0.97  --clausifier_options                    --mode clausify
% 2.52/0.97  --stdin                                 false
% 2.52/0.97  --stats_out                             all
% 2.52/0.97  
% 2.52/0.97  ------ General Options
% 2.52/0.97  
% 2.52/0.97  --fof                                   false
% 2.52/0.97  --time_out_real                         305.
% 2.52/0.97  --time_out_virtual                      -1.
% 2.52/0.97  --symbol_type_check                     false
% 2.52/0.97  --clausify_out                          false
% 2.52/0.97  --sig_cnt_out                           false
% 2.52/0.97  --trig_cnt_out                          false
% 2.52/0.97  --trig_cnt_out_tolerance                1.
% 2.52/0.97  --trig_cnt_out_sk_spl                   false
% 2.52/0.97  --abstr_cl_out                          false
% 2.52/0.97  
% 2.52/0.97  ------ Global Options
% 2.52/0.97  
% 2.52/0.97  --schedule                              default
% 2.52/0.97  --add_important_lit                     false
% 2.52/0.97  --prop_solver_per_cl                    1000
% 2.52/0.97  --min_unsat_core                        false
% 2.52/0.97  --soft_assumptions                      false
% 2.52/0.97  --soft_lemma_size                       3
% 2.52/0.97  --prop_impl_unit_size                   0
% 2.52/0.97  --prop_impl_unit                        []
% 2.52/0.97  --share_sel_clauses                     true
% 2.52/0.97  --reset_solvers                         false
% 2.52/0.97  --bc_imp_inh                            [conj_cone]
% 2.52/0.97  --conj_cone_tolerance                   3.
% 2.52/0.97  --extra_neg_conj                        none
% 2.52/0.97  --large_theory_mode                     true
% 2.52/0.97  --prolific_symb_bound                   200
% 2.52/0.97  --lt_threshold                          2000
% 2.52/0.97  --clause_weak_htbl                      true
% 2.52/0.97  --gc_record_bc_elim                     false
% 2.52/0.97  
% 2.52/0.97  ------ Preprocessing Options
% 2.52/0.97  
% 2.52/0.97  --preprocessing_flag                    true
% 2.52/0.97  --time_out_prep_mult                    0.1
% 2.52/0.97  --splitting_mode                        input
% 2.52/0.97  --splitting_grd                         true
% 2.52/0.97  --splitting_cvd                         false
% 2.52/0.97  --splitting_cvd_svl                     false
% 2.52/0.97  --splitting_nvd                         32
% 2.52/0.97  --sub_typing                            true
% 2.52/0.97  --prep_gs_sim                           true
% 2.52/0.97  --prep_unflatten                        true
% 2.52/0.97  --prep_res_sim                          true
% 2.52/0.97  --prep_upred                            true
% 2.52/0.97  --prep_sem_filter                       exhaustive
% 2.52/0.97  --prep_sem_filter_out                   false
% 2.52/0.97  --pred_elim                             true
% 2.52/0.97  --res_sim_input                         true
% 2.52/0.97  --eq_ax_congr_red                       true
% 2.52/0.97  --pure_diseq_elim                       true
% 2.52/0.97  --brand_transform                       false
% 2.52/0.97  --non_eq_to_eq                          false
% 2.52/0.97  --prep_def_merge                        true
% 2.52/0.97  --prep_def_merge_prop_impl              false
% 2.52/0.97  --prep_def_merge_mbd                    true
% 2.52/0.97  --prep_def_merge_tr_red                 false
% 2.52/0.97  --prep_def_merge_tr_cl                  false
% 2.52/0.97  --smt_preprocessing                     true
% 2.52/0.97  --smt_ac_axioms                         fast
% 2.52/0.97  --preprocessed_out                      false
% 2.52/0.97  --preprocessed_stats                    false
% 2.52/0.97  
% 2.52/0.97  ------ Abstraction refinement Options
% 2.52/0.97  
% 2.52/0.97  --abstr_ref                             []
% 2.52/0.97  --abstr_ref_prep                        false
% 2.52/0.97  --abstr_ref_until_sat                   false
% 2.52/0.97  --abstr_ref_sig_restrict                funpre
% 2.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.97  --abstr_ref_under                       []
% 2.52/0.97  
% 2.52/0.97  ------ SAT Options
% 2.52/0.97  
% 2.52/0.97  --sat_mode                              false
% 2.52/0.97  --sat_fm_restart_options                ""
% 2.52/0.97  --sat_gr_def                            false
% 2.52/0.97  --sat_epr_types                         true
% 2.52/0.97  --sat_non_cyclic_types                  false
% 2.52/0.97  --sat_finite_models                     false
% 2.52/0.97  --sat_fm_lemmas                         false
% 2.52/0.97  --sat_fm_prep                           false
% 2.52/0.97  --sat_fm_uc_incr                        true
% 2.52/0.97  --sat_out_model                         small
% 2.52/0.97  --sat_out_clauses                       false
% 2.52/0.97  
% 2.52/0.97  ------ QBF Options
% 2.52/0.97  
% 2.52/0.97  --qbf_mode                              false
% 2.52/0.97  --qbf_elim_univ                         false
% 2.52/0.97  --qbf_dom_inst                          none
% 2.52/0.97  --qbf_dom_pre_inst                      false
% 2.52/0.97  --qbf_sk_in                             false
% 2.52/0.97  --qbf_pred_elim                         true
% 2.52/0.97  --qbf_split                             512
% 2.52/0.97  
% 2.52/0.97  ------ BMC1 Options
% 2.52/0.97  
% 2.52/0.97  --bmc1_incremental                      false
% 2.52/0.97  --bmc1_axioms                           reachable_all
% 2.52/0.97  --bmc1_min_bound                        0
% 2.52/0.97  --bmc1_max_bound                        -1
% 2.52/0.97  --bmc1_max_bound_default                -1
% 2.52/0.97  --bmc1_symbol_reachability              true
% 2.52/0.97  --bmc1_property_lemmas                  false
% 2.52/0.97  --bmc1_k_induction                      false
% 2.52/0.97  --bmc1_non_equiv_states                 false
% 2.52/0.97  --bmc1_deadlock                         false
% 2.52/0.97  --bmc1_ucm                              false
% 2.52/0.97  --bmc1_add_unsat_core                   none
% 2.52/0.97  --bmc1_unsat_core_children              false
% 2.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.97  --bmc1_out_stat                         full
% 2.52/0.97  --bmc1_ground_init                      false
% 2.52/0.97  --bmc1_pre_inst_next_state              false
% 2.52/0.97  --bmc1_pre_inst_state                   false
% 2.52/0.97  --bmc1_pre_inst_reach_state             false
% 2.52/0.97  --bmc1_out_unsat_core                   false
% 2.52/0.97  --bmc1_aig_witness_out                  false
% 2.52/0.97  --bmc1_verbose                          false
% 2.52/0.97  --bmc1_dump_clauses_tptp                false
% 2.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.97  --bmc1_dump_file                        -
% 2.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.97  --bmc1_ucm_extend_mode                  1
% 2.52/0.97  --bmc1_ucm_init_mode                    2
% 2.52/0.97  --bmc1_ucm_cone_mode                    none
% 2.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.97  --bmc1_ucm_relax_model                  4
% 2.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.97  --bmc1_ucm_layered_model                none
% 2.52/0.97  --bmc1_ucm_max_lemma_size               10
% 2.52/0.97  
% 2.52/0.97  ------ AIG Options
% 2.52/0.97  
% 2.52/0.97  --aig_mode                              false
% 2.52/0.97  
% 2.52/0.97  ------ Instantiation Options
% 2.52/0.97  
% 2.52/0.97  --instantiation_flag                    true
% 2.52/0.97  --inst_sos_flag                         false
% 2.52/0.97  --inst_sos_phase                        true
% 2.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.97  --inst_lit_sel_side                     num_symb
% 2.52/0.97  --inst_solver_per_active                1400
% 2.52/0.97  --inst_solver_calls_frac                1.
% 2.52/0.97  --inst_passive_queue_type               priority_queues
% 2.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.97  --inst_passive_queues_freq              [25;2]
% 2.52/0.97  --inst_dismatching                      true
% 2.52/0.97  --inst_eager_unprocessed_to_passive     true
% 2.52/0.97  --inst_prop_sim_given                   true
% 2.52/0.97  --inst_prop_sim_new                     false
% 2.52/0.97  --inst_subs_new                         false
% 2.52/0.97  --inst_eq_res_simp                      false
% 2.52/0.97  --inst_subs_given                       false
% 2.52/0.97  --inst_orphan_elimination               true
% 2.52/0.97  --inst_learning_loop_flag               true
% 2.52/0.97  --inst_learning_start                   3000
% 2.52/0.97  --inst_learning_factor                  2
% 2.52/0.97  --inst_start_prop_sim_after_learn       3
% 2.52/0.97  --inst_sel_renew                        solver
% 2.52/0.97  --inst_lit_activity_flag                true
% 2.52/0.97  --inst_restr_to_given                   false
% 2.52/0.97  --inst_activity_threshold               500
% 2.52/0.97  --inst_out_proof                        true
% 2.52/0.97  
% 2.52/0.97  ------ Resolution Options
% 2.52/0.97  
% 2.52/0.97  --resolution_flag                       true
% 2.52/0.97  --res_lit_sel                           adaptive
% 2.52/0.97  --res_lit_sel_side                      none
% 2.52/0.97  --res_ordering                          kbo
% 2.52/0.97  --res_to_prop_solver                    active
% 2.52/0.97  --res_prop_simpl_new                    false
% 2.52/0.97  --res_prop_simpl_given                  true
% 2.52/0.97  --res_passive_queue_type                priority_queues
% 2.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.97  --res_passive_queues_freq               [15;5]
% 2.52/0.97  --res_forward_subs                      full
% 2.52/0.97  --res_backward_subs                     full
% 2.52/0.97  --res_forward_subs_resolution           true
% 2.52/0.97  --res_backward_subs_resolution          true
% 2.52/0.97  --res_orphan_elimination                true
% 2.52/0.97  --res_time_limit                        2.
% 2.52/0.97  --res_out_proof                         true
% 2.52/0.97  
% 2.52/0.97  ------ Superposition Options
% 2.52/0.97  
% 2.52/0.97  --superposition_flag                    true
% 2.52/0.97  --sup_passive_queue_type                priority_queues
% 2.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.97  --demod_completeness_check              fast
% 2.52/0.97  --demod_use_ground                      true
% 2.52/0.97  --sup_to_prop_solver                    passive
% 2.52/0.97  --sup_prop_simpl_new                    true
% 2.52/0.97  --sup_prop_simpl_given                  true
% 2.52/0.97  --sup_fun_splitting                     false
% 2.52/0.97  --sup_smt_interval                      50000
% 2.52/0.97  
% 2.52/0.97  ------ Superposition Simplification Setup
% 2.52/0.97  
% 2.52/0.97  --sup_indices_passive                   []
% 2.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.97  --sup_full_bw                           [BwDemod]
% 2.52/0.97  --sup_immed_triv                        [TrivRules]
% 2.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.97  --sup_immed_bw_main                     []
% 2.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.97  
% 2.52/0.97  ------ Combination Options
% 2.52/0.97  
% 2.52/0.97  --comb_res_mult                         3
% 2.52/0.97  --comb_sup_mult                         2
% 2.52/0.97  --comb_inst_mult                        10
% 2.52/0.97  
% 2.52/0.97  ------ Debug Options
% 2.52/0.97  
% 2.52/0.97  --dbg_backtrace                         false
% 2.52/0.97  --dbg_dump_prop_clauses                 false
% 2.52/0.97  --dbg_dump_prop_clauses_file            -
% 2.52/0.97  --dbg_out_stat                          false
% 2.52/0.97  ------ Parsing...
% 2.52/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.97  
% 2.52/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.52/0.97  
% 2.52/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.97  
% 2.52/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.97  ------ Proving...
% 2.52/0.97  ------ Problem Properties 
% 2.52/0.97  
% 2.52/0.97  
% 2.52/0.97  clauses                                 34
% 2.52/0.97  conjectures                             4
% 2.52/0.97  EPR                                     6
% 2.52/0.97  Horn                                    29
% 2.52/0.97  unary                                   9
% 2.52/0.97  binary                                  15
% 2.52/0.97  lits                                    71
% 2.52/0.97  lits eq                                 10
% 2.52/0.97  fd_pure                                 0
% 2.52/0.97  fd_pseudo                               0
% 2.52/0.97  fd_cond                                 0
% 2.52/0.97  fd_pseudo_cond                          2
% 2.52/0.97  AC symbols                              0
% 2.52/0.97  
% 2.52/0.97  ------ Schedule dynamic 5 is on 
% 2.52/0.97  
% 2.52/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.97  
% 2.52/0.97  
% 2.52/0.97  ------ 
% 2.52/0.97  Current options:
% 2.52/0.97  ------ 
% 2.52/0.97  
% 2.52/0.97  ------ Input Options
% 2.52/0.97  
% 2.52/0.97  --out_options                           all
% 2.52/0.97  --tptp_safe_out                         true
% 2.52/0.97  --problem_path                          ""
% 2.52/0.97  --include_path                          ""
% 2.52/0.97  --clausifier                            res/vclausify_rel
% 2.52/0.97  --clausifier_options                    --mode clausify
% 2.52/0.97  --stdin                                 false
% 2.52/0.97  --stats_out                             all
% 2.52/0.97  
% 2.52/0.97  ------ General Options
% 2.52/0.97  
% 2.52/0.97  --fof                                   false
% 2.52/0.97  --time_out_real                         305.
% 2.52/0.97  --time_out_virtual                      -1.
% 2.52/0.97  --symbol_type_check                     false
% 2.52/0.97  --clausify_out                          false
% 2.52/0.97  --sig_cnt_out                           false
% 2.52/0.97  --trig_cnt_out                          false
% 2.52/0.97  --trig_cnt_out_tolerance                1.
% 2.52/0.97  --trig_cnt_out_sk_spl                   false
% 2.52/0.97  --abstr_cl_out                          false
% 2.52/0.97  
% 2.52/0.97  ------ Global Options
% 2.52/0.97  
% 2.52/0.97  --schedule                              default
% 2.52/0.97  --add_important_lit                     false
% 2.52/0.97  --prop_solver_per_cl                    1000
% 2.52/0.97  --min_unsat_core                        false
% 2.52/0.97  --soft_assumptions                      false
% 2.52/0.97  --soft_lemma_size                       3
% 2.52/0.97  --prop_impl_unit_size                   0
% 2.52/0.97  --prop_impl_unit                        []
% 2.52/0.97  --share_sel_clauses                     true
% 2.52/0.97  --reset_solvers                         false
% 2.52/0.97  --bc_imp_inh                            [conj_cone]
% 2.52/0.97  --conj_cone_tolerance                   3.
% 2.52/0.97  --extra_neg_conj                        none
% 2.52/0.97  --large_theory_mode                     true
% 2.52/0.97  --prolific_symb_bound                   200
% 2.52/0.97  --lt_threshold                          2000
% 2.52/0.97  --clause_weak_htbl                      true
% 2.52/0.97  --gc_record_bc_elim                     false
% 2.52/0.97  
% 2.52/0.97  ------ Preprocessing Options
% 2.52/0.97  
% 2.52/0.97  --preprocessing_flag                    true
% 2.52/0.97  --time_out_prep_mult                    0.1
% 2.52/0.97  --splitting_mode                        input
% 2.52/0.97  --splitting_grd                         true
% 2.52/0.97  --splitting_cvd                         false
% 2.52/0.97  --splitting_cvd_svl                     false
% 2.52/0.97  --splitting_nvd                         32
% 2.52/0.97  --sub_typing                            true
% 2.52/0.97  --prep_gs_sim                           true
% 2.52/0.97  --prep_unflatten                        true
% 2.52/0.97  --prep_res_sim                          true
% 2.52/0.97  --prep_upred                            true
% 2.52/0.97  --prep_sem_filter                       exhaustive
% 2.52/0.97  --prep_sem_filter_out                   false
% 2.52/0.97  --pred_elim                             true
% 2.52/0.97  --res_sim_input                         true
% 2.52/0.97  --eq_ax_congr_red                       true
% 2.52/0.97  --pure_diseq_elim                       true
% 2.52/0.97  --brand_transform                       false
% 2.52/0.97  --non_eq_to_eq                          false
% 2.52/0.97  --prep_def_merge                        true
% 2.52/0.97  --prep_def_merge_prop_impl              false
% 2.52/0.97  --prep_def_merge_mbd                    true
% 2.52/0.97  --prep_def_merge_tr_red                 false
% 2.52/0.97  --prep_def_merge_tr_cl                  false
% 2.52/0.97  --smt_preprocessing                     true
% 2.52/0.97  --smt_ac_axioms                         fast
% 2.52/0.97  --preprocessed_out                      false
% 2.52/0.97  --preprocessed_stats                    false
% 2.52/0.97  
% 2.52/0.97  ------ Abstraction refinement Options
% 2.52/0.97  
% 2.52/0.97  --abstr_ref                             []
% 2.52/0.97  --abstr_ref_prep                        false
% 2.52/0.97  --abstr_ref_until_sat                   false
% 2.52/0.97  --abstr_ref_sig_restrict                funpre
% 2.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.97  --abstr_ref_under                       []
% 2.52/0.97  
% 2.52/0.97  ------ SAT Options
% 2.52/0.97  
% 2.52/0.97  --sat_mode                              false
% 2.52/0.97  --sat_fm_restart_options                ""
% 2.52/0.97  --sat_gr_def                            false
% 2.52/0.97  --sat_epr_types                         true
% 2.52/0.97  --sat_non_cyclic_types                  false
% 2.52/0.97  --sat_finite_models                     false
% 2.52/0.97  --sat_fm_lemmas                         false
% 2.52/0.97  --sat_fm_prep                           false
% 2.52/0.97  --sat_fm_uc_incr                        true
% 2.52/0.97  --sat_out_model                         small
% 2.52/0.97  --sat_out_clauses                       false
% 2.52/0.97  
% 2.52/0.97  ------ QBF Options
% 2.52/0.97  
% 2.52/0.97  --qbf_mode                              false
% 2.52/0.97  --qbf_elim_univ                         false
% 2.52/0.97  --qbf_dom_inst                          none
% 2.52/0.97  --qbf_dom_pre_inst                      false
% 2.52/0.97  --qbf_sk_in                             false
% 2.52/0.97  --qbf_pred_elim                         true
% 2.52/0.97  --qbf_split                             512
% 2.52/0.97  
% 2.52/0.97  ------ BMC1 Options
% 2.52/0.97  
% 2.52/0.97  --bmc1_incremental                      false
% 2.52/0.97  --bmc1_axioms                           reachable_all
% 2.52/0.97  --bmc1_min_bound                        0
% 2.52/0.97  --bmc1_max_bound                        -1
% 2.52/0.97  --bmc1_max_bound_default                -1
% 2.52/0.97  --bmc1_symbol_reachability              true
% 2.52/0.97  --bmc1_property_lemmas                  false
% 2.52/0.97  --bmc1_k_induction                      false
% 2.52/0.97  --bmc1_non_equiv_states                 false
% 2.52/0.97  --bmc1_deadlock                         false
% 2.52/0.97  --bmc1_ucm                              false
% 2.52/0.97  --bmc1_add_unsat_core                   none
% 2.52/0.97  --bmc1_unsat_core_children              false
% 2.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.97  --bmc1_out_stat                         full
% 2.52/0.97  --bmc1_ground_init                      false
% 2.52/0.97  --bmc1_pre_inst_next_state              false
% 2.52/0.97  --bmc1_pre_inst_state                   false
% 2.52/0.97  --bmc1_pre_inst_reach_state             false
% 2.52/0.97  --bmc1_out_unsat_core                   false
% 2.52/0.97  --bmc1_aig_witness_out                  false
% 2.52/0.97  --bmc1_verbose                          false
% 2.52/0.97  --bmc1_dump_clauses_tptp                false
% 2.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.97  --bmc1_dump_file                        -
% 2.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.97  --bmc1_ucm_extend_mode                  1
% 2.52/0.97  --bmc1_ucm_init_mode                    2
% 2.52/0.97  --bmc1_ucm_cone_mode                    none
% 2.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.97  --bmc1_ucm_relax_model                  4
% 2.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.97  --bmc1_ucm_layered_model                none
% 2.52/0.97  --bmc1_ucm_max_lemma_size               10
% 2.52/0.97  
% 2.52/0.97  ------ AIG Options
% 2.52/0.97  
% 2.52/0.97  --aig_mode                              false
% 2.52/0.97  
% 2.52/0.97  ------ Instantiation Options
% 2.52/0.97  
% 2.52/0.97  --instantiation_flag                    true
% 2.52/0.97  --inst_sos_flag                         false
% 2.52/0.97  --inst_sos_phase                        true
% 2.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.97  --inst_lit_sel_side                     none
% 2.52/0.97  --inst_solver_per_active                1400
% 2.52/0.97  --inst_solver_calls_frac                1.
% 2.52/0.97  --inst_passive_queue_type               priority_queues
% 2.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.97  --inst_passive_queues_freq              [25;2]
% 2.52/0.97  --inst_dismatching                      true
% 2.52/0.97  --inst_eager_unprocessed_to_passive     true
% 2.52/0.97  --inst_prop_sim_given                   true
% 2.52/0.97  --inst_prop_sim_new                     false
% 2.52/0.97  --inst_subs_new                         false
% 2.52/0.97  --inst_eq_res_simp                      false
% 2.52/0.97  --inst_subs_given                       false
% 2.52/0.97  --inst_orphan_elimination               true
% 2.52/0.97  --inst_learning_loop_flag               true
% 2.52/0.97  --inst_learning_start                   3000
% 2.52/0.97  --inst_learning_factor                  2
% 2.52/0.97  --inst_start_prop_sim_after_learn       3
% 2.52/0.97  --inst_sel_renew                        solver
% 2.52/0.97  --inst_lit_activity_flag                true
% 2.52/0.97  --inst_restr_to_given                   false
% 2.52/0.97  --inst_activity_threshold               500
% 2.52/0.97  --inst_out_proof                        true
% 2.52/0.97  
% 2.52/0.97  ------ Resolution Options
% 2.52/0.97  
% 2.52/0.97  --resolution_flag                       false
% 2.52/0.97  --res_lit_sel                           adaptive
% 2.52/0.97  --res_lit_sel_side                      none
% 2.52/0.97  --res_ordering                          kbo
% 2.52/0.97  --res_to_prop_solver                    active
% 2.52/0.97  --res_prop_simpl_new                    false
% 2.52/0.97  --res_prop_simpl_given                  true
% 2.52/0.97  --res_passive_queue_type                priority_queues
% 2.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.97  --res_passive_queues_freq               [15;5]
% 2.52/0.97  --res_forward_subs                      full
% 2.52/0.97  --res_backward_subs                     full
% 2.52/0.97  --res_forward_subs_resolution           true
% 2.52/0.97  --res_backward_subs_resolution          true
% 2.52/0.97  --res_orphan_elimination                true
% 2.52/0.97  --res_time_limit                        2.
% 2.52/0.97  --res_out_proof                         true
% 2.52/0.97  
% 2.52/0.97  ------ Superposition Options
% 2.52/0.97  
% 2.52/0.97  --superposition_flag                    true
% 2.52/0.97  --sup_passive_queue_type                priority_queues
% 2.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.97  --demod_completeness_check              fast
% 2.52/0.97  --demod_use_ground                      true
% 2.52/0.97  --sup_to_prop_solver                    passive
% 2.52/0.97  --sup_prop_simpl_new                    true
% 2.52/0.97  --sup_prop_simpl_given                  true
% 2.52/0.97  --sup_fun_splitting                     false
% 2.52/0.97  --sup_smt_interval                      50000
% 2.52/0.97  
% 2.52/0.97  ------ Superposition Simplification Setup
% 2.52/0.97  
% 2.52/0.97  --sup_indices_passive                   []
% 2.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.97  --sup_full_bw                           [BwDemod]
% 2.52/0.97  --sup_immed_triv                        [TrivRules]
% 2.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.97  --sup_immed_bw_main                     []
% 2.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.97  
% 2.52/0.97  ------ Combination Options
% 2.52/0.97  
% 2.52/0.97  --comb_res_mult                         3
% 2.52/0.97  --comb_sup_mult                         2
% 2.52/0.97  --comb_inst_mult                        10
% 2.52/0.97  
% 2.52/0.97  ------ Debug Options
% 2.52/0.97  
% 2.52/0.97  --dbg_backtrace                         false
% 2.52/0.97  --dbg_dump_prop_clauses                 false
% 2.52/0.97  --dbg_dump_prop_clauses_file            -
% 2.52/0.97  --dbg_out_stat                          false
% 2.52/0.97  
% 2.52/0.97  
% 2.52/0.97  
% 2.52/0.97  
% 2.52/0.97  ------ Proving...
% 2.52/0.97  
% 2.52/0.97  
% 2.52/0.97  % SZS status Theorem for theBenchmark.p
% 2.52/0.97  
% 2.52/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.97  
% 2.52/0.97  fof(f21,conjecture,(
% 2.52/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f22,negated_conjecture,(
% 2.52/0.97    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 2.52/0.97    inference(negated_conjecture,[],[f21])).
% 2.52/0.97  
% 2.52/0.97  fof(f34,plain,(
% 2.52/0.97    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(ennf_transformation,[],[f22])).
% 2.52/0.97  
% 2.52/0.97  fof(f45,plain,(
% 2.52/0.97    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(nnf_transformation,[],[f34])).
% 2.52/0.97  
% 2.52/0.97  fof(f46,plain,(
% 2.52/0.97    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(flattening,[],[f45])).
% 2.52/0.97  
% 2.52/0.97  fof(f48,plain,(
% 2.52/0.97    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(X1,sK4) | ~r1_xboole_0(X1,k3_subset_1(X0,sK4))) & (r1_tarski(X1,sK4) | r1_xboole_0(X1,k3_subset_1(X0,sK4))) & m1_subset_1(sK4,k1_zfmisc_1(X0)))) )),
% 2.52/0.97    introduced(choice_axiom,[])).
% 2.52/0.97  
% 2.52/0.97  fof(f47,plain,(
% 2.52/0.97    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK3,X2) | ~r1_xboole_0(sK3,k3_subset_1(sK2,X2))) & (r1_tarski(sK3,X2) | r1_xboole_0(sK3,k3_subset_1(sK2,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 2.52/0.97    introduced(choice_axiom,[])).
% 2.52/0.97  
% 2.52/0.97  fof(f49,plain,(
% 2.52/0.97    ((~r1_tarski(sK3,sK4) | ~r1_xboole_0(sK3,k3_subset_1(sK2,sK4))) & (r1_tarski(sK3,sK4) | r1_xboole_0(sK3,k3_subset_1(sK2,sK4))) & m1_subset_1(sK4,k1_zfmisc_1(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 2.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f48,f47])).
% 2.52/0.97  
% 2.52/0.97  fof(f82,plain,(
% 2.52/0.97    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 2.52/0.97    inference(cnf_transformation,[],[f49])).
% 2.52/0.97  
% 2.52/0.97  fof(f15,axiom,(
% 2.52/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f31,plain,(
% 2.52/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(ennf_transformation,[],[f15])).
% 2.52/0.97  
% 2.52/0.97  fof(f74,plain,(
% 2.52/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/0.97    inference(cnf_transformation,[],[f31])).
% 2.52/0.97  
% 2.52/0.97  fof(f5,axiom,(
% 2.52/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f56,plain,(
% 2.52/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.52/0.97    inference(cnf_transformation,[],[f5])).
% 2.52/0.97  
% 2.52/0.97  fof(f86,plain,(
% 2.52/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/0.97    inference(definition_unfolding,[],[f74,f56])).
% 2.52/0.97  
% 2.52/0.97  fof(f19,axiom,(
% 2.52/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f78,plain,(
% 2.52/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.52/0.97    inference(cnf_transformation,[],[f19])).
% 2.52/0.97  
% 2.52/0.97  fof(f87,plain,(
% 2.52/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 2.52/0.97    inference(definition_unfolding,[],[f78,f56])).
% 2.52/0.97  
% 2.52/0.97  fof(f16,axiom,(
% 2.52/0.97    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f75,plain,(
% 2.52/0.97    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.52/0.97    inference(cnf_transformation,[],[f16])).
% 2.52/0.97  
% 2.52/0.97  fof(f18,axiom,(
% 2.52/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f32,plain,(
% 2.52/0.97    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(ennf_transformation,[],[f18])).
% 2.52/0.97  
% 2.52/0.97  fof(f77,plain,(
% 2.52/0.97    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/0.97    inference(cnf_transformation,[],[f32])).
% 2.52/0.97  
% 2.52/0.97  fof(f20,axiom,(
% 2.52/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 2.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.97  
% 2.52/0.97  fof(f33,plain,(
% 2.52/0.97    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(ennf_transformation,[],[f20])).
% 2.52/0.97  
% 2.52/0.97  fof(f44,plain,(
% 2.52/0.97    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/0.97    inference(nnf_transformation,[],[f33])).
% 2.52/0.97  
% 2.52/0.97  fof(f79,plain,(
% 2.52/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/0.97    inference(cnf_transformation,[],[f44])).
% 2.52/0.97  
% 2.52/0.97  fof(f80,plain,(
% 2.52/0.97    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/0.97    inference(cnf_transformation,[],[f44])).
% 2.52/0.97  
% 2.52/0.97  fof(f84,plain,(
% 2.52/0.97    ~r1_tarski(sK3,sK4) | ~r1_xboole_0(sK3,k3_subset_1(sK2,sK4))),
% 2.52/0.97    inference(cnf_transformation,[],[f49])).
% 2.52/0.97  
% 2.52/0.97  fof(f83,plain,(
% 2.52/0.97    r1_tarski(sK3,sK4) | r1_xboole_0(sK3,k3_subset_1(sK2,sK4))),
% 2.52/0.97    inference(cnf_transformation,[],[f49])).
% 2.52/0.97  
% 2.52/0.97  fof(f81,plain,(
% 2.52/0.97    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 2.52/0.97    inference(cnf_transformation,[],[f49])).
% 2.52/0.97  
% 2.52/0.97  cnf(c_32,negated_conjecture,
% 2.52/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 2.52/0.97      inference(cnf_transformation,[],[f82]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1135,plain,
% 2.52/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.52/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_23,plain,
% 2.52/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.97      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.52/0.97      inference(cnf_transformation,[],[f86]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1143,plain,
% 2.52/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.52/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.52/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_27,plain,
% 2.52/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 2.52/0.97      inference(cnf_transformation,[],[f87]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1240,plain,
% 2.52/0.97      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 2.52/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.52/0.97      inference(demodulation,[status(thm)],[c_1143,c_27]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_4883,plain,
% 2.52/0.97      ( k6_subset_1(sK2,sK4) = k3_subset_1(sK2,sK4) ),
% 2.52/0.97      inference(superposition,[status(thm)],[c_1135,c_1240]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_24,plain,
% 2.52/0.97      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 2.52/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1142,plain,
% 2.52/0.97      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 2.52/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_5223,plain,
% 2.52/0.97      ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.52/0.97      inference(superposition,[status(thm)],[c_4883,c_1142]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_26,plain,
% 2.52/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.97      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.52/0.97      inference(cnf_transformation,[],[f77]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1140,plain,
% 2.52/0.97      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.52/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.52/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_4193,plain,
% 2.52/0.97      ( k3_subset_1(sK2,k3_subset_1(sK2,sK4)) = sK4 ),
% 2.52/0.97      inference(superposition,[status(thm)],[c_1135,c_1140]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_29,plain,
% 2.52/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.52/0.97      | ~ r1_xboole_0(X0,X2)
% 2.52/0.97      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 2.52/0.97      inference(cnf_transformation,[],[f79]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1138,plain,
% 2.52/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.52/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.52/0.97      | r1_xboole_0(X0,X2) != iProver_top
% 2.52/0.97      | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
% 2.52/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_4208,plain,
% 2.52/0.97      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | r1_xboole_0(X0,k3_subset_1(sK2,sK4)) != iProver_top
% 2.52/0.97      | r1_tarski(X0,sK4) = iProver_top ),
% 2.52/0.97      inference(superposition,[status(thm)],[c_4193,c_1138]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_4229,plain,
% 2.52/0.97      ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) != iProver_top
% 2.52/0.97      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.52/0.97      inference(instantiation,[status(thm)],[c_4208]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_28,plain,
% 2.52/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.52/0.97      | r1_xboole_0(X0,X2)
% 2.52/0.97      | ~ r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 2.52/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_1139,plain,
% 2.52/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.52/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.52/0.97      | r1_xboole_0(X0,X2) = iProver_top
% 2.52/0.97      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top ),
% 2.52/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_4207,plain,
% 2.52/0.97      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | r1_xboole_0(X0,k3_subset_1(sK2,sK4)) = iProver_top
% 2.52/0.97      | r1_tarski(X0,sK4) != iProver_top ),
% 2.52/0.97      inference(superposition,[status(thm)],[c_4193,c_1139]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_4226,plain,
% 2.52/0.97      ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 2.52/0.97      | r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) = iProver_top
% 2.52/0.97      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.52/0.97      inference(instantiation,[status(thm)],[c_4207]) ).
% 2.52/0.97  
% 2.52/0.97  cnf(c_30,negated_conjecture,
% 2.52/0.98      ( ~ r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) | ~ r1_tarski(sK3,sK4) ),
% 2.52/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_37,plain,
% 2.52/0.98      ( r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) != iProver_top
% 2.52/0.98      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_31,negated_conjecture,
% 2.52/0.98      ( r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) | r1_tarski(sK3,sK4) ),
% 2.52/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_36,plain,
% 2.52/0.98      ( r1_xboole_0(sK3,k3_subset_1(sK2,sK4)) = iProver_top
% 2.52/0.98      | r1_tarski(sK3,sK4) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_33,negated_conjecture,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 2.52/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_34,plain,
% 2.52/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.52/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(contradiction,plain,
% 2.52/0.98      ( $false ),
% 2.52/0.98      inference(minisat,
% 2.52/0.98                [status(thm)],
% 2.52/0.98                [c_5223,c_4229,c_4226,c_37,c_36,c_34]) ).
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  ------                               Statistics
% 2.52/0.98  
% 2.52/0.98  ------ General
% 2.52/0.98  
% 2.52/0.98  abstr_ref_over_cycles:                  0
% 2.52/0.98  abstr_ref_under_cycles:                 0
% 2.52/0.98  gc_basic_clause_elim:                   0
% 2.52/0.98  forced_gc_time:                         0
% 2.52/0.98  parsing_time:                           0.011
% 2.52/0.98  unif_index_cands_time:                  0.
% 2.52/0.98  unif_index_add_time:                    0.
% 2.52/0.98  orderings_time:                         0.
% 2.52/0.98  out_proof_time:                         0.01
% 2.52/0.98  total_time:                             0.146
% 2.52/0.98  num_of_symbols:                         47
% 2.52/0.98  num_of_terms:                           5602
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing
% 2.52/0.98  
% 2.52/0.98  num_of_splits:                          0
% 2.52/0.98  num_of_split_atoms:                     0
% 2.52/0.98  num_of_reused_defs:                     0
% 2.52/0.98  num_eq_ax_congr_red:                    20
% 2.52/0.98  num_of_sem_filtered_clauses:            1
% 2.52/0.98  num_of_subtypes:                        0
% 2.52/0.98  monotx_restored_types:                  0
% 2.52/0.98  sat_num_of_epr_types:                   0
% 2.52/0.98  sat_num_of_non_cyclic_types:            0
% 2.52/0.98  sat_guarded_non_collapsed_types:        0
% 2.52/0.98  num_pure_diseq_elim:                    0
% 2.52/0.98  simp_replaced_by:                       0
% 2.52/0.98  res_preprocessed:                       125
% 2.52/0.98  prep_upred:                             0
% 2.52/0.98  prep_unflattend:                        0
% 2.52/0.98  smt_new_axioms:                         0
% 2.52/0.98  pred_elim_cands:                        5
% 2.52/0.98  pred_elim:                              0
% 2.52/0.98  pred_elim_cl:                           0
% 2.52/0.98  pred_elim_cycles:                       1
% 2.52/0.98  merged_defs:                            12
% 2.52/0.98  merged_defs_ncl:                        0
% 2.52/0.98  bin_hyper_res:                          12
% 2.52/0.98  prep_cycles:                            3
% 2.52/0.98  pred_elim_time:                         0.
% 2.52/0.98  splitting_time:                         0.
% 2.52/0.98  sem_filter_time:                        0.
% 2.52/0.98  monotx_time:                            0.
% 2.52/0.98  subtype_inf_time:                       0.
% 2.52/0.98  
% 2.52/0.98  ------ Problem properties
% 2.52/0.98  
% 2.52/0.98  clauses:                                34
% 2.52/0.98  conjectures:                            4
% 2.52/0.98  epr:                                    6
% 2.52/0.98  horn:                                   29
% 2.52/0.98  ground:                                 4
% 2.52/0.98  unary:                                  9
% 2.52/0.98  binary:                                 15
% 2.52/0.98  lits:                                   71
% 2.52/0.98  lits_eq:                                10
% 2.52/0.98  fd_pure:                                0
% 2.52/0.98  fd_pseudo:                              0
% 2.52/0.98  fd_cond:                                0
% 2.52/0.98  fd_pseudo_cond:                         2
% 2.52/0.98  ac_symbols:                             0
% 2.52/0.98  
% 2.52/0.98  ------ Propositional Solver
% 2.52/0.98  
% 2.52/0.98  prop_solver_calls:                      22
% 2.52/0.98  prop_fast_solver_calls:                 672
% 2.52/0.98  smt_solver_calls:                       0
% 2.52/0.98  smt_fast_solver_calls:                  0
% 2.52/0.98  prop_num_of_clauses:                    2241
% 2.52/0.98  prop_preprocess_simplified:             6294
% 2.52/0.98  prop_fo_subsumed:                       3
% 2.52/0.98  prop_solver_time:                       0.
% 2.52/0.98  smt_solver_time:                        0.
% 2.52/0.98  smt_fast_solver_time:                   0.
% 2.52/0.98  prop_fast_solver_time:                  0.
% 2.52/0.98  prop_unsat_core_time:                   0.
% 2.52/0.98  
% 2.52/0.98  ------ QBF
% 2.52/0.98  
% 2.52/0.98  qbf_q_res:                              0
% 2.52/0.98  qbf_num_tautologies:                    0
% 2.52/0.98  qbf_prep_cycles:                        0
% 2.52/0.98  
% 2.52/0.98  ------ BMC1
% 2.52/0.98  
% 2.52/0.98  bmc1_current_bound:                     -1
% 2.52/0.98  bmc1_last_solved_bound:                 -1
% 2.52/0.98  bmc1_unsat_core_size:                   -1
% 2.52/0.98  bmc1_unsat_core_parents_size:           -1
% 2.52/0.98  bmc1_merge_next_fun:                    0
% 2.52/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation
% 2.52/0.98  
% 2.52/0.98  inst_num_of_clauses:                    597
% 2.52/0.98  inst_num_in_passive:                    111
% 2.52/0.98  inst_num_in_active:                     273
% 2.52/0.98  inst_num_in_unprocessed:                216
% 2.52/0.98  inst_num_of_loops:                      340
% 2.52/0.98  inst_num_of_learning_restarts:          0
% 2.52/0.98  inst_num_moves_active_passive:          65
% 2.52/0.98  inst_lit_activity:                      0
% 2.52/0.98  inst_lit_activity_moves:                0
% 2.52/0.98  inst_num_tautologies:                   0
% 2.52/0.98  inst_num_prop_implied:                  0
% 2.52/0.98  inst_num_existing_simplified:           0
% 2.52/0.98  inst_num_eq_res_simplified:             0
% 2.52/0.98  inst_num_child_elim:                    0
% 2.52/0.98  inst_num_of_dismatching_blockings:      144
% 2.52/0.98  inst_num_of_non_proper_insts:           459
% 2.52/0.98  inst_num_of_duplicates:                 0
% 2.52/0.98  inst_inst_num_from_inst_to_res:         0
% 2.52/0.98  inst_dismatching_checking_time:         0.
% 2.52/0.98  
% 2.52/0.98  ------ Resolution
% 2.52/0.98  
% 2.52/0.98  res_num_of_clauses:                     0
% 2.52/0.98  res_num_in_passive:                     0
% 2.52/0.98  res_num_in_active:                      0
% 2.52/0.98  res_num_of_loops:                       128
% 2.52/0.98  res_forward_subset_subsumed:            25
% 2.52/0.98  res_backward_subset_subsumed:           6
% 2.52/0.98  res_forward_subsumed:                   0
% 2.52/0.98  res_backward_subsumed:                  0
% 2.52/0.98  res_forward_subsumption_resolution:     0
% 2.52/0.98  res_backward_subsumption_resolution:    0
% 2.52/0.98  res_clause_to_clause_subsumption:       400
% 2.52/0.98  res_orphan_elimination:                 0
% 2.52/0.98  res_tautology_del:                      37
% 2.52/0.98  res_num_eq_res_simplified:              0
% 2.52/0.98  res_num_sel_changes:                    0
% 2.52/0.98  res_moves_from_active_to_pass:          0
% 2.52/0.98  
% 2.52/0.98  ------ Superposition
% 2.52/0.98  
% 2.52/0.98  sup_time_total:                         0.
% 2.52/0.98  sup_time_generating:                    0.
% 2.52/0.98  sup_time_sim_full:                      0.
% 2.52/0.98  sup_time_sim_immed:                     0.
% 2.52/0.98  
% 2.52/0.98  sup_num_of_clauses:                     145
% 2.52/0.98  sup_num_in_active:                      66
% 2.52/0.98  sup_num_in_passive:                     79
% 2.52/0.98  sup_num_of_loops:                       66
% 2.52/0.98  sup_fw_superposition:                   114
% 2.52/0.98  sup_bw_superposition:                   123
% 2.52/0.98  sup_immediate_simplified:               35
% 2.52/0.98  sup_given_eliminated:                   0
% 2.52/0.98  comparisons_done:                       0
% 2.52/0.98  comparisons_avoided:                    0
% 2.52/0.98  
% 2.52/0.98  ------ Simplifications
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  sim_fw_subset_subsumed:                 6
% 2.52/0.98  sim_bw_subset_subsumed:                 0
% 2.52/0.98  sim_fw_subsumed:                        10
% 2.52/0.98  sim_bw_subsumed:                        0
% 2.52/0.98  sim_fw_subsumption_res:                 0
% 2.52/0.98  sim_bw_subsumption_res:                 0
% 2.52/0.98  sim_tautology_del:                      6
% 2.52/0.98  sim_eq_tautology_del:                   1
% 2.52/0.98  sim_eq_res_simp:                        0
% 2.52/0.98  sim_fw_demodulated:                     5
% 2.52/0.98  sim_bw_demodulated:                     2
% 2.52/0.98  sim_light_normalised:                   14
% 2.52/0.98  sim_joinable_taut:                      0
% 2.52/0.98  sim_joinable_simp:                      0
% 2.52/0.98  sim_ac_normalised:                      0
% 2.52/0.98  sim_smt_subsumption:                    0
% 2.52/0.98  
%------------------------------------------------------------------------------
