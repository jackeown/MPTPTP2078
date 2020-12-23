%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:27 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 112 expanded)
%              Number of clauses        :   31 (  32 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  232 ( 534 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,X2)
          & r2_hidden(X1,X2)
          & r1_tarski(X0,X1)
          & v3_ordinal1(X2) )
     => ( ~ r2_hidden(X0,sK3)
        & r2_hidden(X1,sK3)
        & r1_tarski(X0,X1)
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X0,X2)
            & r2_hidden(sK2,X2)
            & r1_tarski(X0,sK2)
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK1,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK1,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_hidden(sK1,sK3)
    & r2_hidden(sK2,sK3)
    & r1_tarski(sK1,sK2)
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2)
    & v1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f27,f26,f25])).

fof(f41,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    v1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_503,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_930,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK2
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_967,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_1187,plain,
    ( r2_hidden(sK2,sK2)
    | ~ r2_hidden(sK2,sK3)
    | sK2 != sK2
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X2)
    | r2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_987,plain,
    ( ~ r1_tarski(X0,sK2)
    | r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(sK2,X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1129,plain,
    ( ~ r1_tarski(X0,sK2)
    | r2_xboole_0(X0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1131,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_xboole_0(sK2,sK3)
    | r2_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1008,plain,
    ( ~ r1_tarski(X0,sK3)
    | r2_xboole_0(X0,sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1075,plain,
    ( ~ r1_tarski(sK2,sK3)
    | r2_xboole_0(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_916,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_980,plain,
    ( ~ r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_501,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_968,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_921,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,sK3)
    | ~ v1_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_198,plain,
    ( v1_ordinal1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_199,plain,
    ( v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_9,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_168,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v1_ordinal1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_169,plain,
    ( ~ r2_xboole_0(X0,sK3)
    | r2_hidden(X0,sK3)
    | ~ v1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_171,plain,
    ( ~ r2_xboole_0(sK1,sK3)
    | r2_hidden(sK1,sK3)
    | ~ v1_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( v1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1187,c_1131,c_1075,c_980,c_968,c_921,c_199,c_171,c_10,c_11,c_12,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:24:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.80/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.80/0.97  
% 0.80/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.80/0.97  
% 0.80/0.97  ------  iProver source info
% 0.80/0.97  
% 0.80/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.80/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.80/0.97  git: non_committed_changes: false
% 0.80/0.97  git: last_make_outside_of_git: false
% 0.80/0.97  
% 0.80/0.97  ------ 
% 0.80/0.97  
% 0.80/0.97  ------ Input Options
% 0.80/0.97  
% 0.80/0.97  --out_options                           all
% 0.80/0.97  --tptp_safe_out                         true
% 0.80/0.97  --problem_path                          ""
% 0.80/0.97  --include_path                          ""
% 0.80/0.97  --clausifier                            res/vclausify_rel
% 0.80/0.97  --clausifier_options                    --mode clausify
% 0.80/0.97  --stdin                                 false
% 0.80/0.97  --stats_out                             all
% 0.80/0.97  
% 0.80/0.97  ------ General Options
% 0.80/0.97  
% 0.80/0.97  --fof                                   false
% 0.80/0.97  --time_out_real                         305.
% 0.80/0.97  --time_out_virtual                      -1.
% 0.80/0.97  --symbol_type_check                     false
% 0.80/0.97  --clausify_out                          false
% 0.80/0.97  --sig_cnt_out                           false
% 0.80/0.97  --trig_cnt_out                          false
% 0.80/0.97  --trig_cnt_out_tolerance                1.
% 0.80/0.97  --trig_cnt_out_sk_spl                   false
% 0.80/0.97  --abstr_cl_out                          false
% 0.80/0.97  
% 0.80/0.97  ------ Global Options
% 0.80/0.97  
% 0.80/0.97  --schedule                              default
% 0.80/0.97  --add_important_lit                     false
% 0.80/0.97  --prop_solver_per_cl                    1000
% 0.80/0.97  --min_unsat_core                        false
% 0.80/0.97  --soft_assumptions                      false
% 0.80/0.97  --soft_lemma_size                       3
% 0.80/0.97  --prop_impl_unit_size                   0
% 0.80/0.97  --prop_impl_unit                        []
% 0.80/0.97  --share_sel_clauses                     true
% 0.80/0.97  --reset_solvers                         false
% 0.80/0.97  --bc_imp_inh                            [conj_cone]
% 0.80/0.97  --conj_cone_tolerance                   3.
% 0.80/0.97  --extra_neg_conj                        none
% 0.80/0.97  --large_theory_mode                     true
% 0.80/0.97  --prolific_symb_bound                   200
% 0.80/0.97  --lt_threshold                          2000
% 0.80/0.97  --clause_weak_htbl                      true
% 0.80/0.97  --gc_record_bc_elim                     false
% 0.80/0.97  
% 0.80/0.97  ------ Preprocessing Options
% 0.80/0.97  
% 0.80/0.97  --preprocessing_flag                    true
% 0.80/0.97  --time_out_prep_mult                    0.1
% 0.80/0.97  --splitting_mode                        input
% 0.80/0.97  --splitting_grd                         true
% 0.80/0.97  --splitting_cvd                         false
% 0.80/0.97  --splitting_cvd_svl                     false
% 0.80/0.97  --splitting_nvd                         32
% 0.80/0.97  --sub_typing                            true
% 0.80/0.97  --prep_gs_sim                           true
% 0.80/0.97  --prep_unflatten                        true
% 0.80/0.97  --prep_res_sim                          true
% 0.80/0.97  --prep_upred                            true
% 0.80/0.97  --prep_sem_filter                       exhaustive
% 0.80/0.97  --prep_sem_filter_out                   false
% 0.80/0.97  --pred_elim                             true
% 0.80/0.97  --res_sim_input                         true
% 0.80/0.97  --eq_ax_congr_red                       true
% 0.80/0.97  --pure_diseq_elim                       true
% 0.80/0.97  --brand_transform                       false
% 0.80/0.97  --non_eq_to_eq                          false
% 0.80/0.97  --prep_def_merge                        true
% 0.80/0.97  --prep_def_merge_prop_impl              false
% 0.80/0.97  --prep_def_merge_mbd                    true
% 0.80/0.97  --prep_def_merge_tr_red                 false
% 0.80/0.97  --prep_def_merge_tr_cl                  false
% 0.80/0.97  --smt_preprocessing                     true
% 0.80/0.97  --smt_ac_axioms                         fast
% 0.80/0.97  --preprocessed_out                      false
% 0.80/0.97  --preprocessed_stats                    false
% 0.80/0.97  
% 0.80/0.97  ------ Abstraction refinement Options
% 0.80/0.97  
% 0.80/0.97  --abstr_ref                             []
% 0.80/0.97  --abstr_ref_prep                        false
% 0.80/0.97  --abstr_ref_until_sat                   false
% 0.80/0.97  --abstr_ref_sig_restrict                funpre
% 0.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.80/0.97  --abstr_ref_under                       []
% 0.80/0.97  
% 0.80/0.97  ------ SAT Options
% 0.80/0.97  
% 0.80/0.97  --sat_mode                              false
% 0.80/0.97  --sat_fm_restart_options                ""
% 0.80/0.97  --sat_gr_def                            false
% 0.80/0.97  --sat_epr_types                         true
% 0.80/0.97  --sat_non_cyclic_types                  false
% 0.80/0.97  --sat_finite_models                     false
% 0.80/0.97  --sat_fm_lemmas                         false
% 0.80/0.97  --sat_fm_prep                           false
% 0.80/0.97  --sat_fm_uc_incr                        true
% 0.80/0.97  --sat_out_model                         small
% 0.80/0.97  --sat_out_clauses                       false
% 0.80/0.97  
% 0.80/0.97  ------ QBF Options
% 0.80/0.97  
% 0.80/0.97  --qbf_mode                              false
% 0.80/0.97  --qbf_elim_univ                         false
% 0.80/0.97  --qbf_dom_inst                          none
% 0.80/0.97  --qbf_dom_pre_inst                      false
% 0.80/0.97  --qbf_sk_in                             false
% 0.80/0.97  --qbf_pred_elim                         true
% 0.80/0.97  --qbf_split                             512
% 0.80/0.97  
% 0.80/0.97  ------ BMC1 Options
% 0.80/0.97  
% 0.80/0.97  --bmc1_incremental                      false
% 0.80/0.97  --bmc1_axioms                           reachable_all
% 0.80/0.97  --bmc1_min_bound                        0
% 0.80/0.97  --bmc1_max_bound                        -1
% 0.80/0.97  --bmc1_max_bound_default                -1
% 0.80/0.97  --bmc1_symbol_reachability              true
% 0.80/0.97  --bmc1_property_lemmas                  false
% 0.80/0.97  --bmc1_k_induction                      false
% 0.80/0.97  --bmc1_non_equiv_states                 false
% 0.80/0.97  --bmc1_deadlock                         false
% 0.80/0.97  --bmc1_ucm                              false
% 0.80/0.97  --bmc1_add_unsat_core                   none
% 0.80/0.97  --bmc1_unsat_core_children              false
% 0.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.80/0.97  --bmc1_out_stat                         full
% 0.80/0.97  --bmc1_ground_init                      false
% 0.80/0.97  --bmc1_pre_inst_next_state              false
% 0.80/0.97  --bmc1_pre_inst_state                   false
% 0.80/0.97  --bmc1_pre_inst_reach_state             false
% 0.80/0.97  --bmc1_out_unsat_core                   false
% 0.80/0.97  --bmc1_aig_witness_out                  false
% 0.80/0.97  --bmc1_verbose                          false
% 0.80/0.97  --bmc1_dump_clauses_tptp                false
% 0.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.80/0.97  --bmc1_dump_file                        -
% 0.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.80/0.97  --bmc1_ucm_extend_mode                  1
% 0.80/0.97  --bmc1_ucm_init_mode                    2
% 0.80/0.97  --bmc1_ucm_cone_mode                    none
% 0.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.80/0.97  --bmc1_ucm_relax_model                  4
% 0.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.80/0.97  --bmc1_ucm_layered_model                none
% 0.80/0.97  --bmc1_ucm_max_lemma_size               10
% 0.80/0.97  
% 0.80/0.97  ------ AIG Options
% 0.80/0.97  
% 0.80/0.97  --aig_mode                              false
% 0.80/0.97  
% 0.80/0.97  ------ Instantiation Options
% 0.80/0.97  
% 0.80/0.97  --instantiation_flag                    true
% 0.80/0.97  --inst_sos_flag                         false
% 0.80/0.97  --inst_sos_phase                        true
% 0.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.80/0.97  --inst_lit_sel_side                     num_symb
% 0.80/0.97  --inst_solver_per_active                1400
% 0.80/0.97  --inst_solver_calls_frac                1.
% 0.80/0.97  --inst_passive_queue_type               priority_queues
% 0.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.80/0.97  --inst_passive_queues_freq              [25;2]
% 0.80/0.97  --inst_dismatching                      true
% 0.80/0.97  --inst_eager_unprocessed_to_passive     true
% 0.80/0.97  --inst_prop_sim_given                   true
% 0.80/0.97  --inst_prop_sim_new                     false
% 0.80/0.97  --inst_subs_new                         false
% 0.80/0.97  --inst_eq_res_simp                      false
% 0.80/0.97  --inst_subs_given                       false
% 0.80/0.97  --inst_orphan_elimination               true
% 0.80/0.97  --inst_learning_loop_flag               true
% 0.80/0.97  --inst_learning_start                   3000
% 0.80/0.97  --inst_learning_factor                  2
% 0.80/0.97  --inst_start_prop_sim_after_learn       3
% 0.80/0.97  --inst_sel_renew                        solver
% 0.80/0.97  --inst_lit_activity_flag                true
% 0.80/0.97  --inst_restr_to_given                   false
% 0.80/0.97  --inst_activity_threshold               500
% 0.80/0.97  --inst_out_proof                        true
% 0.80/0.97  
% 0.80/0.97  ------ Resolution Options
% 0.80/0.97  
% 0.80/0.97  --resolution_flag                       true
% 0.80/0.97  --res_lit_sel                           adaptive
% 0.80/0.97  --res_lit_sel_side                      none
% 0.80/0.97  --res_ordering                          kbo
% 0.80/0.97  --res_to_prop_solver                    active
% 0.80/0.97  --res_prop_simpl_new                    false
% 0.80/0.97  --res_prop_simpl_given                  true
% 0.80/0.97  --res_passive_queue_type                priority_queues
% 0.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.80/0.97  --res_passive_queues_freq               [15;5]
% 0.80/0.97  --res_forward_subs                      full
% 0.80/0.97  --res_backward_subs                     full
% 0.80/0.97  --res_forward_subs_resolution           true
% 0.80/0.97  --res_backward_subs_resolution          true
% 0.80/0.97  --res_orphan_elimination                true
% 0.80/0.97  --res_time_limit                        2.
% 0.80/0.97  --res_out_proof                         true
% 0.80/0.97  
% 0.80/0.97  ------ Superposition Options
% 0.80/0.97  
% 0.80/0.97  --superposition_flag                    true
% 0.80/0.97  --sup_passive_queue_type                priority_queues
% 0.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.80/0.97  --demod_completeness_check              fast
% 0.80/0.97  --demod_use_ground                      true
% 0.80/0.97  --sup_to_prop_solver                    passive
% 0.80/0.97  --sup_prop_simpl_new                    true
% 0.80/0.97  --sup_prop_simpl_given                  true
% 0.80/0.97  --sup_fun_splitting                     false
% 0.80/0.97  --sup_smt_interval                      50000
% 0.80/0.97  
% 0.80/0.97  ------ Superposition Simplification Setup
% 0.80/0.97  
% 0.80/0.97  --sup_indices_passive                   []
% 0.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/0.97  --sup_full_bw                           [BwDemod]
% 0.80/0.97  --sup_immed_triv                        [TrivRules]
% 0.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/0.97  --sup_immed_bw_main                     []
% 0.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/0.97  
% 0.80/0.97  ------ Combination Options
% 0.80/0.97  
% 0.80/0.97  --comb_res_mult                         3
% 0.80/0.97  --comb_sup_mult                         2
% 0.80/0.97  --comb_inst_mult                        10
% 0.80/0.97  
% 0.80/0.97  ------ Debug Options
% 0.80/0.97  
% 0.80/0.97  --dbg_backtrace                         false
% 0.80/0.97  --dbg_dump_prop_clauses                 false
% 0.80/0.97  --dbg_dump_prop_clauses_file            -
% 0.80/0.97  --dbg_out_stat                          false
% 0.80/0.97  ------ Parsing...
% 0.80/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.80/0.97  
% 0.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 0.80/0.97  
% 0.80/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.80/0.97  
% 0.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.80/0.97  ------ Proving...
% 0.80/0.97  ------ Problem Properties 
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  clauses                                 16
% 0.80/0.97  conjectures                             4
% 0.80/0.97  EPR                                     14
% 0.80/0.97  Horn                                    14
% 0.80/0.97  unary                                   7
% 0.80/0.97  binary                                  4
% 0.80/0.97  lits                                    30
% 0.80/0.97  lits eq                                 1
% 0.80/0.97  fd_pure                                 0
% 0.80/0.97  fd_pseudo                               0
% 0.80/0.97  fd_cond                                 0
% 0.80/0.97  fd_pseudo_cond                          1
% 0.80/0.97  AC symbols                              0
% 0.80/0.97  
% 0.80/0.97  ------ Schedule dynamic 5 is on 
% 0.80/0.97  
% 0.80/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  ------ 
% 0.80/0.97  Current options:
% 0.80/0.97  ------ 
% 0.80/0.97  
% 0.80/0.97  ------ Input Options
% 0.80/0.97  
% 0.80/0.97  --out_options                           all
% 0.80/0.97  --tptp_safe_out                         true
% 0.80/0.97  --problem_path                          ""
% 0.80/0.97  --include_path                          ""
% 0.80/0.97  --clausifier                            res/vclausify_rel
% 0.80/0.97  --clausifier_options                    --mode clausify
% 0.80/0.97  --stdin                                 false
% 0.80/0.97  --stats_out                             all
% 0.80/0.97  
% 0.80/0.97  ------ General Options
% 0.80/0.97  
% 0.80/0.97  --fof                                   false
% 0.80/0.97  --time_out_real                         305.
% 0.80/0.97  --time_out_virtual                      -1.
% 0.80/0.97  --symbol_type_check                     false
% 0.80/0.97  --clausify_out                          false
% 0.80/0.97  --sig_cnt_out                           false
% 0.80/0.97  --trig_cnt_out                          false
% 0.80/0.97  --trig_cnt_out_tolerance                1.
% 0.80/0.97  --trig_cnt_out_sk_spl                   false
% 0.80/0.97  --abstr_cl_out                          false
% 0.80/0.97  
% 0.80/0.97  ------ Global Options
% 0.80/0.97  
% 0.80/0.97  --schedule                              default
% 0.80/0.97  --add_important_lit                     false
% 0.80/0.97  --prop_solver_per_cl                    1000
% 0.80/0.97  --min_unsat_core                        false
% 0.80/0.97  --soft_assumptions                      false
% 0.80/0.97  --soft_lemma_size                       3
% 0.80/0.97  --prop_impl_unit_size                   0
% 0.80/0.97  --prop_impl_unit                        []
% 0.80/0.97  --share_sel_clauses                     true
% 0.80/0.97  --reset_solvers                         false
% 0.80/0.97  --bc_imp_inh                            [conj_cone]
% 0.80/0.97  --conj_cone_tolerance                   3.
% 0.80/0.97  --extra_neg_conj                        none
% 0.80/0.97  --large_theory_mode                     true
% 0.80/0.97  --prolific_symb_bound                   200
% 0.80/0.97  --lt_threshold                          2000
% 0.80/0.97  --clause_weak_htbl                      true
% 0.80/0.97  --gc_record_bc_elim                     false
% 0.80/0.97  
% 0.80/0.97  ------ Preprocessing Options
% 0.80/0.97  
% 0.80/0.97  --preprocessing_flag                    true
% 0.80/0.97  --time_out_prep_mult                    0.1
% 0.80/0.97  --splitting_mode                        input
% 0.80/0.97  --splitting_grd                         true
% 0.80/0.97  --splitting_cvd                         false
% 0.80/0.97  --splitting_cvd_svl                     false
% 0.80/0.97  --splitting_nvd                         32
% 0.80/0.97  --sub_typing                            true
% 0.80/0.97  --prep_gs_sim                           true
% 0.80/0.97  --prep_unflatten                        true
% 0.80/0.97  --prep_res_sim                          true
% 0.80/0.97  --prep_upred                            true
% 0.80/0.97  --prep_sem_filter                       exhaustive
% 0.80/0.97  --prep_sem_filter_out                   false
% 0.80/0.97  --pred_elim                             true
% 0.80/0.97  --res_sim_input                         true
% 0.80/0.97  --eq_ax_congr_red                       true
% 0.80/0.97  --pure_diseq_elim                       true
% 0.80/0.97  --brand_transform                       false
% 0.80/0.97  --non_eq_to_eq                          false
% 0.80/0.97  --prep_def_merge                        true
% 0.80/0.97  --prep_def_merge_prop_impl              false
% 0.80/0.97  --prep_def_merge_mbd                    true
% 0.80/0.97  --prep_def_merge_tr_red                 false
% 0.80/0.97  --prep_def_merge_tr_cl                  false
% 0.80/0.97  --smt_preprocessing                     true
% 0.80/0.97  --smt_ac_axioms                         fast
% 0.80/0.97  --preprocessed_out                      false
% 0.80/0.97  --preprocessed_stats                    false
% 0.80/0.97  
% 0.80/0.97  ------ Abstraction refinement Options
% 0.80/0.97  
% 0.80/0.97  --abstr_ref                             []
% 0.80/0.97  --abstr_ref_prep                        false
% 0.80/0.97  --abstr_ref_until_sat                   false
% 0.80/0.97  --abstr_ref_sig_restrict                funpre
% 0.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.80/0.97  --abstr_ref_under                       []
% 0.80/0.97  
% 0.80/0.97  ------ SAT Options
% 0.80/0.97  
% 0.80/0.97  --sat_mode                              false
% 0.80/0.97  --sat_fm_restart_options                ""
% 0.80/0.97  --sat_gr_def                            false
% 0.80/0.97  --sat_epr_types                         true
% 0.80/0.97  --sat_non_cyclic_types                  false
% 0.80/0.97  --sat_finite_models                     false
% 0.80/0.97  --sat_fm_lemmas                         false
% 0.80/0.97  --sat_fm_prep                           false
% 0.80/0.97  --sat_fm_uc_incr                        true
% 0.80/0.97  --sat_out_model                         small
% 0.80/0.97  --sat_out_clauses                       false
% 0.80/0.97  
% 0.80/0.97  ------ QBF Options
% 0.80/0.97  
% 0.80/0.97  --qbf_mode                              false
% 0.80/0.97  --qbf_elim_univ                         false
% 0.80/0.97  --qbf_dom_inst                          none
% 0.80/0.97  --qbf_dom_pre_inst                      false
% 0.80/0.97  --qbf_sk_in                             false
% 0.80/0.97  --qbf_pred_elim                         true
% 0.80/0.97  --qbf_split                             512
% 0.80/0.97  
% 0.80/0.97  ------ BMC1 Options
% 0.80/0.97  
% 0.80/0.97  --bmc1_incremental                      false
% 0.80/0.97  --bmc1_axioms                           reachable_all
% 0.80/0.97  --bmc1_min_bound                        0
% 0.80/0.97  --bmc1_max_bound                        -1
% 0.80/0.97  --bmc1_max_bound_default                -1
% 0.80/0.97  --bmc1_symbol_reachability              true
% 0.80/0.97  --bmc1_property_lemmas                  false
% 0.80/0.97  --bmc1_k_induction                      false
% 0.80/0.97  --bmc1_non_equiv_states                 false
% 0.80/0.97  --bmc1_deadlock                         false
% 0.80/0.97  --bmc1_ucm                              false
% 0.80/0.97  --bmc1_add_unsat_core                   none
% 0.80/0.97  --bmc1_unsat_core_children              false
% 0.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.80/0.97  --bmc1_out_stat                         full
% 0.80/0.97  --bmc1_ground_init                      false
% 0.80/0.97  --bmc1_pre_inst_next_state              false
% 0.80/0.97  --bmc1_pre_inst_state                   false
% 0.80/0.97  --bmc1_pre_inst_reach_state             false
% 0.80/0.97  --bmc1_out_unsat_core                   false
% 0.80/0.97  --bmc1_aig_witness_out                  false
% 0.80/0.97  --bmc1_verbose                          false
% 0.80/0.97  --bmc1_dump_clauses_tptp                false
% 0.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.80/0.97  --bmc1_dump_file                        -
% 0.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.80/0.97  --bmc1_ucm_extend_mode                  1
% 0.80/0.97  --bmc1_ucm_init_mode                    2
% 0.80/0.97  --bmc1_ucm_cone_mode                    none
% 0.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.80/0.97  --bmc1_ucm_relax_model                  4
% 0.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.80/0.97  --bmc1_ucm_layered_model                none
% 0.80/0.97  --bmc1_ucm_max_lemma_size               10
% 0.80/0.97  
% 0.80/0.97  ------ AIG Options
% 0.80/0.97  
% 0.80/0.97  --aig_mode                              false
% 0.80/0.97  
% 0.80/0.97  ------ Instantiation Options
% 0.80/0.97  
% 0.80/0.97  --instantiation_flag                    true
% 0.80/0.97  --inst_sos_flag                         false
% 0.80/0.97  --inst_sos_phase                        true
% 0.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.80/0.97  --inst_lit_sel_side                     none
% 0.80/0.97  --inst_solver_per_active                1400
% 0.80/0.97  --inst_solver_calls_frac                1.
% 0.80/0.97  --inst_passive_queue_type               priority_queues
% 0.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.80/0.97  --inst_passive_queues_freq              [25;2]
% 0.80/0.97  --inst_dismatching                      true
% 0.80/0.97  --inst_eager_unprocessed_to_passive     true
% 0.80/0.97  --inst_prop_sim_given                   true
% 0.80/0.97  --inst_prop_sim_new                     false
% 0.80/0.97  --inst_subs_new                         false
% 0.80/0.97  --inst_eq_res_simp                      false
% 0.80/0.97  --inst_subs_given                       false
% 0.80/0.97  --inst_orphan_elimination               true
% 0.80/0.97  --inst_learning_loop_flag               true
% 0.80/0.97  --inst_learning_start                   3000
% 0.80/0.97  --inst_learning_factor                  2
% 0.80/0.97  --inst_start_prop_sim_after_learn       3
% 0.80/0.97  --inst_sel_renew                        solver
% 0.80/0.97  --inst_lit_activity_flag                true
% 0.80/0.97  --inst_restr_to_given                   false
% 0.80/0.97  --inst_activity_threshold               500
% 0.80/0.97  --inst_out_proof                        true
% 0.80/0.97  
% 0.80/0.97  ------ Resolution Options
% 0.80/0.97  
% 0.80/0.97  --resolution_flag                       false
% 0.80/0.97  --res_lit_sel                           adaptive
% 0.80/0.97  --res_lit_sel_side                      none
% 0.80/0.97  --res_ordering                          kbo
% 0.80/0.97  --res_to_prop_solver                    active
% 0.80/0.97  --res_prop_simpl_new                    false
% 0.80/0.97  --res_prop_simpl_given                  true
% 0.80/0.97  --res_passive_queue_type                priority_queues
% 0.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.80/0.97  --res_passive_queues_freq               [15;5]
% 0.80/0.97  --res_forward_subs                      full
% 0.80/0.97  --res_backward_subs                     full
% 0.80/0.97  --res_forward_subs_resolution           true
% 0.80/0.97  --res_backward_subs_resolution          true
% 0.80/0.97  --res_orphan_elimination                true
% 0.80/0.97  --res_time_limit                        2.
% 0.80/0.97  --res_out_proof                         true
% 0.80/0.97  
% 0.80/0.97  ------ Superposition Options
% 0.80/0.97  
% 0.80/0.97  --superposition_flag                    true
% 0.80/0.97  --sup_passive_queue_type                priority_queues
% 0.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.80/0.97  --demod_completeness_check              fast
% 0.80/0.97  --demod_use_ground                      true
% 0.80/0.97  --sup_to_prop_solver                    passive
% 0.80/0.97  --sup_prop_simpl_new                    true
% 0.80/0.97  --sup_prop_simpl_given                  true
% 0.80/0.97  --sup_fun_splitting                     false
% 0.80/0.97  --sup_smt_interval                      50000
% 0.80/0.97  
% 0.80/0.97  ------ Superposition Simplification Setup
% 0.80/0.97  
% 0.80/0.97  --sup_indices_passive                   []
% 0.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/0.97  --sup_full_bw                           [BwDemod]
% 0.80/0.97  --sup_immed_triv                        [TrivRules]
% 0.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/0.97  --sup_immed_bw_main                     []
% 0.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.80/0.97  
% 0.80/0.97  ------ Combination Options
% 0.80/0.97  
% 0.80/0.97  --comb_res_mult                         3
% 0.80/0.97  --comb_sup_mult                         2
% 0.80/0.97  --comb_inst_mult                        10
% 0.80/0.97  
% 0.80/0.97  ------ Debug Options
% 0.80/0.97  
% 0.80/0.97  --dbg_backtrace                         false
% 0.80/0.97  --dbg_dump_prop_clauses                 false
% 0.80/0.97  --dbg_dump_prop_clauses_file            -
% 0.80/0.97  --dbg_out_stat                          false
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  ------ Proving...
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  % SZS status Theorem for theBenchmark.p
% 0.80/0.97  
% 0.80/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.80/0.97  
% 0.80/0.97  fof(f3,axiom,(
% 0.80/0.97    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f11,plain,(
% 0.80/0.97    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.80/0.97    inference(ennf_transformation,[],[f3])).
% 0.80/0.97  
% 0.80/0.97  fof(f12,plain,(
% 0.80/0.97    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.80/0.97    inference(flattening,[],[f11])).
% 0.80/0.97  
% 0.80/0.97  fof(f33,plain,(
% 0.80/0.97    ( ! [X2,X0,X1] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.80/0.97    inference(cnf_transformation,[],[f12])).
% 0.80/0.97  
% 0.80/0.97  fof(f2,axiom,(
% 0.80/0.97    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f19,plain,(
% 0.80/0.97    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.80/0.97    inference(nnf_transformation,[],[f2])).
% 0.80/0.97  
% 0.80/0.97  fof(f20,plain,(
% 0.80/0.97    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.80/0.97    inference(flattening,[],[f19])).
% 0.80/0.97  
% 0.80/0.97  fof(f32,plain,(
% 0.80/0.97    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.80/0.97    inference(cnf_transformation,[],[f20])).
% 0.80/0.97  
% 0.80/0.97  fof(f1,axiom,(
% 0.80/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f10,plain,(
% 0.80/0.97    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.80/0.97    inference(ennf_transformation,[],[f1])).
% 0.80/0.97  
% 0.80/0.97  fof(f29,plain,(
% 0.80/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.80/0.97    inference(cnf_transformation,[],[f10])).
% 0.80/0.97  
% 0.80/0.97  fof(f5,axiom,(
% 0.80/0.97    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f14,plain,(
% 0.80/0.97    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.80/0.97    inference(ennf_transformation,[],[f5])).
% 0.80/0.97  
% 0.80/0.97  fof(f21,plain,(
% 0.80/0.97    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.80/0.97    inference(nnf_transformation,[],[f14])).
% 0.80/0.97  
% 0.80/0.97  fof(f22,plain,(
% 0.80/0.97    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.80/0.97    inference(rectify,[],[f21])).
% 0.80/0.97  
% 0.80/0.97  fof(f23,plain,(
% 0.80/0.97    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0)))),
% 0.80/0.97    introduced(choice_axiom,[])).
% 0.80/0.97  
% 0.80/0.97  fof(f24,plain,(
% 0.80/0.97    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 0.80/0.97  
% 0.80/0.97  fof(f35,plain,(
% 0.80/0.97    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.80/0.97    inference(cnf_transformation,[],[f24])).
% 0.80/0.97  
% 0.80/0.97  fof(f4,axiom,(
% 0.80/0.97    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f9,plain,(
% 0.80/0.97    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.80/0.97    inference(pure_predicate_removal,[],[f4])).
% 0.80/0.97  
% 0.80/0.97  fof(f13,plain,(
% 0.80/0.97    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.80/0.97    inference(ennf_transformation,[],[f9])).
% 0.80/0.97  
% 0.80/0.97  fof(f34,plain,(
% 0.80/0.97    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.80/0.97    inference(cnf_transformation,[],[f13])).
% 0.80/0.97  
% 0.80/0.97  fof(f7,conjecture,(
% 0.80/0.97    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f8,negated_conjecture,(
% 0.80/0.97    ~! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.80/0.97    inference(negated_conjecture,[],[f7])).
% 0.80/0.97  
% 0.80/0.97  fof(f17,plain,(
% 0.80/0.97    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X0,X2) & (r2_hidden(X1,X2) & r1_tarski(X0,X1))) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0))),
% 0.80/0.97    inference(ennf_transformation,[],[f8])).
% 0.80/0.97  
% 0.80/0.97  fof(f18,plain,(
% 0.80/0.97    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0))),
% 0.80/0.97    inference(flattening,[],[f17])).
% 0.80/0.97  
% 0.80/0.97  fof(f27,plain,(
% 0.80/0.97    ( ! [X0,X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) => (~r2_hidden(X0,sK3) & r2_hidden(X1,sK3) & r1_tarski(X0,X1) & v3_ordinal1(sK3))) )),
% 0.80/0.97    introduced(choice_axiom,[])).
% 0.80/0.97  
% 0.80/0.97  fof(f26,plain,(
% 0.80/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) => (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(sK2,X2) & r1_tarski(X0,sK2) & v3_ordinal1(X2)) & v3_ordinal1(sK2))) )),
% 0.80/0.97    introduced(choice_axiom,[])).
% 0.80/0.97  
% 0.80/0.97  fof(f25,plain,(
% 0.80/0.97    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0)) => (? [X1] : (? [X2] : (~r2_hidden(sK1,X2) & r2_hidden(X1,X2) & r1_tarski(sK1,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(sK1))),
% 0.80/0.97    introduced(choice_axiom,[])).
% 0.80/0.97  
% 0.80/0.97  fof(f28,plain,(
% 0.80/0.97    ((~r2_hidden(sK1,sK3) & r2_hidden(sK2,sK3) & r1_tarski(sK1,sK2) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)) & v1_ordinal1(sK1)),
% 0.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f27,f26,f25])).
% 0.80/0.97  
% 0.80/0.97  fof(f41,plain,(
% 0.80/0.97    v3_ordinal1(sK3)),
% 0.80/0.97    inference(cnf_transformation,[],[f28])).
% 0.80/0.97  
% 0.80/0.97  fof(f6,axiom,(
% 0.80/0.97    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.80/0.97  
% 0.80/0.97  fof(f15,plain,(
% 0.80/0.97    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.80/0.97    inference(ennf_transformation,[],[f6])).
% 0.80/0.97  
% 0.80/0.97  fof(f16,plain,(
% 0.80/0.97    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.80/0.97    inference(flattening,[],[f15])).
% 0.80/0.97  
% 0.80/0.97  fof(f38,plain,(
% 0.80/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.80/0.97    inference(cnf_transformation,[],[f16])).
% 0.80/0.97  
% 0.80/0.97  fof(f44,plain,(
% 0.80/0.97    ~r2_hidden(sK1,sK3)),
% 0.80/0.97    inference(cnf_transformation,[],[f28])).
% 0.80/0.97  
% 0.80/0.97  fof(f43,plain,(
% 0.80/0.97    r2_hidden(sK2,sK3)),
% 0.80/0.97    inference(cnf_transformation,[],[f28])).
% 0.80/0.97  
% 0.80/0.97  fof(f42,plain,(
% 0.80/0.97    r1_tarski(sK1,sK2)),
% 0.80/0.97    inference(cnf_transformation,[],[f28])).
% 0.80/0.97  
% 0.80/0.97  fof(f39,plain,(
% 0.80/0.97    v1_ordinal1(sK1)),
% 0.80/0.97    inference(cnf_transformation,[],[f28])).
% 0.80/0.97  
% 0.80/0.97  cnf(c_503,plain,
% 0.80/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.80/0.97      theory(equality) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_930,plain,
% 0.80/0.97      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2,sK3) | X0 != sK2 | X1 != sK3 ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_503]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_967,plain,
% 0.80/0.97      ( r2_hidden(sK2,X0)
% 0.80/0.97      | ~ r2_hidden(sK2,sK3)
% 0.80/0.97      | X0 != sK3
% 0.80/0.97      | sK2 != sK2 ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_930]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_1187,plain,
% 0.80/0.97      ( r2_hidden(sK2,sK2)
% 0.80/0.97      | ~ r2_hidden(sK2,sK3)
% 0.80/0.97      | sK2 != sK2
% 0.80/0.97      | sK2 != sK3 ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_967]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_4,plain,
% 0.80/0.97      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2) ),
% 0.80/0.97      inference(cnf_transformation,[],[f33]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_987,plain,
% 0.80/0.97      ( ~ r1_tarski(X0,sK2)
% 0.80/0.97      | r2_xboole_0(X0,X1)
% 0.80/0.97      | ~ r2_xboole_0(sK2,X1) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_1129,plain,
% 0.80/0.97      ( ~ r1_tarski(X0,sK2)
% 0.80/0.97      | r2_xboole_0(X0,sK3)
% 0.80/0.97      | ~ r2_xboole_0(sK2,sK3) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_987]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_1131,plain,
% 0.80/0.97      ( ~ r1_tarski(sK1,sK2)
% 0.80/0.97      | ~ r2_xboole_0(sK2,sK3)
% 0.80/0.97      | r2_xboole_0(sK1,sK3) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_1129]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_1,plain,
% 0.80/0.97      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X0 = X1 ),
% 0.80/0.97      inference(cnf_transformation,[],[f32]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_1008,plain,
% 0.80/0.97      ( ~ r1_tarski(X0,sK3) | r2_xboole_0(X0,sK3) | X0 = sK3 ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_1075,plain,
% 0.80/0.97      ( ~ r1_tarski(sK2,sK3) | r2_xboole_0(sK2,sK3) | sK2 = sK3 ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_1008]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_0,plain,
% 0.80/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 0.80/0.97      inference(cnf_transformation,[],[f29]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_916,plain,
% 0.80/0.97      ( ~ r2_hidden(X0,sK2) | ~ r2_hidden(sK2,X0) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_980,plain,
% 0.80/0.97      ( ~ r2_hidden(sK2,sK2) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_916]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_501,plain,( X0 = X0 ),theory(equality) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_968,plain,
% 0.80/0.97      ( sK2 = sK2 ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_501]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_8,plain,
% 0.80/0.97      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 0.80/0.97      inference(cnf_transformation,[],[f35]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_921,plain,
% 0.80/0.97      ( r1_tarski(sK2,sK3) | ~ r2_hidden(sK2,sK3) | ~ v1_ordinal1(sK3) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_5,plain,
% 0.80/0.97      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 0.80/0.97      inference(cnf_transformation,[],[f34]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_13,negated_conjecture,
% 0.80/0.97      ( v3_ordinal1(sK3) ),
% 0.80/0.97      inference(cnf_transformation,[],[f41]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_198,plain,
% 0.80/0.97      ( v1_ordinal1(X0) | sK3 != X0 ),
% 0.80/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_199,plain,
% 0.80/0.97      ( v1_ordinal1(sK3) ),
% 0.80/0.97      inference(unflattening,[status(thm)],[c_198]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_9,plain,
% 0.80/0.97      ( ~ r2_xboole_0(X0,X1)
% 0.80/0.97      | r2_hidden(X0,X1)
% 0.80/0.97      | ~ v3_ordinal1(X1)
% 0.80/0.97      | ~ v1_ordinal1(X0) ),
% 0.80/0.97      inference(cnf_transformation,[],[f38]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_168,plain,
% 0.80/0.97      ( ~ r2_xboole_0(X0,X1)
% 0.80/0.97      | r2_hidden(X0,X1)
% 0.80/0.97      | ~ v1_ordinal1(X0)
% 0.80/0.97      | sK3 != X1 ),
% 0.80/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_169,plain,
% 0.80/0.97      ( ~ r2_xboole_0(X0,sK3) | r2_hidden(X0,sK3) | ~ v1_ordinal1(X0) ),
% 0.80/0.97      inference(unflattening,[status(thm)],[c_168]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_171,plain,
% 0.80/0.97      ( ~ r2_xboole_0(sK1,sK3)
% 0.80/0.97      | r2_hidden(sK1,sK3)
% 0.80/0.97      | ~ v1_ordinal1(sK1) ),
% 0.80/0.97      inference(instantiation,[status(thm)],[c_169]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_10,negated_conjecture,
% 0.80/0.97      ( ~ r2_hidden(sK1,sK3) ),
% 0.80/0.97      inference(cnf_transformation,[],[f44]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_11,negated_conjecture,
% 0.80/0.97      ( r2_hidden(sK2,sK3) ),
% 0.80/0.97      inference(cnf_transformation,[],[f43]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_12,negated_conjecture,
% 0.80/0.97      ( r1_tarski(sK1,sK2) ),
% 0.80/0.97      inference(cnf_transformation,[],[f42]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(c_15,negated_conjecture,
% 0.80/0.97      ( v1_ordinal1(sK1) ),
% 0.80/0.97      inference(cnf_transformation,[],[f39]) ).
% 0.80/0.97  
% 0.80/0.97  cnf(contradiction,plain,
% 0.80/0.97      ( $false ),
% 0.80/0.97      inference(minisat,
% 0.80/0.97                [status(thm)],
% 0.80/0.97                [c_1187,c_1131,c_1075,c_980,c_968,c_921,c_199,c_171,c_10,
% 0.80/0.97                 c_11,c_12,c_15]) ).
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 0.80/0.97  
% 0.80/0.97  ------                               Statistics
% 0.80/0.97  
% 0.80/0.97  ------ General
% 0.80/0.97  
% 0.80/0.97  abstr_ref_over_cycles:                  0
% 0.80/0.97  abstr_ref_under_cycles:                 0
% 0.80/0.97  gc_basic_clause_elim:                   0
% 0.80/0.97  forced_gc_time:                         0
% 0.80/0.97  parsing_time:                           0.008
% 0.80/0.97  unif_index_cands_time:                  0.
% 0.80/0.97  unif_index_add_time:                    0.
% 0.80/0.97  orderings_time:                         0.
% 0.80/0.97  out_proof_time:                         0.007
% 0.80/0.97  total_time:                             0.056
% 0.80/0.97  num_of_symbols:                         37
% 0.80/0.97  num_of_terms:                           433
% 0.80/0.97  
% 0.80/0.97  ------ Preprocessing
% 0.80/0.97  
% 0.80/0.97  num_of_splits:                          0
% 0.80/0.97  num_of_split_atoms:                     0
% 0.80/0.97  num_of_reused_defs:                     0
% 0.80/0.97  num_eq_ax_congr_red:                    5
% 0.80/0.97  num_of_sem_filtered_clauses:            1
% 0.80/0.97  num_of_subtypes:                        1
% 0.80/0.97  monotx_restored_types:                  1
% 0.80/0.97  sat_num_of_epr_types:                   0
% 0.80/0.97  sat_num_of_non_cyclic_types:            0
% 0.80/0.97  sat_guarded_non_collapsed_types:        0
% 0.80/0.97  num_pure_diseq_elim:                    0
% 0.80/0.97  simp_replaced_by:                       0
% 0.80/0.97  res_preprocessed:                       61
% 0.80/0.97  prep_upred:                             0
% 0.80/0.97  prep_unflattend:                        24
% 0.80/0.97  smt_new_axioms:                         0
% 0.80/0.97  pred_elim_cands:                        5
% 0.80/0.97  pred_elim:                              1
% 0.80/0.97  pred_elim_cl:                           0
% 0.80/0.97  pred_elim_cycles:                       3
% 0.80/0.97  merged_defs:                            0
% 0.80/0.97  merged_defs_ncl:                        0
% 0.80/0.97  bin_hyper_res:                          0
% 0.80/0.97  prep_cycles:                            3
% 0.80/0.97  pred_elim_time:                         0.004
% 0.80/0.97  splitting_time:                         0.
% 0.80/0.97  sem_filter_time:                        0.
% 0.80/0.97  monotx_time:                            0.
% 0.80/0.97  subtype_inf_time:                       0.
% 0.80/0.97  
% 0.80/0.97  ------ Problem properties
% 0.80/0.97  
% 0.80/0.97  clauses:                                16
% 0.80/0.97  conjectures:                            4
% 0.80/0.97  epr:                                    14
% 0.80/0.97  horn:                                   14
% 0.80/0.97  ground:                                 6
% 0.80/0.97  unary:                                  7
% 0.80/0.97  binary:                                 4
% 0.80/0.97  lits:                                   30
% 0.80/0.97  lits_eq:                                1
% 0.80/0.97  fd_pure:                                0
% 0.80/0.97  fd_pseudo:                              0
% 0.80/0.97  fd_cond:                                0
% 0.80/0.97  fd_pseudo_cond:                         1
% 0.80/0.97  ac_symbols:                             0
% 0.80/0.97  
% 0.80/0.97  ------ Propositional Solver
% 0.80/0.97  
% 0.80/0.97  prop_solver_calls:                      21
% 0.80/0.97  prop_fast_solver_calls:                 334
% 0.80/0.97  smt_solver_calls:                       0
% 0.80/0.97  smt_fast_solver_calls:                  0
% 0.80/0.97  prop_num_of_clauses:                    241
% 0.80/0.97  prop_preprocess_simplified:             1901
% 0.80/0.97  prop_fo_subsumed:                       1
% 0.80/0.97  prop_solver_time:                       0.
% 0.80/0.97  smt_solver_time:                        0.
% 0.80/0.97  smt_fast_solver_time:                   0.
% 0.80/0.97  prop_fast_solver_time:                  0.
% 0.80/0.97  prop_unsat_core_time:                   0.
% 0.80/0.97  
% 0.80/0.97  ------ QBF
% 0.80/0.97  
% 0.80/0.97  qbf_q_res:                              0
% 0.80/0.97  qbf_num_tautologies:                    0
% 0.80/0.97  qbf_prep_cycles:                        0
% 0.80/0.97  
% 0.80/0.97  ------ BMC1
% 0.80/0.97  
% 0.80/0.97  bmc1_current_bound:                     -1
% 0.80/0.97  bmc1_last_solved_bound:                 -1
% 0.80/0.97  bmc1_unsat_core_size:                   -1
% 0.80/0.97  bmc1_unsat_core_parents_size:           -1
% 0.80/0.97  bmc1_merge_next_fun:                    0
% 0.80/0.97  bmc1_unsat_core_clauses_time:           0.
% 0.80/0.97  
% 0.80/0.97  ------ Instantiation
% 0.80/0.97  
% 0.80/0.97  inst_num_of_clauses:                    70
% 0.80/0.97  inst_num_in_passive:                    7
% 0.80/0.97  inst_num_in_active:                     60
% 0.80/0.97  inst_num_in_unprocessed:                2
% 0.80/0.97  inst_num_of_loops:                      66
% 0.80/0.97  inst_num_of_learning_restarts:          0
% 0.80/0.97  inst_num_moves_active_passive:          1
% 0.80/0.97  inst_lit_activity:                      0
% 0.80/0.97  inst_lit_activity_moves:                0
% 0.80/0.97  inst_num_tautologies:                   0
% 0.80/0.97  inst_num_prop_implied:                  0
% 0.80/0.97  inst_num_existing_simplified:           0
% 0.80/0.97  inst_num_eq_res_simplified:             0
% 0.80/0.97  inst_num_child_elim:                    0
% 0.80/0.97  inst_num_of_dismatching_blockings:      2
% 0.80/0.97  inst_num_of_non_proper_insts:           68
% 0.80/0.97  inst_num_of_duplicates:                 0
% 0.80/0.97  inst_inst_num_from_inst_to_res:         0
% 0.80/0.97  inst_dismatching_checking_time:         0.
% 0.80/0.97  
% 0.80/0.97  ------ Resolution
% 0.80/0.97  
% 0.80/0.97  res_num_of_clauses:                     0
% 0.80/0.97  res_num_in_passive:                     0
% 0.80/0.97  res_num_in_active:                      0
% 0.80/0.97  res_num_of_loops:                       64
% 0.80/0.97  res_forward_subset_subsumed:            12
% 0.80/0.97  res_backward_subset_subsumed:           0
% 0.80/0.97  res_forward_subsumed:                   2
% 0.80/0.97  res_backward_subsumed:                  0
% 0.80/0.97  res_forward_subsumption_resolution:     0
% 0.80/0.97  res_backward_subsumption_resolution:    0
% 0.80/0.97  res_clause_to_clause_subsumption:       81
% 0.80/0.97  res_orphan_elimination:                 0
% 0.80/0.97  res_tautology_del:                      9
% 0.80/0.97  res_num_eq_res_simplified:              0
% 0.80/0.97  res_num_sel_changes:                    0
% 0.80/0.97  res_moves_from_active_to_pass:          0
% 0.80/0.97  
% 0.80/0.97  ------ Superposition
% 0.80/0.97  
% 0.80/0.97  sup_time_total:                         0.
% 0.80/0.97  sup_time_generating:                    0.
% 0.80/0.97  sup_time_sim_full:                      0.
% 0.80/0.97  sup_time_sim_immed:                     0.
% 0.80/0.97  
% 0.80/0.97  sup_num_of_clauses:                     18
% 0.80/0.97  sup_num_in_active:                      12
% 0.80/0.97  sup_num_in_passive:                     6
% 0.80/0.97  sup_num_of_loops:                       12
% 0.80/0.97  sup_fw_superposition:                   1
% 0.80/0.97  sup_bw_superposition:                   1
% 0.80/0.97  sup_immediate_simplified:               0
% 0.80/0.97  sup_given_eliminated:                   0
% 0.80/0.97  comparisons_done:                       0
% 0.80/0.97  comparisons_avoided:                    0
% 0.80/0.97  
% 0.80/0.97  ------ Simplifications
% 0.80/0.97  
% 0.80/0.97  
% 0.80/0.97  sim_fw_subset_subsumed:                 0
% 0.80/0.97  sim_bw_subset_subsumed:                 0
% 0.80/0.97  sim_fw_subsumed:                        0
% 0.80/0.97  sim_bw_subsumed:                        0
% 0.80/0.97  sim_fw_subsumption_res:                 0
% 0.80/0.97  sim_bw_subsumption_res:                 0
% 0.80/0.97  sim_tautology_del:                      0
% 0.80/0.97  sim_eq_tautology_del:                   0
% 0.80/0.97  sim_eq_res_simp:                        0
% 0.80/0.97  sim_fw_demodulated:                     0
% 0.80/0.97  sim_bw_demodulated:                     0
% 0.80/0.97  sim_light_normalised:                   0
% 0.80/0.97  sim_joinable_taut:                      0
% 0.80/0.97  sim_joinable_simp:                      0
% 0.80/0.97  sim_ac_normalised:                      0
% 0.80/0.97  sim_smt_subsumption:                    0
% 0.80/0.97  
%------------------------------------------------------------------------------
