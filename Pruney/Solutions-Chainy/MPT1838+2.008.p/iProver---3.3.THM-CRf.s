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
% DateTime   : Thu Dec  3 12:24:32 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 196 expanded)
%              Number of clauses        :   37 (  55 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  226 ( 816 expanded)
%              Number of equality atoms :   88 ( 228 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK2 != X0
        & r1_tarski(X0,sK2)
        & v1_zfmisc_1(sK2)
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK1 != X1
          & r1_tarski(sK1,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( sK1 != sK2
    & r1_tarski(sK1,sK2)
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f42,f41])).

fof(f69,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_858,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,plain,
    ( m1_subset_1(sK0(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_311,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | sK0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_312,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_24,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_330,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_24])).

cnf(c_331,plain,
    ( v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_333,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_25])).

cnf(c_20,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_338,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_339,plain,
    ( v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_341,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_25])).

cnf(c_890,plain,
    ( k1_tarski(sK0(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_333,c_341])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_859,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1965,plain,
    ( k1_tarski(sK0(sK2)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_859])).

cnf(c_1969,plain,
    ( sK2 = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1965,c_890])).

cnf(c_2700,plain,
    ( sK2 = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_858,c_1969])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_53,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_56,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_58,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_67,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_493,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_988,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_990,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_2706,plain,
    ( sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2700,c_26,c_53,c_56,c_58,c_67,c_990])).

cnf(c_22,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2717,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_2706,c_22])).

cnf(c_2718,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2717])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.55/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/0.98  
% 2.55/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/0.98  
% 2.55/0.98  ------  iProver source info
% 2.55/0.98  
% 2.55/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.55/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/0.98  git: non_committed_changes: false
% 2.55/0.98  git: last_make_outside_of_git: false
% 2.55/0.98  
% 2.55/0.98  ------ 
% 2.55/0.98  
% 2.55/0.98  ------ Input Options
% 2.55/0.98  
% 2.55/0.98  --out_options                           all
% 2.55/0.98  --tptp_safe_out                         true
% 2.55/0.98  --problem_path                          ""
% 2.55/0.98  --include_path                          ""
% 2.55/0.98  --clausifier                            res/vclausify_rel
% 2.55/0.98  --clausifier_options                    --mode clausify
% 2.55/0.98  --stdin                                 false
% 2.55/0.98  --stats_out                             all
% 2.55/0.98  
% 2.55/0.98  ------ General Options
% 2.55/0.98  
% 2.55/0.98  --fof                                   false
% 2.55/0.98  --time_out_real                         305.
% 2.55/0.98  --time_out_virtual                      -1.
% 2.55/0.98  --symbol_type_check                     false
% 2.55/0.98  --clausify_out                          false
% 2.55/0.98  --sig_cnt_out                           false
% 2.55/0.98  --trig_cnt_out                          false
% 2.55/0.98  --trig_cnt_out_tolerance                1.
% 2.55/0.98  --trig_cnt_out_sk_spl                   false
% 2.55/0.98  --abstr_cl_out                          false
% 2.55/0.98  
% 2.55/0.98  ------ Global Options
% 2.55/0.98  
% 2.55/0.98  --schedule                              default
% 2.55/0.98  --add_important_lit                     false
% 2.55/0.98  --prop_solver_per_cl                    1000
% 2.55/0.98  --min_unsat_core                        false
% 2.55/0.98  --soft_assumptions                      false
% 2.55/0.98  --soft_lemma_size                       3
% 2.55/0.98  --prop_impl_unit_size                   0
% 2.55/0.98  --prop_impl_unit                        []
% 2.55/0.98  --share_sel_clauses                     true
% 2.55/0.98  --reset_solvers                         false
% 2.55/0.98  --bc_imp_inh                            [conj_cone]
% 2.55/0.98  --conj_cone_tolerance                   3.
% 2.55/0.98  --extra_neg_conj                        none
% 2.55/0.98  --large_theory_mode                     true
% 2.55/0.98  --prolific_symb_bound                   200
% 2.55/0.98  --lt_threshold                          2000
% 2.55/0.98  --clause_weak_htbl                      true
% 2.55/0.98  --gc_record_bc_elim                     false
% 2.55/0.98  
% 2.55/0.98  ------ Preprocessing Options
% 2.55/0.98  
% 2.55/0.98  --preprocessing_flag                    true
% 2.55/0.98  --time_out_prep_mult                    0.1
% 2.55/0.98  --splitting_mode                        input
% 2.55/0.98  --splitting_grd                         true
% 2.55/0.98  --splitting_cvd                         false
% 2.55/0.98  --splitting_cvd_svl                     false
% 2.55/0.98  --splitting_nvd                         32
% 2.55/0.98  --sub_typing                            true
% 2.55/0.98  --prep_gs_sim                           true
% 2.55/0.98  --prep_unflatten                        true
% 2.55/0.98  --prep_res_sim                          true
% 2.55/0.98  --prep_upred                            true
% 2.55/0.98  --prep_sem_filter                       exhaustive
% 2.55/0.98  --prep_sem_filter_out                   false
% 2.55/0.98  --pred_elim                             true
% 2.55/0.98  --res_sim_input                         true
% 2.55/0.98  --eq_ax_congr_red                       true
% 2.55/0.98  --pure_diseq_elim                       true
% 2.55/0.98  --brand_transform                       false
% 2.55/0.98  --non_eq_to_eq                          false
% 2.55/0.98  --prep_def_merge                        true
% 2.55/0.98  --prep_def_merge_prop_impl              false
% 2.55/0.98  --prep_def_merge_mbd                    true
% 2.55/0.98  --prep_def_merge_tr_red                 false
% 2.55/0.98  --prep_def_merge_tr_cl                  false
% 2.55/0.98  --smt_preprocessing                     true
% 2.55/0.98  --smt_ac_axioms                         fast
% 2.55/0.98  --preprocessed_out                      false
% 2.55/0.98  --preprocessed_stats                    false
% 2.55/0.98  
% 2.55/0.98  ------ Abstraction refinement Options
% 2.55/0.98  
% 2.55/0.98  --abstr_ref                             []
% 2.55/0.98  --abstr_ref_prep                        false
% 2.55/0.98  --abstr_ref_until_sat                   false
% 2.55/0.98  --abstr_ref_sig_restrict                funpre
% 2.55/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/0.98  --abstr_ref_under                       []
% 2.55/0.98  
% 2.55/0.98  ------ SAT Options
% 2.55/0.98  
% 2.55/0.98  --sat_mode                              false
% 2.55/0.98  --sat_fm_restart_options                ""
% 2.55/0.98  --sat_gr_def                            false
% 2.55/0.98  --sat_epr_types                         true
% 2.55/0.98  --sat_non_cyclic_types                  false
% 2.55/0.98  --sat_finite_models                     false
% 2.55/0.98  --sat_fm_lemmas                         false
% 2.55/0.98  --sat_fm_prep                           false
% 2.55/0.98  --sat_fm_uc_incr                        true
% 2.55/0.98  --sat_out_model                         small
% 2.55/0.98  --sat_out_clauses                       false
% 2.55/0.98  
% 2.55/0.98  ------ QBF Options
% 2.55/0.98  
% 2.55/0.98  --qbf_mode                              false
% 2.55/0.98  --qbf_elim_univ                         false
% 2.55/0.98  --qbf_dom_inst                          none
% 2.55/0.98  --qbf_dom_pre_inst                      false
% 2.55/0.98  --qbf_sk_in                             false
% 2.55/0.98  --qbf_pred_elim                         true
% 2.55/0.98  --qbf_split                             512
% 2.55/0.98  
% 2.55/0.98  ------ BMC1 Options
% 2.55/0.98  
% 2.55/0.98  --bmc1_incremental                      false
% 2.55/0.98  --bmc1_axioms                           reachable_all
% 2.55/0.98  --bmc1_min_bound                        0
% 2.55/0.98  --bmc1_max_bound                        -1
% 2.55/0.98  --bmc1_max_bound_default                -1
% 2.55/0.98  --bmc1_symbol_reachability              true
% 2.55/0.98  --bmc1_property_lemmas                  false
% 2.55/0.98  --bmc1_k_induction                      false
% 2.55/0.98  --bmc1_non_equiv_states                 false
% 2.55/0.98  --bmc1_deadlock                         false
% 2.55/0.98  --bmc1_ucm                              false
% 2.55/0.98  --bmc1_add_unsat_core                   none
% 2.55/0.98  --bmc1_unsat_core_children              false
% 2.55/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/0.98  --bmc1_out_stat                         full
% 2.55/0.98  --bmc1_ground_init                      false
% 2.55/0.98  --bmc1_pre_inst_next_state              false
% 2.55/0.98  --bmc1_pre_inst_state                   false
% 2.55/0.98  --bmc1_pre_inst_reach_state             false
% 2.55/0.98  --bmc1_out_unsat_core                   false
% 2.55/0.98  --bmc1_aig_witness_out                  false
% 2.55/0.98  --bmc1_verbose                          false
% 2.55/0.98  --bmc1_dump_clauses_tptp                false
% 2.55/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.55/0.98  --bmc1_dump_file                        -
% 2.55/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.55/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.55/0.98  --bmc1_ucm_extend_mode                  1
% 2.55/0.98  --bmc1_ucm_init_mode                    2
% 2.55/0.98  --bmc1_ucm_cone_mode                    none
% 2.55/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.55/0.98  --bmc1_ucm_relax_model                  4
% 2.55/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.55/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/0.98  --bmc1_ucm_layered_model                none
% 2.55/0.98  --bmc1_ucm_max_lemma_size               10
% 2.55/0.98  
% 2.55/0.98  ------ AIG Options
% 2.55/0.98  
% 2.55/0.98  --aig_mode                              false
% 2.55/0.98  
% 2.55/0.98  ------ Instantiation Options
% 2.55/0.98  
% 2.55/0.98  --instantiation_flag                    true
% 2.55/0.98  --inst_sos_flag                         false
% 2.55/0.98  --inst_sos_phase                        true
% 2.55/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/0.98  --inst_lit_sel_side                     num_symb
% 2.55/0.98  --inst_solver_per_active                1400
% 2.55/0.98  --inst_solver_calls_frac                1.
% 2.55/0.98  --inst_passive_queue_type               priority_queues
% 2.55/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/0.98  --inst_passive_queues_freq              [25;2]
% 2.55/0.98  --inst_dismatching                      true
% 2.55/0.98  --inst_eager_unprocessed_to_passive     true
% 2.55/0.98  --inst_prop_sim_given                   true
% 2.55/0.98  --inst_prop_sim_new                     false
% 2.55/0.98  --inst_subs_new                         false
% 2.55/0.98  --inst_eq_res_simp                      false
% 2.55/0.98  --inst_subs_given                       false
% 2.55/0.98  --inst_orphan_elimination               true
% 2.55/0.98  --inst_learning_loop_flag               true
% 2.55/0.98  --inst_learning_start                   3000
% 2.55/0.98  --inst_learning_factor                  2
% 2.55/0.98  --inst_start_prop_sim_after_learn       3
% 2.55/0.98  --inst_sel_renew                        solver
% 2.55/0.98  --inst_lit_activity_flag                true
% 2.55/0.98  --inst_restr_to_given                   false
% 2.55/0.98  --inst_activity_threshold               500
% 2.55/0.98  --inst_out_proof                        true
% 2.55/0.98  
% 2.55/0.98  ------ Resolution Options
% 2.55/0.98  
% 2.55/0.98  --resolution_flag                       true
% 2.55/0.98  --res_lit_sel                           adaptive
% 2.55/0.98  --res_lit_sel_side                      none
% 2.55/0.98  --res_ordering                          kbo
% 2.55/0.98  --res_to_prop_solver                    active
% 2.55/0.98  --res_prop_simpl_new                    false
% 2.55/0.98  --res_prop_simpl_given                  true
% 2.55/0.98  --res_passive_queue_type                priority_queues
% 2.55/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/0.98  --res_passive_queues_freq               [15;5]
% 2.55/0.98  --res_forward_subs                      full
% 2.55/0.98  --res_backward_subs                     full
% 2.55/0.98  --res_forward_subs_resolution           true
% 2.55/0.98  --res_backward_subs_resolution          true
% 2.55/0.98  --res_orphan_elimination                true
% 2.55/0.98  --res_time_limit                        2.
% 2.55/0.98  --res_out_proof                         true
% 2.55/0.98  
% 2.55/0.98  ------ Superposition Options
% 2.55/0.98  
% 2.55/0.98  --superposition_flag                    true
% 2.55/0.98  --sup_passive_queue_type                priority_queues
% 2.55/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.55/0.98  --demod_completeness_check              fast
% 2.55/0.98  --demod_use_ground                      true
% 2.55/0.98  --sup_to_prop_solver                    passive
% 2.55/0.98  --sup_prop_simpl_new                    true
% 2.55/0.98  --sup_prop_simpl_given                  true
% 2.55/0.98  --sup_fun_splitting                     false
% 2.55/0.98  --sup_smt_interval                      50000
% 2.55/0.98  
% 2.55/0.98  ------ Superposition Simplification Setup
% 2.55/0.98  
% 2.55/0.98  --sup_indices_passive                   []
% 2.55/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.98  --sup_full_bw                           [BwDemod]
% 2.55/0.98  --sup_immed_triv                        [TrivRules]
% 2.55/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.98  --sup_immed_bw_main                     []
% 2.55/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.98  
% 2.55/0.98  ------ Combination Options
% 2.55/0.98  
% 2.55/0.98  --comb_res_mult                         3
% 2.55/0.98  --comb_sup_mult                         2
% 2.55/0.98  --comb_inst_mult                        10
% 2.55/0.98  
% 2.55/0.98  ------ Debug Options
% 2.55/0.98  
% 2.55/0.98  --dbg_backtrace                         false
% 2.55/0.98  --dbg_dump_prop_clauses                 false
% 2.55/0.98  --dbg_dump_prop_clauses_file            -
% 2.55/0.98  --dbg_out_stat                          false
% 2.55/0.98  ------ Parsing...
% 2.55/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/0.98  
% 2.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.55/0.98  
% 2.55/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/0.98  
% 2.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/0.98  ------ Proving...
% 2.55/0.98  ------ Problem Properties 
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  clauses                                 22
% 2.55/0.98  conjectures                             4
% 2.55/0.98  EPR                                     7
% 2.55/0.98  Horn                                    21
% 2.55/0.98  unary                                   13
% 2.55/0.98  binary                                  5
% 2.55/0.98  lits                                    35
% 2.55/0.98  lits eq                                 14
% 2.55/0.98  fd_pure                                 0
% 2.55/0.98  fd_pseudo                               0
% 2.55/0.98  fd_cond                                 0
% 2.55/0.98  fd_pseudo_cond                          2
% 2.55/0.98  AC symbols                              0
% 2.55/0.98  
% 2.55/0.98  ------ Schedule dynamic 5 is on 
% 2.55/0.98  
% 2.55/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  ------ 
% 2.55/0.98  Current options:
% 2.55/0.98  ------ 
% 2.55/0.98  
% 2.55/0.98  ------ Input Options
% 2.55/0.98  
% 2.55/0.98  --out_options                           all
% 2.55/0.98  --tptp_safe_out                         true
% 2.55/0.98  --problem_path                          ""
% 2.55/0.98  --include_path                          ""
% 2.55/0.98  --clausifier                            res/vclausify_rel
% 2.55/0.98  --clausifier_options                    --mode clausify
% 2.55/0.98  --stdin                                 false
% 2.55/0.98  --stats_out                             all
% 2.55/0.98  
% 2.55/0.98  ------ General Options
% 2.55/0.98  
% 2.55/0.98  --fof                                   false
% 2.55/0.98  --time_out_real                         305.
% 2.55/0.98  --time_out_virtual                      -1.
% 2.55/0.98  --symbol_type_check                     false
% 2.55/0.98  --clausify_out                          false
% 2.55/0.98  --sig_cnt_out                           false
% 2.55/0.98  --trig_cnt_out                          false
% 2.55/0.98  --trig_cnt_out_tolerance                1.
% 2.55/0.98  --trig_cnt_out_sk_spl                   false
% 2.55/0.98  --abstr_cl_out                          false
% 2.55/0.98  
% 2.55/0.98  ------ Global Options
% 2.55/0.98  
% 2.55/0.98  --schedule                              default
% 2.55/0.98  --add_important_lit                     false
% 2.55/0.98  --prop_solver_per_cl                    1000
% 2.55/0.98  --min_unsat_core                        false
% 2.55/0.98  --soft_assumptions                      false
% 2.55/0.98  --soft_lemma_size                       3
% 2.55/0.98  --prop_impl_unit_size                   0
% 2.55/0.98  --prop_impl_unit                        []
% 2.55/0.98  --share_sel_clauses                     true
% 2.55/0.98  --reset_solvers                         false
% 2.55/0.98  --bc_imp_inh                            [conj_cone]
% 2.55/0.98  --conj_cone_tolerance                   3.
% 2.55/0.98  --extra_neg_conj                        none
% 2.55/0.98  --large_theory_mode                     true
% 2.55/0.98  --prolific_symb_bound                   200
% 2.55/0.98  --lt_threshold                          2000
% 2.55/0.98  --clause_weak_htbl                      true
% 2.55/0.98  --gc_record_bc_elim                     false
% 2.55/0.98  
% 2.55/0.98  ------ Preprocessing Options
% 2.55/0.98  
% 2.55/0.98  --preprocessing_flag                    true
% 2.55/0.98  --time_out_prep_mult                    0.1
% 2.55/0.98  --splitting_mode                        input
% 2.55/0.98  --splitting_grd                         true
% 2.55/0.98  --splitting_cvd                         false
% 2.55/0.98  --splitting_cvd_svl                     false
% 2.55/0.98  --splitting_nvd                         32
% 2.55/0.98  --sub_typing                            true
% 2.55/0.98  --prep_gs_sim                           true
% 2.55/0.98  --prep_unflatten                        true
% 2.55/0.98  --prep_res_sim                          true
% 2.55/0.98  --prep_upred                            true
% 2.55/0.98  --prep_sem_filter                       exhaustive
% 2.55/0.98  --prep_sem_filter_out                   false
% 2.55/0.98  --pred_elim                             true
% 2.55/0.98  --res_sim_input                         true
% 2.55/0.98  --eq_ax_congr_red                       true
% 2.55/0.98  --pure_diseq_elim                       true
% 2.55/0.98  --brand_transform                       false
% 2.55/0.98  --non_eq_to_eq                          false
% 2.55/0.98  --prep_def_merge                        true
% 2.55/0.98  --prep_def_merge_prop_impl              false
% 2.55/0.98  --prep_def_merge_mbd                    true
% 2.55/0.98  --prep_def_merge_tr_red                 false
% 2.55/0.98  --prep_def_merge_tr_cl                  false
% 2.55/0.98  --smt_preprocessing                     true
% 2.55/0.98  --smt_ac_axioms                         fast
% 2.55/0.98  --preprocessed_out                      false
% 2.55/0.98  --preprocessed_stats                    false
% 2.55/0.98  
% 2.55/0.98  ------ Abstraction refinement Options
% 2.55/0.98  
% 2.55/0.98  --abstr_ref                             []
% 2.55/0.98  --abstr_ref_prep                        false
% 2.55/0.98  --abstr_ref_until_sat                   false
% 2.55/0.98  --abstr_ref_sig_restrict                funpre
% 2.55/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/0.98  --abstr_ref_under                       []
% 2.55/0.98  
% 2.55/0.98  ------ SAT Options
% 2.55/0.98  
% 2.55/0.98  --sat_mode                              false
% 2.55/0.98  --sat_fm_restart_options                ""
% 2.55/0.98  --sat_gr_def                            false
% 2.55/0.98  --sat_epr_types                         true
% 2.55/0.98  --sat_non_cyclic_types                  false
% 2.55/0.98  --sat_finite_models                     false
% 2.55/0.98  --sat_fm_lemmas                         false
% 2.55/0.98  --sat_fm_prep                           false
% 2.55/0.98  --sat_fm_uc_incr                        true
% 2.55/0.98  --sat_out_model                         small
% 2.55/0.98  --sat_out_clauses                       false
% 2.55/0.98  
% 2.55/0.98  ------ QBF Options
% 2.55/0.98  
% 2.55/0.98  --qbf_mode                              false
% 2.55/0.98  --qbf_elim_univ                         false
% 2.55/0.98  --qbf_dom_inst                          none
% 2.55/0.98  --qbf_dom_pre_inst                      false
% 2.55/0.98  --qbf_sk_in                             false
% 2.55/0.98  --qbf_pred_elim                         true
% 2.55/0.98  --qbf_split                             512
% 2.55/0.98  
% 2.55/0.98  ------ BMC1 Options
% 2.55/0.98  
% 2.55/0.98  --bmc1_incremental                      false
% 2.55/0.98  --bmc1_axioms                           reachable_all
% 2.55/0.98  --bmc1_min_bound                        0
% 2.55/0.98  --bmc1_max_bound                        -1
% 2.55/0.98  --bmc1_max_bound_default                -1
% 2.55/0.98  --bmc1_symbol_reachability              true
% 2.55/0.98  --bmc1_property_lemmas                  false
% 2.55/0.98  --bmc1_k_induction                      false
% 2.55/0.98  --bmc1_non_equiv_states                 false
% 2.55/0.98  --bmc1_deadlock                         false
% 2.55/0.98  --bmc1_ucm                              false
% 2.55/0.98  --bmc1_add_unsat_core                   none
% 2.55/0.98  --bmc1_unsat_core_children              false
% 2.55/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/0.98  --bmc1_out_stat                         full
% 2.55/0.98  --bmc1_ground_init                      false
% 2.55/0.98  --bmc1_pre_inst_next_state              false
% 2.55/0.98  --bmc1_pre_inst_state                   false
% 2.55/0.98  --bmc1_pre_inst_reach_state             false
% 2.55/0.98  --bmc1_out_unsat_core                   false
% 2.55/0.98  --bmc1_aig_witness_out                  false
% 2.55/0.98  --bmc1_verbose                          false
% 2.55/0.98  --bmc1_dump_clauses_tptp                false
% 2.55/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.55/0.98  --bmc1_dump_file                        -
% 2.55/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.55/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.55/0.98  --bmc1_ucm_extend_mode                  1
% 2.55/0.98  --bmc1_ucm_init_mode                    2
% 2.55/0.98  --bmc1_ucm_cone_mode                    none
% 2.55/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.55/0.98  --bmc1_ucm_relax_model                  4
% 2.55/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.55/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/0.98  --bmc1_ucm_layered_model                none
% 2.55/0.98  --bmc1_ucm_max_lemma_size               10
% 2.55/0.98  
% 2.55/0.98  ------ AIG Options
% 2.55/0.98  
% 2.55/0.98  --aig_mode                              false
% 2.55/0.98  
% 2.55/0.98  ------ Instantiation Options
% 2.55/0.98  
% 2.55/0.98  --instantiation_flag                    true
% 2.55/0.98  --inst_sos_flag                         false
% 2.55/0.98  --inst_sos_phase                        true
% 2.55/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/0.98  --inst_lit_sel_side                     none
% 2.55/0.98  --inst_solver_per_active                1400
% 2.55/0.98  --inst_solver_calls_frac                1.
% 2.55/0.98  --inst_passive_queue_type               priority_queues
% 2.55/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/0.98  --inst_passive_queues_freq              [25;2]
% 2.55/0.98  --inst_dismatching                      true
% 2.55/0.98  --inst_eager_unprocessed_to_passive     true
% 2.55/0.98  --inst_prop_sim_given                   true
% 2.55/0.98  --inst_prop_sim_new                     false
% 2.55/0.98  --inst_subs_new                         false
% 2.55/0.98  --inst_eq_res_simp                      false
% 2.55/0.98  --inst_subs_given                       false
% 2.55/0.98  --inst_orphan_elimination               true
% 2.55/0.98  --inst_learning_loop_flag               true
% 2.55/0.98  --inst_learning_start                   3000
% 2.55/0.98  --inst_learning_factor                  2
% 2.55/0.98  --inst_start_prop_sim_after_learn       3
% 2.55/0.98  --inst_sel_renew                        solver
% 2.55/0.98  --inst_lit_activity_flag                true
% 2.55/0.98  --inst_restr_to_given                   false
% 2.55/0.98  --inst_activity_threshold               500
% 2.55/0.98  --inst_out_proof                        true
% 2.55/0.98  
% 2.55/0.98  ------ Resolution Options
% 2.55/0.98  
% 2.55/0.98  --resolution_flag                       false
% 2.55/0.98  --res_lit_sel                           adaptive
% 2.55/0.98  --res_lit_sel_side                      none
% 2.55/0.98  --res_ordering                          kbo
% 2.55/0.98  --res_to_prop_solver                    active
% 2.55/0.98  --res_prop_simpl_new                    false
% 2.55/0.98  --res_prop_simpl_given                  true
% 2.55/0.98  --res_passive_queue_type                priority_queues
% 2.55/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/0.98  --res_passive_queues_freq               [15;5]
% 2.55/0.98  --res_forward_subs                      full
% 2.55/0.98  --res_backward_subs                     full
% 2.55/0.98  --res_forward_subs_resolution           true
% 2.55/0.98  --res_backward_subs_resolution          true
% 2.55/0.98  --res_orphan_elimination                true
% 2.55/0.98  --res_time_limit                        2.
% 2.55/0.98  --res_out_proof                         true
% 2.55/0.98  
% 2.55/0.98  ------ Superposition Options
% 2.55/0.98  
% 2.55/0.98  --superposition_flag                    true
% 2.55/0.98  --sup_passive_queue_type                priority_queues
% 2.55/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.55/0.98  --demod_completeness_check              fast
% 2.55/0.98  --demod_use_ground                      true
% 2.55/0.98  --sup_to_prop_solver                    passive
% 2.55/0.98  --sup_prop_simpl_new                    true
% 2.55/0.98  --sup_prop_simpl_given                  true
% 2.55/0.98  --sup_fun_splitting                     false
% 2.55/0.98  --sup_smt_interval                      50000
% 2.55/0.98  
% 2.55/0.98  ------ Superposition Simplification Setup
% 2.55/0.98  
% 2.55/0.98  --sup_indices_passive                   []
% 2.55/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.98  --sup_full_bw                           [BwDemod]
% 2.55/0.98  --sup_immed_triv                        [TrivRules]
% 2.55/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.98  --sup_immed_bw_main                     []
% 2.55/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.98  
% 2.55/0.98  ------ Combination Options
% 2.55/0.98  
% 2.55/0.98  --comb_res_mult                         3
% 2.55/0.98  --comb_sup_mult                         2
% 2.55/0.98  --comb_inst_mult                        10
% 2.55/0.98  
% 2.55/0.98  ------ Debug Options
% 2.55/0.98  
% 2.55/0.98  --dbg_backtrace                         false
% 2.55/0.98  --dbg_dump_prop_clauses                 false
% 2.55/0.98  --dbg_dump_prop_clauses_file            -
% 2.55/0.98  --dbg_out_stat                          false
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  ------ Proving...
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  % SZS status Theorem for theBenchmark.p
% 2.55/0.98  
% 2.55/0.98   Resolution empty clause
% 2.55/0.98  
% 2.55/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/0.98  
% 2.55/0.98  fof(f16,conjecture,(
% 2.55/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f17,negated_conjecture,(
% 2.55/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.55/0.98    inference(negated_conjecture,[],[f16])).
% 2.55/0.98  
% 2.55/0.98  fof(f30,plain,(
% 2.55/0.98    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 2.55/0.98    inference(ennf_transformation,[],[f17])).
% 2.55/0.98  
% 2.55/0.98  fof(f31,plain,(
% 2.55/0.98    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.55/0.98    inference(flattening,[],[f30])).
% 2.55/0.98  
% 2.55/0.98  fof(f42,plain,(
% 2.55/0.98    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK2 != X0 & r1_tarski(X0,sK2) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2))) )),
% 2.55/0.98    introduced(choice_axiom,[])).
% 2.55/0.98  
% 2.55/0.98  fof(f41,plain,(
% 2.55/0.98    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK1 != X1 & r1_tarski(sK1,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 2.55/0.98    introduced(choice_axiom,[])).
% 2.55/0.98  
% 2.55/0.98  fof(f43,plain,(
% 2.55/0.98    (sK1 != sK2 & r1_tarski(sK1,sK2) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 2.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f42,f41])).
% 2.55/0.98  
% 2.55/0.98  fof(f69,plain,(
% 2.55/0.98    r1_tarski(sK1,sK2)),
% 2.55/0.98    inference(cnf_transformation,[],[f43])).
% 2.55/0.98  
% 2.55/0.98  fof(f14,axiom,(
% 2.55/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f27,plain,(
% 2.55/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.55/0.98    inference(ennf_transformation,[],[f14])).
% 2.55/0.98  
% 2.55/0.98  fof(f28,plain,(
% 2.55/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.55/0.98    inference(flattening,[],[f27])).
% 2.55/0.98  
% 2.55/0.98  fof(f62,plain,(
% 2.55/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.55/0.98    inference(cnf_transformation,[],[f28])).
% 2.55/0.98  
% 2.55/0.98  fof(f15,axiom,(
% 2.55/0.98    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f29,plain,(
% 2.55/0.98    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.55/0.98    inference(ennf_transformation,[],[f15])).
% 2.55/0.98  
% 2.55/0.98  fof(f37,plain,(
% 2.55/0.98    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.55/0.98    inference(nnf_transformation,[],[f29])).
% 2.55/0.98  
% 2.55/0.98  fof(f38,plain,(
% 2.55/0.98    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.55/0.98    inference(rectify,[],[f37])).
% 2.55/0.98  
% 2.55/0.98  fof(f39,plain,(
% 2.55/0.98    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.55/0.98    introduced(choice_axiom,[])).
% 2.55/0.98  
% 2.55/0.98  fof(f40,plain,(
% 2.55/0.98    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 2.55/0.98  
% 2.55/0.98  fof(f63,plain,(
% 2.55/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.55/0.98    inference(cnf_transformation,[],[f40])).
% 2.55/0.98  
% 2.55/0.98  fof(f68,plain,(
% 2.55/0.98    v1_zfmisc_1(sK2)),
% 2.55/0.98    inference(cnf_transformation,[],[f43])).
% 2.55/0.98  
% 2.55/0.98  fof(f67,plain,(
% 2.55/0.98    ~v1_xboole_0(sK2)),
% 2.55/0.98    inference(cnf_transformation,[],[f43])).
% 2.55/0.98  
% 2.55/0.98  fof(f64,plain,(
% 2.55/0.98    ( ! [X0] : (k6_domain_1(X0,sK0(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.55/0.98    inference(cnf_transformation,[],[f40])).
% 2.55/0.98  
% 2.55/0.98  fof(f13,axiom,(
% 2.55/0.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f35,plain,(
% 2.55/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.55/0.98    inference(nnf_transformation,[],[f13])).
% 2.55/0.98  
% 2.55/0.98  fof(f36,plain,(
% 2.55/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.55/0.98    inference(flattening,[],[f35])).
% 2.55/0.98  
% 2.55/0.98  fof(f59,plain,(
% 2.55/0.98    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.55/0.98    inference(cnf_transformation,[],[f36])).
% 2.55/0.98  
% 2.55/0.98  fof(f66,plain,(
% 2.55/0.98    ~v1_xboole_0(sK1)),
% 2.55/0.98    inference(cnf_transformation,[],[f43])).
% 2.55/0.98  
% 2.55/0.98  fof(f12,axiom,(
% 2.55/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f18,plain,(
% 2.55/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 2.55/0.98    inference(unused_predicate_definition_removal,[],[f12])).
% 2.55/0.98  
% 2.55/0.98  fof(f26,plain,(
% 2.55/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 2.55/0.98    inference(ennf_transformation,[],[f18])).
% 2.55/0.98  
% 2.55/0.98  fof(f58,plain,(
% 2.55/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.55/0.98    inference(cnf_transformation,[],[f26])).
% 2.55/0.98  
% 2.55/0.98  fof(f11,axiom,(
% 2.55/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f24,plain,(
% 2.55/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.55/0.98    inference(ennf_transformation,[],[f11])).
% 2.55/0.98  
% 2.55/0.98  fof(f25,plain,(
% 2.55/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.55/0.98    inference(flattening,[],[f24])).
% 2.55/0.98  
% 2.55/0.98  fof(f57,plain,(
% 2.55/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.55/0.98    inference(cnf_transformation,[],[f25])).
% 2.55/0.98  
% 2.55/0.98  fof(f10,axiom,(
% 2.55/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f56,plain,(
% 2.55/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.55/0.98    inference(cnf_transformation,[],[f10])).
% 2.55/0.98  
% 2.55/0.98  fof(f4,axiom,(
% 2.55/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.55/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.98  
% 2.55/0.98  fof(f34,plain,(
% 2.55/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.55/0.98    inference(nnf_transformation,[],[f4])).
% 2.55/0.98  
% 2.55/0.98  fof(f49,plain,(
% 2.55/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.55/0.98    inference(cnf_transformation,[],[f34])).
% 2.55/0.98  
% 2.55/0.98  fof(f70,plain,(
% 2.55/0.98    sK1 != sK2),
% 2.55/0.98    inference(cnf_transformation,[],[f43])).
% 2.55/0.98  
% 2.55/0.98  cnf(c_23,negated_conjecture,
% 2.55/0.98      ( r1_tarski(sK1,sK2) ),
% 2.55/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_858,plain,
% 2.55/0.98      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.55/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_18,plain,
% 2.55/0.98      ( ~ m1_subset_1(X0,X1)
% 2.55/0.98      | v1_xboole_0(X1)
% 2.55/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.55/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_21,plain,
% 2.55/0.98      ( m1_subset_1(sK0(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 2.55/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_311,plain,
% 2.55/0.98      ( ~ v1_zfmisc_1(X0)
% 2.55/0.98      | v1_xboole_0(X1)
% 2.55/0.98      | v1_xboole_0(X0)
% 2.55/0.98      | X0 != X1
% 2.55/0.98      | k6_domain_1(X1,X2) = k1_tarski(X2)
% 2.55/0.98      | sK0(X0) != X2 ),
% 2.55/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_312,plain,
% 2.55/0.98      ( ~ v1_zfmisc_1(X0)
% 2.55/0.98      | v1_xboole_0(X0)
% 2.55/0.98      | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
% 2.55/0.98      inference(unflattening,[status(thm)],[c_311]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_24,negated_conjecture,
% 2.55/0.98      ( v1_zfmisc_1(sK2) ),
% 2.55/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_330,plain,
% 2.55/0.98      ( v1_xboole_0(X0)
% 2.55/0.98      | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.55/0.98      | sK2 != X0 ),
% 2.55/0.98      inference(resolution_lifted,[status(thm)],[c_312,c_24]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_331,plain,
% 2.55/0.98      ( v1_xboole_0(sK2) | k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
% 2.55/0.98      inference(unflattening,[status(thm)],[c_330]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_25,negated_conjecture,
% 2.55/0.98      ( ~ v1_xboole_0(sK2) ),
% 2.55/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_333,plain,
% 2.55/0.98      ( k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
% 2.55/0.98      inference(global_propositional_subsumption,[status(thm)],[c_331,c_25]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_20,plain,
% 2.55/0.98      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK0(X0)) = X0 ),
% 2.55/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_338,plain,
% 2.55/0.98      ( v1_xboole_0(X0) | k6_domain_1(X0,sK0(X0)) = X0 | sK2 != X0 ),
% 2.55/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_339,plain,
% 2.55/0.98      ( v1_xboole_0(sK2) | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
% 2.55/0.98      inference(unflattening,[status(thm)],[c_338]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_341,plain,
% 2.55/0.98      ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
% 2.55/0.98      inference(global_propositional_subsumption,[status(thm)],[c_339,c_25]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_890,plain,
% 2.55/0.98      ( k1_tarski(sK0(sK2)) = sK2 ),
% 2.55/0.98      inference(light_normalisation,[status(thm)],[c_333,c_341]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_17,plain,
% 2.55/0.98      ( ~ r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0 ),
% 2.55/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_859,plain,
% 2.55/0.98      ( k1_tarski(X0) = X1
% 2.55/0.98      | k1_xboole_0 = X1
% 2.55/0.98      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 2.55/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_1965,plain,
% 2.55/0.98      ( k1_tarski(sK0(sK2)) = X0
% 2.55/0.98      | k1_xboole_0 = X0
% 2.55/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 2.55/0.98      inference(superposition,[status(thm)],[c_890,c_859]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_1969,plain,
% 2.55/0.98      ( sK2 = X0 | k1_xboole_0 = X0 | r1_tarski(X0,sK2) != iProver_top ),
% 2.55/0.98      inference(demodulation,[status(thm)],[c_1965,c_890]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_2700,plain,
% 2.55/0.98      ( sK2 = sK1 | sK1 = k1_xboole_0 ),
% 2.55/0.98      inference(superposition,[status(thm)],[c_858,c_1969]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_26,negated_conjecture,
% 2.55/0.98      ( ~ v1_xboole_0(sK1) ),
% 2.55/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_14,plain,
% 2.55/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.55/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_53,plain,
% 2.55/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.55/0.98      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.55/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_13,plain,
% 2.55/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.55/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_56,plain,
% 2.55/0.98      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.55/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.55/0.98      | v1_xboole_0(k1_xboole_0) ),
% 2.55/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_12,plain,
% 2.55/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.55/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_58,plain,
% 2.55/0.98      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.55/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_6,plain,
% 2.55/0.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.55/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_67,plain,
% 2.55/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.55/0.98      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.55/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_493,plain,
% 2.55/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.55/0.98      theory(equality) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_988,plain,
% 2.55/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.55/0.98      inference(instantiation,[status(thm)],[c_493]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_990,plain,
% 2.55/0.98      ( v1_xboole_0(sK1) | ~ v1_xboole_0(k1_xboole_0) | sK1 != k1_xboole_0 ),
% 2.55/0.98      inference(instantiation,[status(thm)],[c_988]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_2706,plain,
% 2.55/0.98      ( sK2 = sK1 ),
% 2.55/0.98      inference(global_propositional_subsumption,
% 2.55/0.98                [status(thm)],
% 2.55/0.98                [c_2700,c_26,c_53,c_56,c_58,c_67,c_990]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_22,negated_conjecture,
% 2.55/0.98      ( sK1 != sK2 ),
% 2.55/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_2717,plain,
% 2.55/0.98      ( sK1 != sK1 ),
% 2.55/0.98      inference(demodulation,[status(thm)],[c_2706,c_22]) ).
% 2.55/0.98  
% 2.55/0.98  cnf(c_2718,plain,
% 2.55/0.98      ( $false ),
% 2.55/0.98      inference(equality_resolution_simp,[status(thm)],[c_2717]) ).
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/0.98  
% 2.55/0.98  ------                               Statistics
% 2.55/0.98  
% 2.55/0.98  ------ General
% 2.55/0.98  
% 2.55/0.98  abstr_ref_over_cycles:                  0
% 2.55/0.98  abstr_ref_under_cycles:                 0
% 2.55/0.98  gc_basic_clause_elim:                   0
% 2.55/0.98  forced_gc_time:                         0
% 2.55/0.98  parsing_time:                           0.01
% 2.55/0.98  unif_index_cands_time:                  0.
% 2.55/0.98  unif_index_add_time:                    0.
% 2.55/0.98  orderings_time:                         0.
% 2.55/0.98  out_proof_time:                         0.013
% 2.55/0.98  total_time:                             0.111
% 2.55/0.98  num_of_symbols:                         44
% 2.55/0.98  num_of_terms:                           2287
% 2.55/0.98  
% 2.55/0.98  ------ Preprocessing
% 2.55/0.98  
% 2.55/0.98  num_of_splits:                          0
% 2.55/0.98  num_of_split_atoms:                     0
% 2.55/0.98  num_of_reused_defs:                     0
% 2.55/0.98  num_eq_ax_congr_red:                    12
% 2.55/0.98  num_of_sem_filtered_clauses:            1
% 2.55/0.98  num_of_subtypes:                        0
% 2.55/0.98  monotx_restored_types:                  0
% 2.55/0.98  sat_num_of_epr_types:                   0
% 2.55/0.98  sat_num_of_non_cyclic_types:            0
% 2.55/0.98  sat_guarded_non_collapsed_types:        0
% 2.55/0.98  num_pure_diseq_elim:                    0
% 2.55/0.98  simp_replaced_by:                       0
% 2.55/0.98  res_preprocessed:                       111
% 2.55/0.98  prep_upred:                             0
% 2.55/0.98  prep_unflattend:                        6
% 2.55/0.98  smt_new_axioms:                         0
% 2.55/0.98  pred_elim_cands:                        2
% 2.55/0.98  pred_elim:                              3
% 2.55/0.98  pred_elim_cl:                           4
% 2.55/0.98  pred_elim_cycles:                       5
% 2.55/0.98  merged_defs:                            8
% 2.55/0.98  merged_defs_ncl:                        0
% 2.55/0.98  bin_hyper_res:                          8
% 2.55/0.98  prep_cycles:                            4
% 2.55/0.98  pred_elim_time:                         0.002
% 2.55/0.98  splitting_time:                         0.
% 2.55/0.98  sem_filter_time:                        0.
% 2.55/0.98  monotx_time:                            0.001
% 2.55/0.98  subtype_inf_time:                       0.
% 2.55/0.98  
% 2.55/0.98  ------ Problem properties
% 2.55/0.98  
% 2.55/0.98  clauses:                                22
% 2.55/0.98  conjectures:                            4
% 2.55/0.98  epr:                                    7
% 2.55/0.98  horn:                                   21
% 2.55/0.98  ground:                                 6
% 2.55/0.98  unary:                                  13
% 2.55/0.98  binary:                                 5
% 2.55/0.98  lits:                                   35
% 2.55/0.98  lits_eq:                                14
% 2.55/0.98  fd_pure:                                0
% 2.55/0.98  fd_pseudo:                              0
% 2.55/0.98  fd_cond:                                0
% 2.55/0.98  fd_pseudo_cond:                         2
% 2.55/0.98  ac_symbols:                             0
% 2.55/0.98  
% 2.55/0.98  ------ Propositional Solver
% 2.55/0.98  
% 2.55/0.98  prop_solver_calls:                      26
% 2.55/0.98  prop_fast_solver_calls:                 459
% 2.55/0.98  smt_solver_calls:                       0
% 2.55/0.98  smt_fast_solver_calls:                  0
% 2.55/0.98  prop_num_of_clauses:                    1010
% 2.55/0.98  prop_preprocess_simplified:             4351
% 2.55/0.98  prop_fo_subsumed:                       5
% 2.55/0.98  prop_solver_time:                       0.
% 2.55/0.98  smt_solver_time:                        0.
% 2.55/0.98  smt_fast_solver_time:                   0.
% 2.55/0.98  prop_fast_solver_time:                  0.
% 2.55/0.98  prop_unsat_core_time:                   0.
% 2.55/0.98  
% 2.55/0.98  ------ QBF
% 2.55/0.98  
% 2.55/0.98  qbf_q_res:                              0
% 2.55/0.98  qbf_num_tautologies:                    0
% 2.55/0.98  qbf_prep_cycles:                        0
% 2.55/0.98  
% 2.55/0.98  ------ BMC1
% 2.55/0.98  
% 2.55/0.98  bmc1_current_bound:                     -1
% 2.55/0.98  bmc1_last_solved_bound:                 -1
% 2.55/0.98  bmc1_unsat_core_size:                   -1
% 2.55/0.98  bmc1_unsat_core_parents_size:           -1
% 2.55/0.98  bmc1_merge_next_fun:                    0
% 2.55/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.55/0.98  
% 2.55/0.98  ------ Instantiation
% 2.55/0.98  
% 2.55/0.98  inst_num_of_clauses:                    323
% 2.55/0.98  inst_num_in_passive:                    137
% 2.55/0.98  inst_num_in_active:                     144
% 2.55/0.98  inst_num_in_unprocessed:                42
% 2.55/0.98  inst_num_of_loops:                      150
% 2.55/0.98  inst_num_of_learning_restarts:          0
% 2.55/0.98  inst_num_moves_active_passive:          5
% 2.55/0.98  inst_lit_activity:                      0
% 2.55/0.98  inst_lit_activity_moves:                0
% 2.55/0.98  inst_num_tautologies:                   0
% 2.55/0.98  inst_num_prop_implied:                  0
% 2.55/0.98  inst_num_existing_simplified:           0
% 2.55/0.98  inst_num_eq_res_simplified:             0
% 2.55/0.98  inst_num_child_elim:                    0
% 2.55/0.98  inst_num_of_dismatching_blockings:      48
% 2.55/0.98  inst_num_of_non_proper_insts:           318
% 2.55/0.98  inst_num_of_duplicates:                 0
% 2.55/0.98  inst_inst_num_from_inst_to_res:         0
% 2.55/0.98  inst_dismatching_checking_time:         0.
% 2.55/0.98  
% 2.55/0.98  ------ Resolution
% 2.55/0.98  
% 2.55/0.98  res_num_of_clauses:                     0
% 2.55/0.98  res_num_in_passive:                     0
% 2.55/0.98  res_num_in_active:                      0
% 2.55/0.98  res_num_of_loops:                       115
% 2.55/0.98  res_forward_subset_subsumed:            32
% 2.55/0.98  res_backward_subset_subsumed:           0
% 2.55/0.98  res_forward_subsumed:                   0
% 2.55/0.98  res_backward_subsumed:                  0
% 2.55/0.98  res_forward_subsumption_resolution:     0
% 2.55/0.98  res_backward_subsumption_resolution:    0
% 2.55/0.98  res_clause_to_clause_subsumption:       92
% 2.55/0.98  res_orphan_elimination:                 0
% 2.55/0.98  res_tautology_del:                      48
% 2.55/0.98  res_num_eq_res_simplified:              0
% 2.55/0.98  res_num_sel_changes:                    0
% 2.55/0.98  res_moves_from_active_to_pass:          0
% 2.55/0.98  
% 2.55/0.98  ------ Superposition
% 2.55/0.98  
% 2.55/0.98  sup_time_total:                         0.
% 2.55/0.98  sup_time_generating:                    0.
% 2.55/0.98  sup_time_sim_full:                      0.
% 2.55/0.98  sup_time_sim_immed:                     0.
% 2.55/0.98  
% 2.55/0.98  sup_num_of_clauses:                     29
% 2.55/0.98  sup_num_in_active:                      20
% 2.55/0.98  sup_num_in_passive:                     9
% 2.55/0.98  sup_num_of_loops:                       29
% 2.55/0.98  sup_fw_superposition:                   37
% 2.55/0.98  sup_bw_superposition:                   8
% 2.55/0.98  sup_immediate_simplified:               9
% 2.55/0.98  sup_given_eliminated:                   0
% 2.55/0.98  comparisons_done:                       0
% 2.55/0.98  comparisons_avoided:                    0
% 2.55/0.98  
% 2.55/0.98  ------ Simplifications
% 2.55/0.98  
% 2.55/0.98  
% 2.55/0.98  sim_fw_subset_subsumed:                 2
% 2.55/0.98  sim_bw_subset_subsumed:                 0
% 2.55/0.98  sim_fw_subsumed:                        5
% 2.55/0.98  sim_bw_subsumed:                        0
% 2.55/0.98  sim_fw_subsumption_res:                 0
% 2.55/0.98  sim_bw_subsumption_res:                 0
% 2.55/0.98  sim_tautology_del:                      4
% 2.55/0.98  sim_eq_tautology_del:                   4
% 2.55/0.98  sim_eq_res_simp:                        0
% 2.55/0.98  sim_fw_demodulated:                     2
% 2.55/0.98  sim_bw_demodulated:                     9
% 2.55/0.98  sim_light_normalised:                   2
% 2.55/0.98  sim_joinable_taut:                      0
% 2.55/0.98  sim_joinable_simp:                      0
% 2.55/0.98  sim_ac_normalised:                      0
% 2.55/0.98  sim_smt_subsumption:                    0
% 2.55/0.98  
%------------------------------------------------------------------------------
