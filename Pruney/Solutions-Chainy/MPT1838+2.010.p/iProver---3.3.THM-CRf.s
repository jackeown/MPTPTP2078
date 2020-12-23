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

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 197 expanded)
%              Number of clauses        :   37 (  55 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  222 ( 812 expanded)
%              Number of equality atoms :   85 ( 225 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK5 != X0
        & r1_tarski(X0,sK5)
        & v1_zfmisc_1(sK5)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r1_tarski(sK4,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( sK4 != sK5
    & r1_tarski(sK4,sK5)
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f43,f42])).

fof(f72,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1647,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,plain,
    ( m1_subset_1(sK3(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_349,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | sK3(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_350,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_26,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_368,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_350,c_26])).

cnf(c_369,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_371,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27])).

cnf(c_22,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_376,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_377,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_379,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_27])).

cnf(c_1682,plain,
    ( k1_tarski(sK3(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_371,c_379])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1649,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3291,plain,
    ( k1_tarski(sK3(sK5)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_1649])).

cnf(c_3295,plain,
    ( sK5 = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3291,c_1682])).

cnf(c_4138,plain,
    ( sK5 = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1647,c_3295])).

cnf(c_24,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4265,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4138,c_24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_405,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_406,plain,
    ( r2_hidden(sK0(sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1644,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_4277,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4265,c_1644])).

cnf(c_15,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1653,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2654,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1653])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1648,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3702,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_1648])).

cnf(c_6397,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4277,c_3702])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:40:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.86/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.01  
% 2.86/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/1.01  
% 2.86/1.01  ------  iProver source info
% 2.86/1.01  
% 2.86/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.86/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/1.01  git: non_committed_changes: false
% 2.86/1.01  git: last_make_outside_of_git: false
% 2.86/1.01  
% 2.86/1.01  ------ 
% 2.86/1.01  
% 2.86/1.01  ------ Input Options
% 2.86/1.01  
% 2.86/1.01  --out_options                           all
% 2.86/1.01  --tptp_safe_out                         true
% 2.86/1.01  --problem_path                          ""
% 2.86/1.01  --include_path                          ""
% 2.86/1.01  --clausifier                            res/vclausify_rel
% 2.86/1.01  --clausifier_options                    --mode clausify
% 2.86/1.01  --stdin                                 false
% 2.86/1.01  --stats_out                             all
% 2.86/1.01  
% 2.86/1.01  ------ General Options
% 2.86/1.01  
% 2.86/1.01  --fof                                   false
% 2.86/1.01  --time_out_real                         305.
% 2.86/1.01  --time_out_virtual                      -1.
% 2.86/1.01  --symbol_type_check                     false
% 2.86/1.01  --clausify_out                          false
% 2.86/1.01  --sig_cnt_out                           false
% 2.86/1.01  --trig_cnt_out                          false
% 2.86/1.01  --trig_cnt_out_tolerance                1.
% 2.86/1.01  --trig_cnt_out_sk_spl                   false
% 2.86/1.01  --abstr_cl_out                          false
% 2.86/1.01  
% 2.86/1.01  ------ Global Options
% 2.86/1.01  
% 2.86/1.01  --schedule                              default
% 2.86/1.01  --add_important_lit                     false
% 2.86/1.01  --prop_solver_per_cl                    1000
% 2.86/1.01  --min_unsat_core                        false
% 2.86/1.01  --soft_assumptions                      false
% 2.86/1.01  --soft_lemma_size                       3
% 2.86/1.01  --prop_impl_unit_size                   0
% 2.86/1.01  --prop_impl_unit                        []
% 2.86/1.01  --share_sel_clauses                     true
% 2.86/1.01  --reset_solvers                         false
% 2.86/1.01  --bc_imp_inh                            [conj_cone]
% 2.86/1.01  --conj_cone_tolerance                   3.
% 2.86/1.01  --extra_neg_conj                        none
% 2.86/1.01  --large_theory_mode                     true
% 2.86/1.01  --prolific_symb_bound                   200
% 2.86/1.01  --lt_threshold                          2000
% 2.86/1.01  --clause_weak_htbl                      true
% 2.86/1.01  --gc_record_bc_elim                     false
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing Options
% 2.86/1.01  
% 2.86/1.01  --preprocessing_flag                    true
% 2.86/1.01  --time_out_prep_mult                    0.1
% 2.86/1.01  --splitting_mode                        input
% 2.86/1.01  --splitting_grd                         true
% 2.86/1.01  --splitting_cvd                         false
% 2.86/1.01  --splitting_cvd_svl                     false
% 2.86/1.01  --splitting_nvd                         32
% 2.86/1.01  --sub_typing                            true
% 2.86/1.01  --prep_gs_sim                           true
% 2.86/1.01  --prep_unflatten                        true
% 2.86/1.01  --prep_res_sim                          true
% 2.86/1.01  --prep_upred                            true
% 2.86/1.01  --prep_sem_filter                       exhaustive
% 2.86/1.01  --prep_sem_filter_out                   false
% 2.86/1.01  --pred_elim                             true
% 2.86/1.01  --res_sim_input                         true
% 2.86/1.01  --eq_ax_congr_red                       true
% 2.86/1.01  --pure_diseq_elim                       true
% 2.86/1.01  --brand_transform                       false
% 2.86/1.01  --non_eq_to_eq                          false
% 2.86/1.01  --prep_def_merge                        true
% 2.86/1.01  --prep_def_merge_prop_impl              false
% 2.86/1.01  --prep_def_merge_mbd                    true
% 2.86/1.01  --prep_def_merge_tr_red                 false
% 2.86/1.01  --prep_def_merge_tr_cl                  false
% 2.86/1.01  --smt_preprocessing                     true
% 2.86/1.01  --smt_ac_axioms                         fast
% 2.86/1.01  --preprocessed_out                      false
% 2.86/1.01  --preprocessed_stats                    false
% 2.86/1.01  
% 2.86/1.01  ------ Abstraction refinement Options
% 2.86/1.01  
% 2.86/1.01  --abstr_ref                             []
% 2.86/1.01  --abstr_ref_prep                        false
% 2.86/1.01  --abstr_ref_until_sat                   false
% 2.86/1.01  --abstr_ref_sig_restrict                funpre
% 2.86/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/1.01  --abstr_ref_under                       []
% 2.86/1.01  
% 2.86/1.01  ------ SAT Options
% 2.86/1.01  
% 2.86/1.01  --sat_mode                              false
% 2.86/1.01  --sat_fm_restart_options                ""
% 2.86/1.01  --sat_gr_def                            false
% 2.86/1.01  --sat_epr_types                         true
% 2.86/1.01  --sat_non_cyclic_types                  false
% 2.86/1.01  --sat_finite_models                     false
% 2.86/1.01  --sat_fm_lemmas                         false
% 2.86/1.01  --sat_fm_prep                           false
% 2.86/1.01  --sat_fm_uc_incr                        true
% 2.86/1.01  --sat_out_model                         small
% 2.86/1.01  --sat_out_clauses                       false
% 2.86/1.01  
% 2.86/1.01  ------ QBF Options
% 2.86/1.01  
% 2.86/1.01  --qbf_mode                              false
% 2.86/1.01  --qbf_elim_univ                         false
% 2.86/1.01  --qbf_dom_inst                          none
% 2.86/1.01  --qbf_dom_pre_inst                      false
% 2.86/1.01  --qbf_sk_in                             false
% 2.86/1.01  --qbf_pred_elim                         true
% 2.86/1.01  --qbf_split                             512
% 2.86/1.01  
% 2.86/1.01  ------ BMC1 Options
% 2.86/1.01  
% 2.86/1.01  --bmc1_incremental                      false
% 2.86/1.01  --bmc1_axioms                           reachable_all
% 2.86/1.01  --bmc1_min_bound                        0
% 2.86/1.01  --bmc1_max_bound                        -1
% 2.86/1.01  --bmc1_max_bound_default                -1
% 2.86/1.01  --bmc1_symbol_reachability              true
% 2.86/1.01  --bmc1_property_lemmas                  false
% 2.86/1.01  --bmc1_k_induction                      false
% 2.86/1.01  --bmc1_non_equiv_states                 false
% 2.86/1.01  --bmc1_deadlock                         false
% 2.86/1.01  --bmc1_ucm                              false
% 2.86/1.01  --bmc1_add_unsat_core                   none
% 2.86/1.01  --bmc1_unsat_core_children              false
% 2.86/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/1.01  --bmc1_out_stat                         full
% 2.86/1.01  --bmc1_ground_init                      false
% 2.86/1.01  --bmc1_pre_inst_next_state              false
% 2.86/1.01  --bmc1_pre_inst_state                   false
% 2.86/1.01  --bmc1_pre_inst_reach_state             false
% 2.86/1.01  --bmc1_out_unsat_core                   false
% 2.86/1.01  --bmc1_aig_witness_out                  false
% 2.86/1.01  --bmc1_verbose                          false
% 2.86/1.01  --bmc1_dump_clauses_tptp                false
% 2.86/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.86/1.01  --bmc1_dump_file                        -
% 2.86/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.86/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.86/1.01  --bmc1_ucm_extend_mode                  1
% 2.86/1.01  --bmc1_ucm_init_mode                    2
% 2.86/1.01  --bmc1_ucm_cone_mode                    none
% 2.86/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.86/1.01  --bmc1_ucm_relax_model                  4
% 2.86/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.86/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/1.01  --bmc1_ucm_layered_model                none
% 2.86/1.01  --bmc1_ucm_max_lemma_size               10
% 2.86/1.01  
% 2.86/1.01  ------ AIG Options
% 2.86/1.01  
% 2.86/1.01  --aig_mode                              false
% 2.86/1.01  
% 2.86/1.01  ------ Instantiation Options
% 2.86/1.01  
% 2.86/1.01  --instantiation_flag                    true
% 2.86/1.01  --inst_sos_flag                         false
% 2.86/1.01  --inst_sos_phase                        true
% 2.86/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/1.01  --inst_lit_sel_side                     num_symb
% 2.86/1.01  --inst_solver_per_active                1400
% 2.86/1.01  --inst_solver_calls_frac                1.
% 2.86/1.01  --inst_passive_queue_type               priority_queues
% 2.86/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/1.01  --inst_passive_queues_freq              [25;2]
% 2.86/1.01  --inst_dismatching                      true
% 2.86/1.01  --inst_eager_unprocessed_to_passive     true
% 2.86/1.01  --inst_prop_sim_given                   true
% 2.86/1.01  --inst_prop_sim_new                     false
% 2.86/1.01  --inst_subs_new                         false
% 2.86/1.01  --inst_eq_res_simp                      false
% 2.86/1.01  --inst_subs_given                       false
% 2.86/1.01  --inst_orphan_elimination               true
% 2.86/1.01  --inst_learning_loop_flag               true
% 2.86/1.01  --inst_learning_start                   3000
% 2.86/1.01  --inst_learning_factor                  2
% 2.86/1.01  --inst_start_prop_sim_after_learn       3
% 2.86/1.01  --inst_sel_renew                        solver
% 2.86/1.01  --inst_lit_activity_flag                true
% 2.86/1.01  --inst_restr_to_given                   false
% 2.86/1.01  --inst_activity_threshold               500
% 2.86/1.01  --inst_out_proof                        true
% 2.86/1.01  
% 2.86/1.01  ------ Resolution Options
% 2.86/1.01  
% 2.86/1.01  --resolution_flag                       true
% 2.86/1.01  --res_lit_sel                           adaptive
% 2.86/1.01  --res_lit_sel_side                      none
% 2.86/1.01  --res_ordering                          kbo
% 2.86/1.01  --res_to_prop_solver                    active
% 2.86/1.01  --res_prop_simpl_new                    false
% 2.86/1.01  --res_prop_simpl_given                  true
% 2.86/1.01  --res_passive_queue_type                priority_queues
% 2.86/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/1.01  --res_passive_queues_freq               [15;5]
% 2.86/1.01  --res_forward_subs                      full
% 2.86/1.01  --res_backward_subs                     full
% 2.86/1.01  --res_forward_subs_resolution           true
% 2.86/1.01  --res_backward_subs_resolution          true
% 2.86/1.01  --res_orphan_elimination                true
% 2.86/1.01  --res_time_limit                        2.
% 2.86/1.01  --res_out_proof                         true
% 2.86/1.01  
% 2.86/1.01  ------ Superposition Options
% 2.86/1.01  
% 2.86/1.01  --superposition_flag                    true
% 2.86/1.01  --sup_passive_queue_type                priority_queues
% 2.86/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.86/1.01  --demod_completeness_check              fast
% 2.86/1.01  --demod_use_ground                      true
% 2.86/1.01  --sup_to_prop_solver                    passive
% 2.86/1.01  --sup_prop_simpl_new                    true
% 2.86/1.01  --sup_prop_simpl_given                  true
% 2.86/1.01  --sup_fun_splitting                     false
% 2.86/1.01  --sup_smt_interval                      50000
% 2.86/1.01  
% 2.86/1.01  ------ Superposition Simplification Setup
% 2.86/1.01  
% 2.86/1.01  --sup_indices_passive                   []
% 2.86/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.01  --sup_full_bw                           [BwDemod]
% 2.86/1.01  --sup_immed_triv                        [TrivRules]
% 2.86/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.01  --sup_immed_bw_main                     []
% 2.86/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.01  
% 2.86/1.01  ------ Combination Options
% 2.86/1.01  
% 2.86/1.01  --comb_res_mult                         3
% 2.86/1.01  --comb_sup_mult                         2
% 2.86/1.01  --comb_inst_mult                        10
% 2.86/1.01  
% 2.86/1.01  ------ Debug Options
% 2.86/1.01  
% 2.86/1.01  --dbg_backtrace                         false
% 2.86/1.01  --dbg_dump_prop_clauses                 false
% 2.86/1.01  --dbg_dump_prop_clauses_file            -
% 2.86/1.01  --dbg_out_stat                          false
% 2.86/1.01  ------ Parsing...
% 2.86/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.86/1.01  ------ Proving...
% 2.86/1.01  ------ Problem Properties 
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  clauses                                 25
% 2.86/1.01  conjectures                             2
% 2.86/1.01  EPR                                     4
% 2.86/1.01  Horn                                    21
% 2.86/1.01  unary                                   10
% 2.86/1.01  binary                                  9
% 2.86/1.01  lits                                    47
% 2.86/1.01  lits eq                                 13
% 2.86/1.01  fd_pure                                 0
% 2.86/1.01  fd_pseudo                               0
% 2.86/1.01  fd_cond                                 0
% 2.86/1.01  fd_pseudo_cond                          4
% 2.86/1.01  AC symbols                              0
% 2.86/1.01  
% 2.86/1.01  ------ Schedule dynamic 5 is on 
% 2.86/1.01  
% 2.86/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  ------ 
% 2.86/1.01  Current options:
% 2.86/1.01  ------ 
% 2.86/1.01  
% 2.86/1.01  ------ Input Options
% 2.86/1.01  
% 2.86/1.01  --out_options                           all
% 2.86/1.01  --tptp_safe_out                         true
% 2.86/1.01  --problem_path                          ""
% 2.86/1.01  --include_path                          ""
% 2.86/1.01  --clausifier                            res/vclausify_rel
% 2.86/1.01  --clausifier_options                    --mode clausify
% 2.86/1.01  --stdin                                 false
% 2.86/1.01  --stats_out                             all
% 2.86/1.01  
% 2.86/1.01  ------ General Options
% 2.86/1.01  
% 2.86/1.01  --fof                                   false
% 2.86/1.01  --time_out_real                         305.
% 2.86/1.01  --time_out_virtual                      -1.
% 2.86/1.01  --symbol_type_check                     false
% 2.86/1.01  --clausify_out                          false
% 2.86/1.01  --sig_cnt_out                           false
% 2.86/1.01  --trig_cnt_out                          false
% 2.86/1.01  --trig_cnt_out_tolerance                1.
% 2.86/1.01  --trig_cnt_out_sk_spl                   false
% 2.86/1.01  --abstr_cl_out                          false
% 2.86/1.01  
% 2.86/1.01  ------ Global Options
% 2.86/1.01  
% 2.86/1.01  --schedule                              default
% 2.86/1.01  --add_important_lit                     false
% 2.86/1.01  --prop_solver_per_cl                    1000
% 2.86/1.01  --min_unsat_core                        false
% 2.86/1.01  --soft_assumptions                      false
% 2.86/1.01  --soft_lemma_size                       3
% 2.86/1.01  --prop_impl_unit_size                   0
% 2.86/1.01  --prop_impl_unit                        []
% 2.86/1.01  --share_sel_clauses                     true
% 2.86/1.01  --reset_solvers                         false
% 2.86/1.01  --bc_imp_inh                            [conj_cone]
% 2.86/1.01  --conj_cone_tolerance                   3.
% 2.86/1.01  --extra_neg_conj                        none
% 2.86/1.01  --large_theory_mode                     true
% 2.86/1.01  --prolific_symb_bound                   200
% 2.86/1.01  --lt_threshold                          2000
% 2.86/1.01  --clause_weak_htbl                      true
% 2.86/1.01  --gc_record_bc_elim                     false
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing Options
% 2.86/1.01  
% 2.86/1.01  --preprocessing_flag                    true
% 2.86/1.01  --time_out_prep_mult                    0.1
% 2.86/1.01  --splitting_mode                        input
% 2.86/1.01  --splitting_grd                         true
% 2.86/1.01  --splitting_cvd                         false
% 2.86/1.01  --splitting_cvd_svl                     false
% 2.86/1.01  --splitting_nvd                         32
% 2.86/1.01  --sub_typing                            true
% 2.86/1.01  --prep_gs_sim                           true
% 2.86/1.01  --prep_unflatten                        true
% 2.86/1.01  --prep_res_sim                          true
% 2.86/1.01  --prep_upred                            true
% 2.86/1.01  --prep_sem_filter                       exhaustive
% 2.86/1.01  --prep_sem_filter_out                   false
% 2.86/1.01  --pred_elim                             true
% 2.86/1.01  --res_sim_input                         true
% 2.86/1.01  --eq_ax_congr_red                       true
% 2.86/1.01  --pure_diseq_elim                       true
% 2.86/1.01  --brand_transform                       false
% 2.86/1.01  --non_eq_to_eq                          false
% 2.86/1.01  --prep_def_merge                        true
% 2.86/1.01  --prep_def_merge_prop_impl              false
% 2.86/1.01  --prep_def_merge_mbd                    true
% 2.86/1.01  --prep_def_merge_tr_red                 false
% 2.86/1.01  --prep_def_merge_tr_cl                  false
% 2.86/1.01  --smt_preprocessing                     true
% 2.86/1.01  --smt_ac_axioms                         fast
% 2.86/1.01  --preprocessed_out                      false
% 2.86/1.01  --preprocessed_stats                    false
% 2.86/1.01  
% 2.86/1.01  ------ Abstraction refinement Options
% 2.86/1.01  
% 2.86/1.01  --abstr_ref                             []
% 2.86/1.01  --abstr_ref_prep                        false
% 2.86/1.01  --abstr_ref_until_sat                   false
% 2.86/1.01  --abstr_ref_sig_restrict                funpre
% 2.86/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/1.01  --abstr_ref_under                       []
% 2.86/1.01  
% 2.86/1.01  ------ SAT Options
% 2.86/1.01  
% 2.86/1.01  --sat_mode                              false
% 2.86/1.01  --sat_fm_restart_options                ""
% 2.86/1.01  --sat_gr_def                            false
% 2.86/1.01  --sat_epr_types                         true
% 2.86/1.01  --sat_non_cyclic_types                  false
% 2.86/1.01  --sat_finite_models                     false
% 2.86/1.01  --sat_fm_lemmas                         false
% 2.86/1.01  --sat_fm_prep                           false
% 2.86/1.01  --sat_fm_uc_incr                        true
% 2.86/1.01  --sat_out_model                         small
% 2.86/1.01  --sat_out_clauses                       false
% 2.86/1.01  
% 2.86/1.01  ------ QBF Options
% 2.86/1.01  
% 2.86/1.01  --qbf_mode                              false
% 2.86/1.01  --qbf_elim_univ                         false
% 2.86/1.01  --qbf_dom_inst                          none
% 2.86/1.01  --qbf_dom_pre_inst                      false
% 2.86/1.01  --qbf_sk_in                             false
% 2.86/1.01  --qbf_pred_elim                         true
% 2.86/1.01  --qbf_split                             512
% 2.86/1.01  
% 2.86/1.01  ------ BMC1 Options
% 2.86/1.01  
% 2.86/1.01  --bmc1_incremental                      false
% 2.86/1.01  --bmc1_axioms                           reachable_all
% 2.86/1.01  --bmc1_min_bound                        0
% 2.86/1.01  --bmc1_max_bound                        -1
% 2.86/1.01  --bmc1_max_bound_default                -1
% 2.86/1.01  --bmc1_symbol_reachability              true
% 2.86/1.01  --bmc1_property_lemmas                  false
% 2.86/1.01  --bmc1_k_induction                      false
% 2.86/1.01  --bmc1_non_equiv_states                 false
% 2.86/1.01  --bmc1_deadlock                         false
% 2.86/1.01  --bmc1_ucm                              false
% 2.86/1.01  --bmc1_add_unsat_core                   none
% 2.86/1.01  --bmc1_unsat_core_children              false
% 2.86/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/1.01  --bmc1_out_stat                         full
% 2.86/1.01  --bmc1_ground_init                      false
% 2.86/1.01  --bmc1_pre_inst_next_state              false
% 2.86/1.01  --bmc1_pre_inst_state                   false
% 2.86/1.01  --bmc1_pre_inst_reach_state             false
% 2.86/1.01  --bmc1_out_unsat_core                   false
% 2.86/1.01  --bmc1_aig_witness_out                  false
% 2.86/1.01  --bmc1_verbose                          false
% 2.86/1.01  --bmc1_dump_clauses_tptp                false
% 2.86/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.86/1.01  --bmc1_dump_file                        -
% 2.86/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.86/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.86/1.01  --bmc1_ucm_extend_mode                  1
% 2.86/1.01  --bmc1_ucm_init_mode                    2
% 2.86/1.01  --bmc1_ucm_cone_mode                    none
% 2.86/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.86/1.01  --bmc1_ucm_relax_model                  4
% 2.86/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.86/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/1.01  --bmc1_ucm_layered_model                none
% 2.86/1.01  --bmc1_ucm_max_lemma_size               10
% 2.86/1.01  
% 2.86/1.01  ------ AIG Options
% 2.86/1.01  
% 2.86/1.01  --aig_mode                              false
% 2.86/1.01  
% 2.86/1.01  ------ Instantiation Options
% 2.86/1.01  
% 2.86/1.01  --instantiation_flag                    true
% 2.86/1.01  --inst_sos_flag                         false
% 2.86/1.01  --inst_sos_phase                        true
% 2.86/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/1.01  --inst_lit_sel_side                     none
% 2.86/1.01  --inst_solver_per_active                1400
% 2.86/1.01  --inst_solver_calls_frac                1.
% 2.86/1.01  --inst_passive_queue_type               priority_queues
% 2.86/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/1.01  --inst_passive_queues_freq              [25;2]
% 2.86/1.01  --inst_dismatching                      true
% 2.86/1.01  --inst_eager_unprocessed_to_passive     true
% 2.86/1.01  --inst_prop_sim_given                   true
% 2.86/1.01  --inst_prop_sim_new                     false
% 2.86/1.01  --inst_subs_new                         false
% 2.86/1.01  --inst_eq_res_simp                      false
% 2.86/1.01  --inst_subs_given                       false
% 2.86/1.01  --inst_orphan_elimination               true
% 2.86/1.01  --inst_learning_loop_flag               true
% 2.86/1.01  --inst_learning_start                   3000
% 2.86/1.01  --inst_learning_factor                  2
% 2.86/1.01  --inst_start_prop_sim_after_learn       3
% 2.86/1.01  --inst_sel_renew                        solver
% 2.86/1.01  --inst_lit_activity_flag                true
% 2.86/1.01  --inst_restr_to_given                   false
% 2.86/1.01  --inst_activity_threshold               500
% 2.86/1.01  --inst_out_proof                        true
% 2.86/1.01  
% 2.86/1.01  ------ Resolution Options
% 2.86/1.01  
% 2.86/1.01  --resolution_flag                       false
% 2.86/1.01  --res_lit_sel                           adaptive
% 2.86/1.01  --res_lit_sel_side                      none
% 2.86/1.01  --res_ordering                          kbo
% 2.86/1.01  --res_to_prop_solver                    active
% 2.86/1.01  --res_prop_simpl_new                    false
% 2.86/1.01  --res_prop_simpl_given                  true
% 2.86/1.01  --res_passive_queue_type                priority_queues
% 2.86/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/1.01  --res_passive_queues_freq               [15;5]
% 2.86/1.01  --res_forward_subs                      full
% 2.86/1.01  --res_backward_subs                     full
% 2.86/1.01  --res_forward_subs_resolution           true
% 2.86/1.01  --res_backward_subs_resolution          true
% 2.86/1.01  --res_orphan_elimination                true
% 2.86/1.01  --res_time_limit                        2.
% 2.86/1.01  --res_out_proof                         true
% 2.86/1.01  
% 2.86/1.01  ------ Superposition Options
% 2.86/1.01  
% 2.86/1.01  --superposition_flag                    true
% 2.86/1.01  --sup_passive_queue_type                priority_queues
% 2.86/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.86/1.01  --demod_completeness_check              fast
% 2.86/1.01  --demod_use_ground                      true
% 2.86/1.01  --sup_to_prop_solver                    passive
% 2.86/1.01  --sup_prop_simpl_new                    true
% 2.86/1.01  --sup_prop_simpl_given                  true
% 2.86/1.01  --sup_fun_splitting                     false
% 2.86/1.01  --sup_smt_interval                      50000
% 2.86/1.01  
% 2.86/1.01  ------ Superposition Simplification Setup
% 2.86/1.01  
% 2.86/1.01  --sup_indices_passive                   []
% 2.86/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.01  --sup_full_bw                           [BwDemod]
% 2.86/1.01  --sup_immed_triv                        [TrivRules]
% 2.86/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.01  --sup_immed_bw_main                     []
% 2.86/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/1.01  
% 2.86/1.01  ------ Combination Options
% 2.86/1.01  
% 2.86/1.01  --comb_res_mult                         3
% 2.86/1.01  --comb_sup_mult                         2
% 2.86/1.01  --comb_inst_mult                        10
% 2.86/1.01  
% 2.86/1.01  ------ Debug Options
% 2.86/1.01  
% 2.86/1.01  --dbg_backtrace                         false
% 2.86/1.01  --dbg_dump_prop_clauses                 false
% 2.86/1.01  --dbg_dump_prop_clauses_file            -
% 2.86/1.01  --dbg_out_stat                          false
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  ------ Proving...
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  % SZS status Theorem for theBenchmark.p
% 2.86/1.01  
% 2.86/1.01   Resolution empty clause
% 2.86/1.01  
% 2.86/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/1.01  
% 2.86/1.01  fof(f12,conjecture,(
% 2.86/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f13,negated_conjecture,(
% 2.86/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.86/1.01    inference(negated_conjecture,[],[f12])).
% 2.86/1.01  
% 2.86/1.01  fof(f20,plain,(
% 2.86/1.01    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 2.86/1.01    inference(ennf_transformation,[],[f13])).
% 2.86/1.01  
% 2.86/1.01  fof(f21,plain,(
% 2.86/1.01    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.86/1.01    inference(flattening,[],[f20])).
% 2.86/1.01  
% 2.86/1.01  fof(f43,plain,(
% 2.86/1.01    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK5 != X0 & r1_tarski(X0,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))) )),
% 2.86/1.01    introduced(choice_axiom,[])).
% 2.86/1.01  
% 2.86/1.01  fof(f42,plain,(
% 2.86/1.01    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK4 != X1 & r1_tarski(sK4,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 2.86/1.01    introduced(choice_axiom,[])).
% 2.86/1.01  
% 2.86/1.01  fof(f44,plain,(
% 2.86/1.01    (sK4 != sK5 & r1_tarski(sK4,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 2.86/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f43,f42])).
% 2.86/1.01  
% 2.86/1.01  fof(f72,plain,(
% 2.86/1.01    r1_tarski(sK4,sK5)),
% 2.86/1.01    inference(cnf_transformation,[],[f44])).
% 2.86/1.01  
% 2.86/1.01  fof(f10,axiom,(
% 2.86/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f17,plain,(
% 2.86/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.86/1.01    inference(ennf_transformation,[],[f10])).
% 2.86/1.01  
% 2.86/1.01  fof(f18,plain,(
% 2.86/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.86/1.01    inference(flattening,[],[f17])).
% 2.86/1.01  
% 2.86/1.01  fof(f65,plain,(
% 2.86/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f18])).
% 2.86/1.01  
% 2.86/1.01  fof(f11,axiom,(
% 2.86/1.01    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f19,plain,(
% 2.86/1.01    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.86/1.01    inference(ennf_transformation,[],[f11])).
% 2.86/1.01  
% 2.86/1.01  fof(f38,plain,(
% 2.86/1.01    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.86/1.01    inference(nnf_transformation,[],[f19])).
% 2.86/1.01  
% 2.86/1.01  fof(f39,plain,(
% 2.86/1.01    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.86/1.01    inference(rectify,[],[f38])).
% 2.86/1.01  
% 2.86/1.01  fof(f40,plain,(
% 2.86/1.01    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 2.86/1.01    introduced(choice_axiom,[])).
% 2.86/1.01  
% 2.86/1.01  fof(f41,plain,(
% 2.86/1.01    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.86/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.86/1.01  
% 2.86/1.01  fof(f66,plain,(
% 2.86/1.01    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f41])).
% 2.86/1.01  
% 2.86/1.01  fof(f71,plain,(
% 2.86/1.01    v1_zfmisc_1(sK5)),
% 2.86/1.01    inference(cnf_transformation,[],[f44])).
% 2.86/1.01  
% 2.86/1.01  fof(f70,plain,(
% 2.86/1.01    ~v1_xboole_0(sK5)),
% 2.86/1.01    inference(cnf_transformation,[],[f44])).
% 2.86/1.01  
% 2.86/1.01  fof(f67,plain,(
% 2.86/1.01    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f41])).
% 2.86/1.01  
% 2.86/1.01  fof(f8,axiom,(
% 2.86/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f36,plain,(
% 2.86/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.86/1.01    inference(nnf_transformation,[],[f8])).
% 2.86/1.01  
% 2.86/1.01  fof(f37,plain,(
% 2.86/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.86/1.01    inference(flattening,[],[f36])).
% 2.86/1.01  
% 2.86/1.01  fof(f61,plain,(
% 2.86/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.86/1.01    inference(cnf_transformation,[],[f37])).
% 2.86/1.01  
% 2.86/1.01  fof(f73,plain,(
% 2.86/1.01    sK4 != sK5),
% 2.86/1.01    inference(cnf_transformation,[],[f44])).
% 2.86/1.01  
% 2.86/1.01  fof(f2,axiom,(
% 2.86/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f22,plain,(
% 2.86/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.86/1.01    inference(nnf_transformation,[],[f2])).
% 2.86/1.01  
% 2.86/1.01  fof(f23,plain,(
% 2.86/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.86/1.01    inference(rectify,[],[f22])).
% 2.86/1.01  
% 2.86/1.01  fof(f24,plain,(
% 2.86/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.86/1.01    introduced(choice_axiom,[])).
% 2.86/1.01  
% 2.86/1.01  fof(f25,plain,(
% 2.86/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.86/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.86/1.01  
% 2.86/1.01  fof(f47,plain,(
% 2.86/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f25])).
% 2.86/1.01  
% 2.86/1.01  fof(f69,plain,(
% 2.86/1.01    ~v1_xboole_0(sK4)),
% 2.86/1.01    inference(cnf_transformation,[],[f44])).
% 2.86/1.01  
% 2.86/1.01  fof(f7,axiom,(
% 2.86/1.01    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f60,plain,(
% 2.86/1.01    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 2.86/1.01    inference(cnf_transformation,[],[f7])).
% 2.86/1.01  
% 2.86/1.01  fof(f5,axiom,(
% 2.86/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f35,plain,(
% 2.86/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.86/1.01    inference(nnf_transformation,[],[f5])).
% 2.86/1.01  
% 2.86/1.01  fof(f57,plain,(
% 2.86/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.86/1.01    inference(cnf_transformation,[],[f35])).
% 2.86/1.01  
% 2.86/1.01  fof(f9,axiom,(
% 2.86/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.86/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/1.01  
% 2.86/1.01  fof(f16,plain,(
% 2.86/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.86/1.01    inference(ennf_transformation,[],[f9])).
% 2.86/1.01  
% 2.86/1.01  fof(f64,plain,(
% 2.86/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.86/1.01    inference(cnf_transformation,[],[f16])).
% 2.86/1.01  
% 2.86/1.01  cnf(c_25,negated_conjecture,
% 2.86/1.01      ( r1_tarski(sK4,sK5) ),
% 2.86/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1647,plain,
% 2.86/1.01      ( r1_tarski(sK4,sK5) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_20,plain,
% 2.86/1.01      ( ~ m1_subset_1(X0,X1)
% 2.86/1.01      | v1_xboole_0(X1)
% 2.86/1.01      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_23,plain,
% 2.86/1.01      ( m1_subset_1(sK3(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_349,plain,
% 2.86/1.01      ( ~ v1_zfmisc_1(X0)
% 2.86/1.01      | v1_xboole_0(X1)
% 2.86/1.01      | v1_xboole_0(X0)
% 2.86/1.01      | X0 != X1
% 2.86/1.01      | k6_domain_1(X1,X2) = k1_tarski(X2)
% 2.86/1.01      | sK3(X0) != X2 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_350,plain,
% 2.86/1.01      ( ~ v1_zfmisc_1(X0)
% 2.86/1.01      | v1_xboole_0(X0)
% 2.86/1.01      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_349]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_26,negated_conjecture,
% 2.86/1.01      ( v1_zfmisc_1(sK5) ),
% 2.86/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_368,plain,
% 2.86/1.01      ( v1_xboole_0(X0)
% 2.86/1.01      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
% 2.86/1.01      | sK5 != X0 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_350,c_26]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_369,plain,
% 2.86/1.01      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_368]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_27,negated_conjecture,
% 2.86/1.01      ( ~ v1_xboole_0(sK5) ),
% 2.86/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_371,plain,
% 2.86/1.01      ( k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 2.86/1.01      inference(global_propositional_subsumption,[status(thm)],[c_369,c_27]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_22,plain,
% 2.86/1.01      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 ),
% 2.86/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_376,plain,
% 2.86/1.01      ( v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | sK5 != X0 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_377,plain,
% 2.86/1.01      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_376]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_379,plain,
% 2.86/1.01      ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 2.86/1.01      inference(global_propositional_subsumption,[status(thm)],[c_377,c_27]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1682,plain,
% 2.86/1.01      ( k1_tarski(sK3(sK5)) = sK5 ),
% 2.86/1.01      inference(light_normalisation,[status(thm)],[c_371,c_379]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_18,plain,
% 2.86/1.01      ( ~ r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0 ),
% 2.86/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1649,plain,
% 2.86/1.01      ( k1_tarski(X0) = X1
% 2.86/1.01      | k1_xboole_0 = X1
% 2.86/1.01      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_3291,plain,
% 2.86/1.01      ( k1_tarski(sK3(sK5)) = X0
% 2.86/1.01      | k1_xboole_0 = X0
% 2.86/1.01      | r1_tarski(X0,sK5) != iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_1682,c_1649]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_3295,plain,
% 2.86/1.01      ( sK5 = X0 | k1_xboole_0 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 2.86/1.01      inference(demodulation,[status(thm)],[c_3291,c_1682]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_4138,plain,
% 2.86/1.01      ( sK5 = sK4 | sK4 = k1_xboole_0 ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_1647,c_3295]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_24,negated_conjecture,
% 2.86/1.01      ( sK4 != sK5 ),
% 2.86/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_4265,plain,
% 2.86/1.01      ( sK4 = k1_xboole_0 ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_4138,c_24]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1,plain,
% 2.86/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_28,negated_conjecture,
% 2.86/1.01      ( ~ v1_xboole_0(sK4) ),
% 2.86/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_405,plain,
% 2.86/1.01      ( r2_hidden(sK0(X0),X0) | sK4 != X0 ),
% 2.86/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_406,plain,
% 2.86/1.01      ( r2_hidden(sK0(sK4),sK4) ),
% 2.86/1.01      inference(unflattening,[status(thm)],[c_405]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1644,plain,
% 2.86/1.01      ( r2_hidden(sK0(sK4),sK4) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_4277,plain,
% 2.86/1.01      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.86/1.01      inference(demodulation,[status(thm)],[c_4265,c_1644]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_15,plain,
% 2.86/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.86/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_13,plain,
% 2.86/1.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.86/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1653,plain,
% 2.86/1.01      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_2654,plain,
% 2.86/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_15,c_1653]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_19,plain,
% 2.86/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.86/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_1648,plain,
% 2.86/1.01      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 2.86/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_3702,plain,
% 2.86/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_2654,c_1648]) ).
% 2.86/1.01  
% 2.86/1.01  cnf(c_6397,plain,
% 2.86/1.01      ( $false ),
% 2.86/1.01      inference(superposition,[status(thm)],[c_4277,c_3702]) ).
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/1.01  
% 2.86/1.01  ------                               Statistics
% 2.86/1.01  
% 2.86/1.01  ------ General
% 2.86/1.01  
% 2.86/1.01  abstr_ref_over_cycles:                  0
% 2.86/1.01  abstr_ref_under_cycles:                 0
% 2.86/1.01  gc_basic_clause_elim:                   0
% 2.86/1.01  forced_gc_time:                         0
% 2.86/1.01  parsing_time:                           0.012
% 2.86/1.01  unif_index_cands_time:                  0.
% 2.86/1.01  unif_index_add_time:                    0.
% 2.86/1.01  orderings_time:                         0.
% 2.86/1.01  out_proof_time:                         0.011
% 2.86/1.01  total_time:                             0.231
% 2.86/1.01  num_of_symbols:                         47
% 2.86/1.01  num_of_terms:                           5986
% 2.86/1.01  
% 2.86/1.01  ------ Preprocessing
% 2.86/1.01  
% 2.86/1.01  num_of_splits:                          0
% 2.86/1.01  num_of_split_atoms:                     0
% 2.86/1.01  num_of_reused_defs:                     0
% 2.86/1.01  num_eq_ax_congr_red:                    29
% 2.86/1.01  num_of_sem_filtered_clauses:            1
% 2.86/1.01  num_of_subtypes:                        0
% 2.86/1.01  monotx_restored_types:                  0
% 2.86/1.01  sat_num_of_epr_types:                   0
% 2.86/1.01  sat_num_of_non_cyclic_types:            0
% 2.86/1.01  sat_guarded_non_collapsed_types:        0
% 2.86/1.01  num_pure_diseq_elim:                    0
% 2.86/1.01  simp_replaced_by:                       0
% 2.86/1.01  res_preprocessed:                       123
% 2.86/1.01  prep_upred:                             0
% 2.86/1.01  prep_unflattend:                        75
% 2.86/1.01  smt_new_axioms:                         0
% 2.86/1.01  pred_elim_cands:                        2
% 2.86/1.01  pred_elim:                              3
% 2.86/1.01  pred_elim_cl:                           4
% 2.86/1.01  pred_elim_cycles:                       5
% 2.86/1.01  merged_defs:                            8
% 2.86/1.01  merged_defs_ncl:                        0
% 2.86/1.01  bin_hyper_res:                          8
% 2.86/1.01  prep_cycles:                            4
% 2.86/1.01  pred_elim_time:                         0.013
% 2.86/1.01  splitting_time:                         0.
% 2.86/1.01  sem_filter_time:                        0.
% 2.86/1.01  monotx_time:                            0.001
% 2.86/1.01  subtype_inf_time:                       0.
% 2.86/1.01  
% 2.86/1.01  ------ Problem properties
% 2.86/1.01  
% 2.86/1.01  clauses:                                25
% 2.86/1.01  conjectures:                            2
% 2.86/1.01  epr:                                    4
% 2.86/1.01  horn:                                   21
% 2.86/1.01  ground:                                 6
% 2.86/1.01  unary:                                  10
% 2.86/1.01  binary:                                 9
% 2.86/1.01  lits:                                   47
% 2.86/1.01  lits_eq:                                13
% 2.86/1.01  fd_pure:                                0
% 2.86/1.01  fd_pseudo:                              0
% 2.86/1.01  fd_cond:                                0
% 2.86/1.01  fd_pseudo_cond:                         4
% 2.86/1.01  ac_symbols:                             0
% 2.86/1.01  
% 2.86/1.01  ------ Propositional Solver
% 2.86/1.01  
% 2.86/1.01  prop_solver_calls:                      27
% 2.86/1.01  prop_fast_solver_calls:                 691
% 2.86/1.01  smt_solver_calls:                       0
% 2.86/1.01  smt_fast_solver_calls:                  0
% 2.86/1.01  prop_num_of_clauses:                    2478
% 2.86/1.01  prop_preprocess_simplified:             7923
% 2.86/1.01  prop_fo_subsumed:                       2
% 2.86/1.01  prop_solver_time:                       0.
% 2.86/1.01  smt_solver_time:                        0.
% 2.86/1.01  smt_fast_solver_time:                   0.
% 2.86/1.01  prop_fast_solver_time:                  0.
% 2.86/1.01  prop_unsat_core_time:                   0.
% 2.86/1.01  
% 2.86/1.01  ------ QBF
% 2.86/1.01  
% 2.86/1.01  qbf_q_res:                              0
% 2.86/1.01  qbf_num_tautologies:                    0
% 2.86/1.01  qbf_prep_cycles:                        0
% 2.86/1.01  
% 2.86/1.01  ------ BMC1
% 2.86/1.01  
% 2.86/1.01  bmc1_current_bound:                     -1
% 2.86/1.01  bmc1_last_solved_bound:                 -1
% 2.86/1.01  bmc1_unsat_core_size:                   -1
% 2.86/1.01  bmc1_unsat_core_parents_size:           -1
% 2.86/1.01  bmc1_merge_next_fun:                    0
% 2.86/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.86/1.01  
% 2.86/1.01  ------ Instantiation
% 2.86/1.01  
% 2.86/1.01  inst_num_of_clauses:                    657
% 2.86/1.01  inst_num_in_passive:                    380
% 2.86/1.01  inst_num_in_active:                     243
% 2.86/1.01  inst_num_in_unprocessed:                34
% 2.86/1.01  inst_num_of_loops:                      260
% 2.86/1.01  inst_num_of_learning_restarts:          0
% 2.86/1.01  inst_num_moves_active_passive:          16
% 2.86/1.01  inst_lit_activity:                      0
% 2.86/1.01  inst_lit_activity_moves:                0
% 2.86/1.01  inst_num_tautologies:                   0
% 2.86/1.01  inst_num_prop_implied:                  0
% 2.86/1.01  inst_num_existing_simplified:           0
% 2.86/1.01  inst_num_eq_res_simplified:             0
% 2.86/1.01  inst_num_child_elim:                    0
% 2.86/1.01  inst_num_of_dismatching_blockings:      237
% 2.86/1.01  inst_num_of_non_proper_insts:           529
% 2.86/1.01  inst_num_of_duplicates:                 0
% 2.86/1.01  inst_inst_num_from_inst_to_res:         0
% 2.86/1.01  inst_dismatching_checking_time:         0.
% 2.86/1.01  
% 2.86/1.01  ------ Resolution
% 2.86/1.01  
% 2.86/1.01  res_num_of_clauses:                     0
% 2.86/1.01  res_num_in_passive:                     0
% 2.86/1.01  res_num_in_active:                      0
% 2.86/1.01  res_num_of_loops:                       127
% 2.86/1.01  res_forward_subset_subsumed:            29
% 2.86/1.01  res_backward_subset_subsumed:           0
% 2.86/1.01  res_forward_subsumed:                   2
% 2.86/1.01  res_backward_subsumed:                  0
% 2.86/1.01  res_forward_subsumption_resolution:     0
% 2.86/1.01  res_backward_subsumption_resolution:    0
% 2.86/1.01  res_clause_to_clause_subsumption:       329
% 2.86/1.01  res_orphan_elimination:                 0
% 2.86/1.01  res_tautology_del:                      49
% 2.86/1.01  res_num_eq_res_simplified:              0
% 2.86/1.01  res_num_sel_changes:                    0
% 2.86/1.01  res_moves_from_active_to_pass:          0
% 2.86/1.01  
% 2.86/1.01  ------ Superposition
% 2.86/1.01  
% 2.86/1.01  sup_time_total:                         0.
% 2.86/1.01  sup_time_generating:                    0.
% 2.86/1.01  sup_time_sim_full:                      0.
% 2.86/1.01  sup_time_sim_immed:                     0.
% 2.86/1.01  
% 2.86/1.01  sup_num_of_clauses:                     70
% 2.86/1.01  sup_num_in_active:                      42
% 2.86/1.01  sup_num_in_passive:                     28
% 2.86/1.01  sup_num_of_loops:                       50
% 2.86/1.01  sup_fw_superposition:                   80
% 2.86/1.01  sup_bw_superposition:                   60
% 2.86/1.01  sup_immediate_simplified:               26
% 2.86/1.01  sup_given_eliminated:                   1
% 2.86/1.01  comparisons_done:                       0
% 2.86/1.01  comparisons_avoided:                    0
% 2.86/1.01  
% 2.86/1.01  ------ Simplifications
% 2.86/1.01  
% 2.86/1.01  
% 2.86/1.01  sim_fw_subset_subsumed:                 17
% 2.86/1.01  sim_bw_subset_subsumed:                 0
% 2.86/1.01  sim_fw_subsumed:                        6
% 2.86/1.01  sim_bw_subsumed:                        0
% 2.86/1.01  sim_fw_subsumption_res:                 0
% 2.86/1.01  sim_bw_subsumption_res:                 0
% 2.86/1.01  sim_tautology_del:                      18
% 2.86/1.01  sim_eq_tautology_del:                   8
% 2.86/1.01  sim_eq_res_simp:                        6
% 2.86/1.01  sim_fw_demodulated:                     7
% 2.86/1.01  sim_bw_demodulated:                     9
% 2.86/1.01  sim_light_normalised:                   4
% 2.86/1.01  sim_joinable_taut:                      0
% 2.86/1.01  sim_joinable_simp:                      0
% 2.86/1.01  sim_ac_normalised:                      0
% 2.86/1.01  sim_smt_subsumption:                    0
% 2.86/1.01  
%------------------------------------------------------------------------------
