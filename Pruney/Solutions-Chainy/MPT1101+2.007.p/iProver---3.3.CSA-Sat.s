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
% DateTime   : Thu Dec  3 12:10:43 EST 2020

% Result     : CounterSatisfiable 6.88s
% Output     : Saturation 6.88s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 232 expanded)
%              Number of clauses        :   35 (  90 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 527 expanded)
%              Number of equality atoms :   82 ( 246 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_57,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4847,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_50
    | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0_1(X1) ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_4844,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | iProver_ARSWP_50 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4752])).

cnf(c_5059,plain,
    ( arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)) = arAF0_k3_subset_1_0
    | iProver_ARSWP_50 != iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_4844])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4753,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_51 ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_4843,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
    | iProver_ARSWP_51 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4753])).

cnf(c_5228,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_4843])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5360,plain,
    ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK0)) = iProver_top
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_5228,c_4848])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4751,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ iProver_ARSWP_49
    | k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = X1 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_4845,plain,
    ( k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = X1
    | r1_tarski(X0,X1) != iProver_top
    | iProver_ARSWP_49 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4751])).

cnf(c_5381,plain,
    ( k2_xboole_0(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = u1_struct_0(sK0)
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_49 != iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_4845])).

cnf(c_6004,plain,
    ( k2_xboole_0(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) = u1_struct_0(sK0)
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_49 != iProver_top ),
    inference(superposition,[status(thm)],[c_5059,c_5381])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4849,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5357,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,X0) = k2_xboole_0(arAF0_k3_subset_1_0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_5228,c_4849])).

cnf(c_5702,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) = k2_xboole_0(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_5228,c_5357])).

cnf(c_5701,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,sK1) = k2_xboole_0(arAF0_k3_subset_1_0,sK1)
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_5357])).

cnf(c_5004,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_4848])).

cnf(c_5154,plain,
    ( k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = u1_struct_0(sK0)
    | iProver_ARSWP_49 != iProver_top ),
    inference(superposition,[status(thm)],[c_5004,c_4845])).

cnf(c_5159,plain,
    ( k2_xboole_0(sK1,arAF0_k3_subset_1_0) = u1_struct_0(sK0)
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_49 != iProver_top ),
    inference(superposition,[status(thm)],[c_5059,c_5154])).

cnf(c_5234,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_4849])).

cnf(c_5471,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0) = k2_xboole_0(sK1,arAF0_k3_subset_1_0)
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_5228,c_5234])).

cnf(c_5,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4754,negated_conjecture,
    ( ~ iProver_ARSWP_52
    | k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0) != k2_struct_0(sK0) ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_4842,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0) != k2_struct_0(sK0)
    | iProver_ARSWP_52 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4754])).

cnf(c_5585,plain,
    ( k2_xboole_0(sK1,arAF0_k3_subset_1_0) != k2_struct_0(sK0)
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top ),
    inference(superposition,[status(thm)],[c_5471,c_4842])).

cnf(c_5695,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | iProver_ARSWP_52 != iProver_top
    | iProver_ARSWP_51 != iProver_top
    | iProver_ARSWP_50 != iProver_top
    | iProver_ARSWP_49 != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_5585])).

cnf(c_5470,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_4847,c_5234])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.88/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/1.53  
% 6.88/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.88/1.53  
% 6.88/1.53  ------  iProver source info
% 6.88/1.53  
% 6.88/1.53  git: date: 2020-06-30 10:37:57 +0100
% 6.88/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.88/1.53  git: non_committed_changes: false
% 6.88/1.53  git: last_make_outside_of_git: false
% 6.88/1.53  
% 6.88/1.53  ------ 
% 6.88/1.53  ------ Parsing...
% 6.88/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  ------ Proving...
% 6.88/1.53  ------ Problem Properties 
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  clauses                                 7
% 6.88/1.53  conjectures                             2
% 6.88/1.53  EPR                                     0
% 6.88/1.53  Horn                                    7
% 6.88/1.53  unary                                   2
% 6.88/1.53  binary                                  4
% 6.88/1.53  lits                                    13
% 6.88/1.53  lits eq                                 4
% 6.88/1.53  fd_pure                                 0
% 6.88/1.53  fd_pseudo                               0
% 6.88/1.53  fd_cond                                 0
% 6.88/1.53  fd_pseudo_cond                          0
% 6.88/1.53  AC symbols                              0
% 6.88/1.53  
% 6.88/1.53  ------ Input Options Time Limit: Unbounded
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 6.88/1.53  Current options:
% 6.88/1.53  ------ 
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.88/1.53  
% 6.88/1.53  ------ Proving...
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  % SZS status CounterSatisfiable for theBenchmark.p
% 6.88/1.53  
% 6.88/1.53  % SZS output start Saturation for theBenchmark.p
% 6.88/1.53  
% 6.88/1.53  fof(f6,conjecture,(
% 6.88/1.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 6.88/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.88/1.53  
% 6.88/1.53  fof(f7,negated_conjecture,(
% 6.88/1.53    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 6.88/1.53    inference(negated_conjecture,[],[f6])).
% 6.88/1.53  
% 6.88/1.53  fof(f9,plain,(
% 6.88/1.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0))),
% 6.88/1.53    inference(pure_predicate_removal,[],[f7])).
% 6.88/1.53  
% 6.88/1.53  fof(f16,plain,(
% 6.88/1.53    ? [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 6.88/1.53    inference(ennf_transformation,[],[f9])).
% 6.88/1.53  
% 6.88/1.53  fof(f17,plain,(
% 6.88/1.53    ? [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.88/1.53    introduced(choice_axiom,[])).
% 6.88/1.53  
% 6.88/1.53  fof(f18,plain,(
% 6.88/1.53    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.88/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 6.88/1.53  
% 6.88/1.53  fof(f24,plain,(
% 6.88/1.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.88/1.53    inference(cnf_transformation,[],[f18])).
% 6.88/1.53  
% 6.88/1.53  fof(f2,axiom,(
% 6.88/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.88/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.88/1.53  
% 6.88/1.53  fof(f11,plain,(
% 6.88/1.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.88/1.53    inference(ennf_transformation,[],[f2])).
% 6.88/1.53  
% 6.88/1.53  fof(f20,plain,(
% 6.88/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.88/1.53    inference(cnf_transformation,[],[f11])).
% 6.88/1.53  
% 6.88/1.53  fof(f3,axiom,(
% 6.88/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.88/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.88/1.53  
% 6.88/1.53  fof(f12,plain,(
% 6.88/1.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.88/1.53    inference(ennf_transformation,[],[f3])).
% 6.88/1.53  
% 6.88/1.53  fof(f21,plain,(
% 6.88/1.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.88/1.53    inference(cnf_transformation,[],[f12])).
% 6.88/1.53  
% 6.88/1.53  fof(f5,axiom,(
% 6.88/1.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.88/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.88/1.53  
% 6.88/1.53  fof(f8,plain,(
% 6.88/1.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 6.88/1.53    inference(unused_predicate_definition_removal,[],[f5])).
% 6.88/1.53  
% 6.88/1.53  fof(f15,plain,(
% 6.88/1.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 6.88/1.53    inference(ennf_transformation,[],[f8])).
% 6.88/1.53  
% 6.88/1.53  fof(f23,plain,(
% 6.88/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.88/1.53    inference(cnf_transformation,[],[f15])).
% 6.88/1.53  
% 6.88/1.53  fof(f1,axiom,(
% 6.88/1.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 6.88/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.88/1.53  
% 6.88/1.53  fof(f10,plain,(
% 6.88/1.53    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 6.88/1.53    inference(ennf_transformation,[],[f1])).
% 6.88/1.53  
% 6.88/1.53  fof(f19,plain,(
% 6.88/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 6.88/1.53    inference(cnf_transformation,[],[f10])).
% 6.88/1.53  
% 6.88/1.53  fof(f4,axiom,(
% 6.88/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.88/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.88/1.53  
% 6.88/1.53  fof(f13,plain,(
% 6.88/1.53    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.88/1.53    inference(ennf_transformation,[],[f4])).
% 6.88/1.53  
% 6.88/1.53  fof(f14,plain,(
% 6.88/1.53    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.88/1.53    inference(flattening,[],[f13])).
% 6.88/1.53  
% 6.88/1.53  fof(f22,plain,(
% 6.88/1.53    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.88/1.53    inference(cnf_transformation,[],[f14])).
% 6.88/1.53  
% 6.88/1.53  fof(f25,plain,(
% 6.88/1.53    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)),
% 6.88/1.53    inference(cnf_transformation,[],[f18])).
% 6.88/1.53  
% 6.88/1.53  cnf(c_57,plain,( X0_2 = X0_2 ),theory(equality) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_6,negated_conjecture,
% 6.88/1.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 6.88/1.53      inference(cnf_transformation,[],[f24]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4847,plain,
% 6.88/1.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_1,plain,
% 6.88/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.53      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 6.88/1.53      inference(cnf_transformation,[],[f20]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4752,plain,
% 6.88/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.53      | ~ iProver_ARSWP_50
% 6.88/1.53      | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0_1(X1) ),
% 6.88/1.53      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4844,plain,
% 6.88/1.53      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0_1(X0)
% 6.88/1.53      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.88/1.53      | iProver_ARSWP_50 != iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_4752]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5059,plain,
% 6.88/1.53      ( arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)) = arAF0_k3_subset_1_0
% 6.88/1.53      | iProver_ARSWP_50 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_4847,c_4844]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_2,plain,
% 6.88/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.53      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 6.88/1.53      inference(cnf_transformation,[],[f21]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4753,plain,
% 6.88/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.53      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1))
% 6.88/1.53      | ~ iProver_ARSWP_51 ),
% 6.88/1.53      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4843,plain,
% 6.88/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.88/1.53      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_4753]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5228,plain,
% 6.88/1.53      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_4847,c_4843]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4,plain,
% 6.88/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.88/1.53      inference(cnf_transformation,[],[f23]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4848,plain,
% 6.88/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.88/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5360,plain,
% 6.88/1.53      ( r1_tarski(arAF0_k3_subset_1_0,u1_struct_0(sK0)) = iProver_top
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5228,c_4848]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_0,plain,
% 6.88/1.53      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 6.88/1.53      inference(cnf_transformation,[],[f19]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4751,plain,
% 6.88/1.53      ( ~ r1_tarski(X0,X1)
% 6.88/1.53      | ~ iProver_ARSWP_49
% 6.88/1.53      | k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = X1 ),
% 6.88/1.53      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4845,plain,
% 6.88/1.53      ( k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = X1
% 6.88/1.53      | r1_tarski(X0,X1) != iProver_top
% 6.88/1.53      | iProver_ARSWP_49 != iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_4751]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5381,plain,
% 6.88/1.53      ( k2_xboole_0(arAF0_k3_subset_1_0,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = u1_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top
% 6.88/1.53      | iProver_ARSWP_49 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5360,c_4845]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_6004,plain,
% 6.88/1.53      ( k2_xboole_0(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) = u1_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top
% 6.88/1.53      | iProver_ARSWP_50 != iProver_top
% 6.88/1.53      | iProver_ARSWP_49 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5059,c_5381]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_3,plain,
% 6.88/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.88/1.53      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 6.88/1.53      inference(cnf_transformation,[],[f22]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4849,plain,
% 6.88/1.53      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 6.88/1.53      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.88/1.53      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5357,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,X0) = k2_xboole_0(arAF0_k3_subset_1_0,X0)
% 6.88/1.53      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5228,c_4849]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5702,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,arAF0_k3_subset_1_0) = k2_xboole_0(arAF0_k3_subset_1_0,arAF0_k3_subset_1_0)
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5228,c_5357]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5701,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,sK1) = k2_xboole_0(arAF0_k3_subset_1_0,sK1)
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_4847,c_5357]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5004,plain,
% 6.88/1.53      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_4847,c_4848]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5154,plain,
% 6.88/1.53      ( k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = u1_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_49 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5004,c_4845]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5159,plain,
% 6.88/1.53      ( k2_xboole_0(sK1,arAF0_k3_subset_1_0) = u1_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_50 != iProver_top
% 6.88/1.53      | iProver_ARSWP_49 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5059,c_5154]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5234,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 6.88/1.53      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_4847,c_4849]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5471,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0) = k2_xboole_0(sK1,arAF0_k3_subset_1_0)
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5228,c_5234]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5,negated_conjecture,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
% 6.88/1.53      inference(cnf_transformation,[],[f25]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4754,negated_conjecture,
% 6.88/1.53      ( ~ iProver_ARSWP_52
% 6.88/1.53      | k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0) != k2_struct_0(sK0) ),
% 6.88/1.53      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_4842,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0) != k2_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_52 != iProver_top ),
% 6.88/1.53      inference(predicate_to_equality,[status(thm)],[c_4754]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5585,plain,
% 6.88/1.53      ( k2_xboole_0(sK1,arAF0_k3_subset_1_0) != k2_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_52 != iProver_top
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5471,c_4842]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5695,plain,
% 6.88/1.53      ( k2_struct_0(sK0) != u1_struct_0(sK0)
% 6.88/1.53      | iProver_ARSWP_52 != iProver_top
% 6.88/1.53      | iProver_ARSWP_51 != iProver_top
% 6.88/1.53      | iProver_ARSWP_50 != iProver_top
% 6.88/1.53      | iProver_ARSWP_49 != iProver_top ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_5159,c_5585]) ).
% 6.88/1.53  
% 6.88/1.53  cnf(c_5470,plain,
% 6.88/1.53      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
% 6.88/1.53      inference(superposition,[status(thm)],[c_4847,c_5234]) ).
% 6.88/1.53  
% 6.88/1.53  
% 6.88/1.53  % SZS output end Saturation for theBenchmark.p
% 6.88/1.53  
% 6.88/1.53  ------                               Statistics
% 6.88/1.53  
% 6.88/1.53  ------ Selected
% 6.88/1.53  
% 6.88/1.53  total_time:                             0.494
% 6.88/1.53  
%------------------------------------------------------------------------------
