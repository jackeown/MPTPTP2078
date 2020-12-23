%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:43 EST 2020

% Result     : CounterSatisfiable 2.58s
% Output     : Saturation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 230 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(X0))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ m1_subset_1(sK3,u1_struct_0(X0))
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,u1_struct_0(X0))
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,u1_struct_0(X0))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(sK1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f27,f26,f25])).

fof(f42,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_137,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_925,plain,
    ( m1_subset_1(X0,X1)
    | ~ iProver_ARSWP_46
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_1099,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | iProver_ARSWP_46 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1105,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1500,plain,
    ( iProver_ARSWP_46 != iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1105])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_924,plain,
    ( m1_subset_1(k2_subset_1(X0),arAF0_k1_zfmisc_1_0)
    | ~ iProver_ARSWP_45 ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_1100,plain,
    ( m1_subset_1(k2_subset_1(X0),arAF0_k1_zfmisc_1_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1113,plain,
    ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0) = iProver_top
    | iProver_ARSWP_45 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1100,c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,arAF0_k1_zfmisc_1_0)
    | ~ iProver_ARSWP_48
    | arAF0_r1_tarski_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_1097,plain,
    ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0) != iProver_top
    | iProver_ARSWP_48 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_1320,plain,
    ( iProver_ARSWP_48 != iProver_top
    | iProver_ARSWP_45 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1097])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_926,plain,
    ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0)
    | ~ iProver_ARSWP_47
    | ~ arAF0_r1_tarski_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_1098,plain,
    ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0) = iProver_top
    | iProver_ARSWP_47 != iProver_top
    | arAF0_r1_tarski_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_922,plain,
    ( ~ iProver_ARSWP_43
    | arAF0_r1_tarski_0
    | arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1101,plain,
    ( iProver_ARSWP_43 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top
    | arAF0_r2_hidden_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_921,plain,
    ( ~ iProver_ARSWP_42
    | arAF0_r1_tarski_0
    | ~ arAF0_r2_hidden_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1102,plain,
    ( iProver_ARSWP_42 != iProver_top
    | arAF0_r1_tarski_0 = iProver_top
    | arAF0_r2_hidden_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1104,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.58/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.04  
% 2.58/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/1.04  
% 2.58/1.04  ------  iProver source info
% 2.58/1.04  
% 2.58/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.58/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/1.04  git: non_committed_changes: false
% 2.58/1.04  git: last_make_outside_of_git: false
% 2.58/1.04  
% 2.58/1.04  ------ 
% 2.58/1.04  ------ Parsing...
% 2.58/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.04  ------ Proving...
% 2.58/1.04  ------ Problem Properties 
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  clauses                                 14
% 2.58/1.04  conjectures                             4
% 2.58/1.04  EPR                                     5
% 2.58/1.04  Horn                                    13
% 2.58/1.04  unary                                   6
% 2.58/1.04  binary                                  5
% 2.58/1.04  lits                                    26
% 2.58/1.04  lits eq                                 1
% 2.58/1.04  fd_pure                                 0
% 2.58/1.04  fd_pseudo                               0
% 2.58/1.04  fd_cond                                 0
% 2.58/1.04  fd_pseudo_cond                          0
% 2.58/1.04  AC symbols                              0
% 2.58/1.04  
% 2.58/1.04  ------ Input Options Time Limit: Unbounded
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing...
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 2.58/1.04  Current options:
% 2.58/1.04  ------ 
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Proving...
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing...
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing...
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.04  
% 2.58/1.04  ------ Proving...
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.04  
% 2.58/1.04  ------ Proving...
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.04  
% 2.58/1.04  ------ Proving...
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.04  
% 2.58/1.04  ------ Proving...
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.04  
% 2.58/1.04  ------ Proving...
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  % SZS status CounterSatisfiable for theBenchmark.p
% 2.58/1.04  
% 2.58/1.04  % SZS output start Saturation for theBenchmark.p
% 2.58/1.04  
% 2.58/1.04  fof(f4,axiom,(
% 2.58/1.04    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.58/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.04  
% 2.58/1.04  fof(f16,plain,(
% 2.58/1.04    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.58/1.04    inference(ennf_transformation,[],[f4])).
% 2.58/1.04  
% 2.58/1.04  fof(f34,plain,(
% 2.58/1.04    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.58/1.04    inference(cnf_transformation,[],[f16])).
% 2.58/1.04  
% 2.58/1.04  fof(f10,conjecture,(
% 2.58/1.04    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.58/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.04  
% 2.58/1.04  fof(f11,negated_conjecture,(
% 2.58/1.04    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.58/1.04    inference(negated_conjecture,[],[f10])).
% 2.58/1.04  
% 2.58/1.04  fof(f12,plain,(
% 2.58/1.04    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.58/1.04    inference(pure_predicate_removal,[],[f11])).
% 2.58/1.04  
% 2.58/1.04  fof(f19,plain,(
% 2.58/1.04    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 2.58/1.04    inference(ennf_transformation,[],[f12])).
% 2.58/1.04  
% 2.58/1.04  fof(f27,plain,(
% 2.58/1.04    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X2,u1_struct_0(X1))) => (~m1_subset_1(sK3,u1_struct_0(X0)) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 2.58/1.04    introduced(choice_axiom,[])).
% 2.58/1.04  
% 2.58/1.04  fof(f26,plain,(
% 2.58/1.04    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0)) => (? [X2] : (~m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_pre_topc(sK2,X0))) )),
% 2.58/1.04    introduced(choice_axiom,[])).
% 2.58/1.04  
% 2.58/1.04  fof(f25,plain,(
% 2.58/1.04    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK1)) & l1_pre_topc(sK1))),
% 2.58/1.04    introduced(choice_axiom,[])).
% 2.58/1.04  
% 2.58/1.04  fof(f28,plain,(
% 2.58/1.04    ((~m1_subset_1(sK3,u1_struct_0(sK1)) & m1_subset_1(sK3,u1_struct_0(sK2))) & m1_pre_topc(sK2,sK1)) & l1_pre_topc(sK1)),
% 2.58/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f27,f26,f25])).
% 2.58/1.04  
% 2.58/1.04  fof(f42,plain,(
% 2.58/1.04    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.58/1.04    inference(cnf_transformation,[],[f28])).
% 2.58/1.04  
% 2.58/1.04  fof(f3,axiom,(
% 2.58/1.04    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.58/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.04  
% 2.58/1.04  fof(f33,plain,(
% 2.58/1.04    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.58/1.04    inference(cnf_transformation,[],[f3])).
% 2.58/1.04  
% 2.58/1.04  fof(f2,axiom,(
% 2.58/1.04    ! [X0] : k2_subset_1(X0) = X0),
% 2.58/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.04  
% 2.58/1.04  fof(f32,plain,(
% 2.58/1.04    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.58/1.04    inference(cnf_transformation,[],[f2])).
% 2.58/1.04  
% 2.58/1.04  fof(f6,axiom,(
% 2.58/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.58/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.04  
% 2.58/1.04  fof(f24,plain,(
% 2.58/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.58/1.04    inference(nnf_transformation,[],[f6])).
% 2.58/1.04  
% 2.58/1.04  fof(f35,plain,(
% 2.58/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.58/1.04    inference(cnf_transformation,[],[f24])).
% 2.58/1.04  
% 2.58/1.04  fof(f36,plain,(
% 2.58/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.58/1.04    inference(cnf_transformation,[],[f24])).
% 2.58/1.04  
% 2.58/1.04  fof(f1,axiom,(
% 2.58/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.58/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.04  
% 2.58/1.04  fof(f15,plain,(
% 2.58/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.58/1.04    inference(ennf_transformation,[],[f1])).
% 2.58/1.04  
% 2.58/1.04  fof(f20,plain,(
% 2.58/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.58/1.04    inference(nnf_transformation,[],[f15])).
% 2.58/1.04  
% 2.58/1.04  fof(f21,plain,(
% 2.58/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.58/1.04    inference(rectify,[],[f20])).
% 2.58/1.04  
% 2.58/1.04  fof(f22,plain,(
% 2.58/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.58/1.04    introduced(choice_axiom,[])).
% 2.58/1.04  
% 2.58/1.04  fof(f23,plain,(
% 2.58/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.58/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.58/1.04  
% 2.58/1.04  fof(f30,plain,(
% 2.58/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.58/1.04    inference(cnf_transformation,[],[f23])).
% 2.58/1.04  
% 2.58/1.04  fof(f31,plain,(
% 2.58/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.58/1.04    inference(cnf_transformation,[],[f23])).
% 2.58/1.04  
% 2.58/1.04  fof(f41,plain,(
% 2.58/1.04    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.58/1.04    inference(cnf_transformation,[],[f28])).
% 2.58/1.04  
% 2.58/1.04  cnf(c_137,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_5,plain,
% 2.58/1.04      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.58/1.04      inference(cnf_transformation,[],[f34]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_925,plain,
% 2.58/1.04      ( m1_subset_1(X0,X1) | ~ iProver_ARSWP_46 | ~ arAF0_r2_hidden_0 ),
% 2.58/1.04      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1099,plain,
% 2.58/1.04      ( m1_subset_1(X0,X1) = iProver_top
% 2.58/1.04      | iProver_ARSWP_46 != iProver_top
% 2.58/1.04      | arAF0_r2_hidden_0 != iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_10,negated_conjecture,
% 2.58/1.04      ( ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.58/1.04      inference(cnf_transformation,[],[f42]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1105,plain,
% 2.58/1.04      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1500,plain,
% 2.58/1.04      ( iProver_ARSWP_46 != iProver_top | arAF0_r2_hidden_0 != iProver_top ),
% 2.58/1.04      inference(superposition,[status(thm)],[c_1099,c_1105]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_4,plain,
% 2.58/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.58/1.04      inference(cnf_transformation,[],[f33]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_924,plain,
% 2.58/1.04      ( m1_subset_1(k2_subset_1(X0),arAF0_k1_zfmisc_1_0) | ~ iProver_ARSWP_45 ),
% 2.58/1.04      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1100,plain,
% 2.58/1.04      ( m1_subset_1(k2_subset_1(X0),arAF0_k1_zfmisc_1_0) = iProver_top
% 2.58/1.04      | iProver_ARSWP_45 != iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_3,plain,
% 2.58/1.04      ( k2_subset_1(X0) = X0 ),
% 2.58/1.04      inference(cnf_transformation,[],[f32]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1113,plain,
% 2.58/1.04      ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0) = iProver_top
% 2.58/1.04      | iProver_ARSWP_45 != iProver_top ),
% 2.58/1.04      inference(light_normalisation,[status(thm)],[c_1100,c_3]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_7,plain,
% 2.58/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.58/1.04      inference(cnf_transformation,[],[f35]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_927,plain,
% 2.58/1.04      ( ~ m1_subset_1(X0,arAF0_k1_zfmisc_1_0)
% 2.58/1.04      | ~ iProver_ARSWP_48
% 2.58/1.04      | arAF0_r1_tarski_0 ),
% 2.58/1.04      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1097,plain,
% 2.58/1.04      ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0) != iProver_top
% 2.58/1.04      | iProver_ARSWP_48 != iProver_top
% 2.58/1.04      | arAF0_r1_tarski_0 = iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1320,plain,
% 2.58/1.04      ( iProver_ARSWP_48 != iProver_top
% 2.58/1.04      | iProver_ARSWP_45 != iProver_top
% 2.58/1.04      | arAF0_r1_tarski_0 = iProver_top ),
% 2.58/1.04      inference(superposition,[status(thm)],[c_1113,c_1097]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_6,plain,
% 2.58/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.58/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_926,plain,
% 2.58/1.04      ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0)
% 2.58/1.04      | ~ iProver_ARSWP_47
% 2.58/1.04      | ~ arAF0_r1_tarski_0 ),
% 2.58/1.04      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1098,plain,
% 2.58/1.04      ( m1_subset_1(X0,arAF0_k1_zfmisc_1_0) = iProver_top
% 2.58/1.04      | iProver_ARSWP_47 != iProver_top
% 2.58/1.04      | arAF0_r1_tarski_0 != iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1,plain,
% 2.58/1.04      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.58/1.04      inference(cnf_transformation,[],[f30]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_922,plain,
% 2.58/1.04      ( ~ iProver_ARSWP_43 | arAF0_r1_tarski_0 | arAF0_r2_hidden_0 ),
% 2.58/1.04      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1101,plain,
% 2.58/1.04      ( iProver_ARSWP_43 != iProver_top
% 2.58/1.04      | arAF0_r1_tarski_0 = iProver_top
% 2.58/1.04      | arAF0_r2_hidden_0 = iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_0,plain,
% 2.58/1.04      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.58/1.04      inference(cnf_transformation,[],[f31]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_921,plain,
% 2.58/1.04      ( ~ iProver_ARSWP_42 | arAF0_r1_tarski_0 | ~ arAF0_r2_hidden_0 ),
% 2.58/1.04      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1102,plain,
% 2.58/1.04      ( iProver_ARSWP_42 != iProver_top
% 2.58/1.04      | arAF0_r1_tarski_0 = iProver_top
% 2.58/1.04      | arAF0_r2_hidden_0 != iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_11,negated_conjecture,
% 2.58/1.04      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.58/1.04      inference(cnf_transformation,[],[f41]) ).
% 2.58/1.04  
% 2.58/1.04  cnf(c_1104,plain,
% 2.58/1.04      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.58/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.58/1.04  
% 2.58/1.04  
% 2.58/1.04  % SZS output end Saturation for theBenchmark.p
% 2.58/1.04  
% 2.58/1.04  ------                               Statistics
% 2.58/1.04  
% 2.58/1.04  ------ Selected
% 2.58/1.04  
% 2.58/1.04  total_time:                             0.078
% 2.58/1.04  
%------------------------------------------------------------------------------
