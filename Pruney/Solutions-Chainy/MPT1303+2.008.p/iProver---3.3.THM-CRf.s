%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:24 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   55 (  97 expanded)
%              Number of clauses        :   27 (  28 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 395 expanded)
%              Number of equality atoms :   42 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK5),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK4,X2),X0)
            & v1_tops_2(sK4,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X1,X2),sK3)
              & v1_tops_2(X1,sK3)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    & v1_tops_2(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f55,f54,f53])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f82,f68])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1095,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1103,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6033,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,sK5) = k4_xboole_0(X0,k4_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_1095,c_1103])).

cnf(c_10,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1116,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6762,plain,
    ( r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6033,c_1116])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1094,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1098,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | v1_tops_2(X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1514,plain,
    ( v1_tops_2(X0,sK3) = iProver_top
    | v1_tops_2(sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1098])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( v1_tops_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2020,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | v1_tops_2(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1514,c_35,c_38])).

cnf(c_2021,plain,
    ( v1_tops_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2020])).

cnf(c_3601,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,X1),sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_2021])).

cnf(c_7071,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6762,c_3601])).

cnf(c_30,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7071,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:10:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.37/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.99  
% 3.37/0.99  ------  iProver source info
% 3.37/0.99  
% 3.37/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.99  git: non_committed_changes: false
% 3.37/0.99  git: last_make_outside_of_git: false
% 3.37/0.99  
% 3.37/0.99  ------ 
% 3.37/0.99  ------ Parsing...
% 3.37/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.99  ------ Proving...
% 3.37/0.99  ------ Problem Properties 
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  clauses                                 35
% 3.37/0.99  conjectures                             5
% 3.37/0.99  EPR                                     10
% 3.37/0.99  Horn                                    29
% 3.37/0.99  unary                                   13
% 3.37/0.99  binary                                  11
% 3.37/0.99  lits                                    74
% 3.37/0.99  lits eq                                 8
% 3.37/0.99  fd_pure                                 0
% 3.37/0.99  fd_pseudo                               0
% 3.37/0.99  fd_cond                                 0
% 3.37/0.99  fd_pseudo_cond                          1
% 3.37/0.99  AC symbols                              0
% 3.37/0.99  
% 3.37/0.99  ------ Input Options Time Limit: Unbounded
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ 
% 3.37/0.99  Current options:
% 3.37/0.99  ------ 
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ Proving...
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS status Theorem for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  fof(f22,conjecture,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f23,negated_conjecture,(
% 3.37/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.37/0.99    inference(negated_conjecture,[],[f22])).
% 3.37/0.99  
% 3.37/0.99  fof(f40,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f41,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f40])).
% 3.37/0.99  
% 3.37/0.99  fof(f55,plain,(
% 3.37/0.99    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK5),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f54,plain,(
% 3.37/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK4,X2),X0) & v1_tops_2(sK4,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f53,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X1,X2),sK3) & v1_tops_2(X1,sK3) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f56,plain,(
% 3.37/0.99    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) & v1_tops_2(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3)),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f55,f54,f53])).
% 3.37/0.99  
% 3.37/0.99  fof(f90,plain,(
% 3.37/0.99    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f17,axiom,(
% 3.37/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f34,plain,(
% 3.37/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f17])).
% 3.37/0.99  
% 3.37/0.99  fof(f82,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.37/0.99    inference(cnf_transformation,[],[f34])).
% 3.37/0.99  
% 3.37/0.99  fof(f7,axiom,(
% 3.37/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f68,plain,(
% 3.37/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.37/0.99    inference(cnf_transformation,[],[f7])).
% 3.37/0.99  
% 3.37/0.99  fof(f95,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.37/0.99    inference(definition_unfolding,[],[f82,f68])).
% 3.37/0.99  
% 3.37/0.99  fof(f6,axiom,(
% 3.37/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f67,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f6])).
% 3.37/0.99  
% 3.37/0.99  fof(f15,axiom,(
% 3.37/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f33,plain,(
% 3.37/0.99    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f15])).
% 3.37/0.99  
% 3.37/0.99  fof(f80,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.37/0.99    inference(cnf_transformation,[],[f33])).
% 3.37/0.99  
% 3.37/0.99  fof(f89,plain,(
% 3.37/0.99    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f21,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f38,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f21])).
% 3.37/0.99  
% 3.37/0.99  fof(f39,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f38])).
% 3.37/0.99  
% 3.37/0.99  fof(f87,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f88,plain,(
% 3.37/0.99    l1_pre_topc(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f91,plain,(
% 3.37/0.99    v1_tops_2(sK4,sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f92,plain,(
% 3.37/0.99    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  cnf(c_32,negated_conjecture,
% 3.37/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1095,plain,
% 3.37/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_24,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.37/0.99      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1103,plain,
% 3.37/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6033,plain,
% 3.37/0.99      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,sK5) = k4_xboole_0(X0,k4_xboole_0(X0,sK5)) ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1095,c_1103]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10,plain,
% 3.37/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1116,plain,
% 3.37/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6762,plain,
% 3.37/0.99      ( r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,sK5),X0) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_6033,c_1116]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_22,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.37/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1105,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.37/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_33,negated_conjecture,
% 3.37/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1094,plain,
% 3.37/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_29,plain,
% 3.37/0.99      ( ~ v1_tops_2(X0,X1)
% 3.37/0.99      | v1_tops_2(X2,X1)
% 3.37/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.37/0.99      | ~ r1_tarski(X2,X0)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1098,plain,
% 3.37/0.99      ( v1_tops_2(X0,X1) != iProver_top
% 3.37/0.99      | v1_tops_2(X2,X1) = iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.37/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 3.37/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1514,plain,
% 3.37/0.99      ( v1_tops_2(X0,sK3) = iProver_top
% 3.37/0.99      | v1_tops_2(sK4,sK3) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.37/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1094,c_1098]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_34,negated_conjecture,
% 3.37/0.99      ( l1_pre_topc(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_35,plain,
% 3.37/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_31,negated_conjecture,
% 3.37/0.99      ( v1_tops_2(sK4,sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_38,plain,
% 3.37/0.99      ( v1_tops_2(sK4,sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2020,plain,
% 3.37/0.99      ( r1_tarski(X0,sK4) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.37/0.99      | v1_tops_2(X0,sK3) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_1514,c_35,c_38]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2021,plain,
% 3.37/0.99      ( v1_tops_2(X0,sK3) = iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.37/0.99      | r1_tarski(X0,sK4) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_2020]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3601,plain,
% 3.37/0.99      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,X1),sK3) = iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.37/0.99      | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X0,X1),sK4) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1105,c_2021]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7071,plain,
% 3.37/0.99      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) = iProver_top
% 3.37/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_6762,c_3601]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_30,negated_conjecture,
% 3.37/0.99      ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_39,plain,
% 3.37/0.99      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_37,plain,
% 3.37/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(contradiction,plain,
% 3.37/0.99      ( $false ),
% 3.37/0.99      inference(minisat,[status(thm)],[c_7071,c_39,c_37]) ).
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  ------                               Statistics
% 3.37/0.99  
% 3.37/0.99  ------ Selected
% 3.37/0.99  
% 3.37/0.99  total_time:                             0.217
% 3.37/0.99  
%------------------------------------------------------------------------------
