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
% DateTime   : Thu Dec  3 12:25:52 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 341 expanded)
%              Number of clauses        :   56 ( 129 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  260 (1234 expanded)
%              Number of equality atoms :   98 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & ( v2_tex_2(sK2,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24,f23,f22])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f42,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_649,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_642,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_646,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1147,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_646])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_100,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_101,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_100])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_101])).

cnf(c_638,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_2228,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1147,c_638])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_126,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_101])).

cnf(c_639,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_2378,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_646])).

cnf(c_2820,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2228,c_2378])).

cnf(c_815,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_9,c_13])).

cnf(c_816,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_6202,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2820,c_816])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_641,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_645,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1266,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_645])).

cnf(c_3370,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_1266])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4144,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3370,c_16])).

cnf(c_4145,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4144])).

cnf(c_6214,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6202,c_4145])).

cnf(c_6465,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_6214])).

cnf(c_12,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_650,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2226,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_650,c_638])).

cnf(c_2377,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2226,c_639])).

cnf(c_6688,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2377,c_650])).

cnf(c_6692,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6688,c_646])).

cnf(c_3369,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_1266])).

cnf(c_3939,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3369,c_16])).

cnf(c_3940,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3939])).

cnf(c_6215,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6202,c_3940])).

cnf(c_6772,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6692,c_6215])).

cnf(c_7178,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6465,c_19,c_6772])).

cnf(c_11,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_644,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2817,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2228,c_644])).

cnf(c_7186,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7178,c_2817])).

cnf(c_3867,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3870,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3867])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7186,c_3870])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.82/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/1.00  
% 3.82/1.00  ------  iProver source info
% 3.82/1.00  
% 3.82/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.82/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/1.00  git: non_committed_changes: false
% 3.82/1.00  git: last_make_outside_of_git: false
% 3.82/1.00  
% 3.82/1.00  ------ 
% 3.82/1.00  ------ Parsing...
% 3.82/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/1.00  ------ Proving...
% 3.82/1.00  ------ Problem Properties 
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  clauses                                 15
% 3.82/1.00  conjectures                             5
% 3.82/1.00  EPR                                     4
% 3.82/1.00  Horn                                    14
% 3.82/1.00  unary                                   7
% 3.82/1.00  binary                                  6
% 3.82/1.00  lits                                    28
% 3.82/1.00  lits eq                                 3
% 3.82/1.00  fd_pure                                 0
% 3.82/1.00  fd_pseudo                               0
% 3.82/1.00  fd_cond                                 0
% 3.82/1.00  fd_pseudo_cond                          1
% 3.82/1.00  AC symbols                              0
% 3.82/1.00  
% 3.82/1.00  ------ Input Options Time Limit: Unbounded
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  ------ 
% 3.82/1.00  Current options:
% 3.82/1.00  ------ 
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  ------ Proving...
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  % SZS status Theorem for theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  fof(f2,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f12,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.82/1.00    inference(ennf_transformation,[],[f2])).
% 3.82/1.00  
% 3.82/1.00  fof(f29,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f12])).
% 3.82/1.00  
% 3.82/1.00  fof(f7,axiom,(
% 3.82/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f34,plain,(
% 3.82/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f7])).
% 3.82/1.00  
% 3.82/1.00  fof(f43,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 3.82/1.00    inference(definition_unfolding,[],[f29,f34])).
% 3.82/1.00  
% 3.82/1.00  fof(f10,conjecture,(
% 3.82/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f11,negated_conjecture,(
% 3.82/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.82/1.00    inference(negated_conjecture,[],[f10])).
% 3.82/1.00  
% 3.82/1.00  fof(f17,plain,(
% 3.82/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.82/1.00    inference(ennf_transformation,[],[f11])).
% 3.82/1.00  
% 3.82/1.00  fof(f18,plain,(
% 3.82/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.82/1.00    inference(flattening,[],[f17])).
% 3.82/1.00  
% 3.82/1.00  fof(f24,plain,(
% 3.82/1.00    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.82/1.00    introduced(choice_axiom,[])).
% 3.82/1.00  
% 3.82/1.00  fof(f23,plain,(
% 3.82/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.82/1.00    introduced(choice_axiom,[])).
% 3.82/1.00  
% 3.82/1.00  fof(f22,plain,(
% 3.82/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.82/1.00    introduced(choice_axiom,[])).
% 3.82/1.00  
% 3.82/1.00  fof(f25,plain,(
% 3.82/1.00    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24,f23,f22])).
% 3.82/1.00  
% 3.82/1.00  fof(f40,plain,(
% 3.82/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.82/1.00    inference(cnf_transformation,[],[f25])).
% 3.82/1.00  
% 3.82/1.00  fof(f8,axiom,(
% 3.82/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f21,plain,(
% 3.82/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.82/1.00    inference(nnf_transformation,[],[f8])).
% 3.82/1.00  
% 3.82/1.00  fof(f35,plain,(
% 3.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f21])).
% 3.82/1.00  
% 3.82/1.00  fof(f6,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f14,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f6])).
% 3.82/1.00  
% 3.82/1.00  fof(f33,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f14])).
% 3.82/1.00  
% 3.82/1.00  fof(f44,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.82/1.00    inference(definition_unfolding,[],[f33,f34])).
% 3.82/1.00  
% 3.82/1.00  fof(f36,plain,(
% 3.82/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f21])).
% 3.82/1.00  
% 3.82/1.00  fof(f5,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f13,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f5])).
% 3.82/1.00  
% 3.82/1.00  fof(f32,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f13])).
% 3.82/1.00  
% 3.82/1.00  fof(f39,plain,(
% 3.82/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.82/1.00    inference(cnf_transformation,[],[f25])).
% 3.82/1.00  
% 3.82/1.00  fof(f9,axiom,(
% 3.82/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f15,plain,(
% 3.82/1.00    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.82/1.00    inference(ennf_transformation,[],[f9])).
% 3.82/1.00  
% 3.82/1.00  fof(f16,plain,(
% 3.82/1.00    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.82/1.00    inference(flattening,[],[f15])).
% 3.82/1.00  
% 3.82/1.00  fof(f37,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f16])).
% 3.82/1.00  
% 3.82/1.00  fof(f38,plain,(
% 3.82/1.00    l1_pre_topc(sK0)),
% 3.82/1.00    inference(cnf_transformation,[],[f25])).
% 3.82/1.00  
% 3.82/1.00  fof(f41,plain,(
% 3.82/1.00    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 3.82/1.00    inference(cnf_transformation,[],[f25])).
% 3.82/1.00  
% 3.82/1.00  fof(f1,axiom,(
% 3.82/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f19,plain,(
% 3.82/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.82/1.00    inference(nnf_transformation,[],[f1])).
% 3.82/1.00  
% 3.82/1.00  fof(f20,plain,(
% 3.82/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.82/1.00    inference(flattening,[],[f19])).
% 3.82/1.00  
% 3.82/1.00  fof(f26,plain,(
% 3.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.82/1.00    inference(cnf_transformation,[],[f20])).
% 3.82/1.00  
% 3.82/1.00  fof(f46,plain,(
% 3.82/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.82/1.00    inference(equality_resolution,[],[f26])).
% 3.82/1.00  
% 3.82/1.00  fof(f42,plain,(
% 3.82/1.00    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.82/1.00    inference(cnf_transformation,[],[f25])).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3,plain,
% 3.82/1.00      ( ~ r1_tarski(X0,X1)
% 3.82/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 3.82/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_649,plain,
% 3.82/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.82/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_13,negated_conjecture,
% 3.82/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.82/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_642,plain,
% 3.82/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.82/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_646,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.82/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1147,plain,
% 3.82/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_642,c_646]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.82/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.82/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_8,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.82/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_100,plain,
% 3.82/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.82/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_101,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.82/1.00      inference(renaming,[status(thm)],[c_100]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_127,plain,
% 3.82/1.00      ( ~ r1_tarski(X0,X1)
% 3.82/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.82/1.00      inference(bin_hyper_res,[status(thm)],[c_7,c_101]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_638,plain,
% 3.82/1.00      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.82/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2228,plain,
% 3.82/1.00      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1147,c_638]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.82/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.82/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_126,plain,
% 3.82/1.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.82/1.00      | ~ r1_tarski(X2,X0) ),
% 3.82/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_101]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_639,plain,
% 3.82/1.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.82/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2378,plain,
% 3.82/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.82/1.00      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_639,c_646]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2820,plain,
% 3.82/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),u1_struct_0(sK0)) = iProver_top
% 3.82/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_2228,c_2378]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_815,plain,
% 3.82/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.82/1.00      inference(resolution,[status(thm)],[c_9,c_13]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_816,plain,
% 3.82/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6202,plain,
% 3.82/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),u1_struct_0(sK0)) = iProver_top ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_2820,c_816]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_14,negated_conjecture,
% 3.82/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.82/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_641,plain,
% 3.82/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_647,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.82/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_10,plain,
% 3.82/1.00      ( ~ v2_tex_2(X0,X1)
% 3.82/1.00      | v2_tex_2(X2,X1)
% 3.82/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.00      | ~ r1_tarski(X2,X0)
% 3.82/1.00      | ~ l1_pre_topc(X1) ),
% 3.82/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_645,plain,
% 3.82/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.82/1.00      | v2_tex_2(X2,X1) = iProver_top
% 3.82/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.82/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.82/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.82/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1266,plain,
% 3.82/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.82/1.00      | v2_tex_2(X2,X1) = iProver_top
% 3.82/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.82/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.82/1.00      | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
% 3.82/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_647,c_645]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3370,plain,
% 3.82/1.00      ( v2_tex_2(X0,sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.82/1.00      | r1_tarski(X0,sK1) != iProver_top
% 3.82/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_641,c_1266]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_15,negated_conjecture,
% 3.82/1.00      ( l1_pre_topc(sK0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_16,plain,
% 3.82/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4144,plain,
% 3.82/1.00      ( r1_tarski(X0,sK1) != iProver_top
% 3.82/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.82/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 3.82/1.00      | v2_tex_2(X0,sK0) = iProver_top ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_3370,c_16]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4145,plain,
% 3.82/1.00      ( v2_tex_2(X0,sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.82/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.82/1.00      inference(renaming,[status(thm)],[c_4144]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6214,plain,
% 3.82/1.00      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK1) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_6202,c_4145]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6465,plain,
% 3.82/1.00      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_649,c_6214]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_12,negated_conjecture,
% 3.82/1.00      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_19,plain,
% 3.82/1.00      ( v2_tex_2(sK2,sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK1,sK0) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2,plain,
% 3.82/1.00      ( r1_tarski(X0,X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_650,plain,
% 3.82/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2226,plain,
% 3.82/1.00      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_650,c_638]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2377,plain,
% 3.82/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
% 3.82/1.00      | r1_tarski(X1,X1) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_2226,c_639]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6688,plain,
% 3.82/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 3.82/1.00      inference(forward_subsumption_resolution,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_2377,c_650]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6692,plain,
% 3.82/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_6688,c_646]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3369,plain,
% 3.82/1.00      ( v2_tex_2(X0,sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.82/1.00      | r1_tarski(X0,sK2) != iProver_top
% 3.82/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_642,c_1266]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3939,plain,
% 3.82/1.00      ( r1_tarski(X0,sK2) != iProver_top
% 3.82/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.82/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 3.82/1.00      | v2_tex_2(X0,sK0) = iProver_top ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_3369,c_16]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3940,plain,
% 3.82/1.00      ( v2_tex_2(X0,sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.82/1.00      | r1_tarski(X0,sK2) != iProver_top ),
% 3.82/1.00      inference(renaming,[status(thm)],[c_3939]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6215,plain,
% 3.82/1.00      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 3.82/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK2) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_6202,c_3940]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6772,plain,
% 3.82/1.00      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.82/1.00      | v2_tex_2(sK2,sK0) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_6692,c_6215]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7178,plain,
% 3.82/1.00      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.82/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_6465,c_19,c_6772]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_11,negated_conjecture,
% 3.82/1.00      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_644,plain,
% 3.82/1.00      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2817,plain,
% 3.82/1.00      ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_2228,c_644]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7186,plain,
% 3.82/1.00      ( r1_tarski(sK1,sK1) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_7178,c_2817]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3867,plain,
% 3.82/1.00      ( r1_tarski(sK1,sK1) ),
% 3.82/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3870,plain,
% 3.82/1.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_3867]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(contradiction,plain,
% 3.82/1.00      ( $false ),
% 3.82/1.00      inference(minisat,[status(thm)],[c_7186,c_3870]) ).
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  ------                               Statistics
% 3.82/1.00  
% 3.82/1.00  ------ Selected
% 3.82/1.00  
% 3.82/1.00  total_time:                             0.229
% 3.82/1.00  
%------------------------------------------------------------------------------
