%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:07 EST 2020

% Result     : Theorem 15.58s
% Output     : CNFRefutation 15.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 377 expanded)
%              Number of clauses        :   70 ( 132 expanded)
%              Number of leaves         :   15 (  85 expanded)
%              Depth                    :   21
%              Number of atoms          :  304 (1174 expanded)
%              Number of equality atoms :  109 ( 166 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),sK1)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35,f34])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_813,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_161,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_131])).

cnf(c_803,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_1696,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_813,c_803])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1716,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1696,c_5])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_131])).

cnf(c_268,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_302,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_164,c_269])).

cnf(c_800,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_2020,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_800])).

cnf(c_55,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11629,plain,
    ( r1_tarski(k1_xboole_0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2020,c_55])).

cnf(c_11630,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11629])).

cnf(c_11636,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11630,c_813])).

cnf(c_812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_811,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2273,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_811])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_805,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_808,plain,
    ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3161,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_808])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_809,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2428,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_809])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_987,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2470,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2428,c_20,c_19,c_18,c_987])).

cnf(c_3164,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3161,c_2470])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3629,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3164,c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_131])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
    inference(bin_hyper_res,[status(thm)],[c_165,c_269])).

cnf(c_799,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_3634,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_799])).

cnf(c_1047,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_13,c_19])).

cnf(c_1048,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_4092,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3634,c_1048])).

cnf(c_4093,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4092])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_163,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_131])).

cnf(c_301,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_163,c_269])).

cnf(c_801,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_4100,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_801])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_162,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_131])).

cnf(c_802,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_1595,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_811])).

cnf(c_3633,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_1595])).

cnf(c_4123,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4100,c_24,c_1048,c_3633])).

cnf(c_21071,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2273,c_4123])).

cnf(c_23715,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21071,c_21])).

cnf(c_23720,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_23715])).

cnf(c_45007,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11636,c_23720])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45007,c_1048])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:32:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.58/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.58/2.49  
% 15.58/2.49  ------  iProver source info
% 15.58/2.49  
% 15.58/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.58/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.58/2.49  git: non_committed_changes: false
% 15.58/2.49  git: last_make_outside_of_git: false
% 15.58/2.49  
% 15.58/2.49  ------ 
% 15.58/2.49  ------ Parsing...
% 15.58/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.58/2.49  
% 15.58/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.58/2.49  ------ Proving...
% 15.58/2.49  ------ Problem Properties 
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  clauses                                 20
% 15.58/2.49  conjectures                             4
% 15.58/2.49  EPR                                     5
% 15.58/2.49  Horn                                    20
% 15.58/2.49  unary                                   9
% 15.58/2.49  binary                                  4
% 15.58/2.49  lits                                    41
% 15.58/2.49  lits eq                                 6
% 15.58/2.49  fd_pure                                 0
% 15.58/2.49  fd_pseudo                               0
% 15.58/2.49  fd_cond                                 0
% 15.58/2.49  fd_pseudo_cond                          1
% 15.58/2.49  AC symbols                              0
% 15.58/2.49  
% 15.58/2.49  ------ Input Options Time Limit: Unbounded
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  ------ 
% 15.58/2.49  Current options:
% 15.58/2.49  ------ 
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  ------ Proving...
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  % SZS status Theorem for theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  fof(f4,axiom,(
% 15.58/2.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f42,plain,(
% 15.58/2.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f4])).
% 15.58/2.49  
% 15.58/2.49  fof(f7,axiom,(
% 15.58/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f19,plain,(
% 15.58/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f7])).
% 15.58/2.49  
% 15.58/2.49  fof(f45,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f19])).
% 15.58/2.49  
% 15.58/2.49  fof(f2,axiom,(
% 15.58/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f40,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f2])).
% 15.58/2.49  
% 15.58/2.49  fof(f11,axiom,(
% 15.58/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f50,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f11])).
% 15.58/2.49  
% 15.58/2.49  fof(f60,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.58/2.49    inference(definition_unfolding,[],[f40,f50])).
% 15.58/2.49  
% 15.58/2.49  fof(f63,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.58/2.49    inference(definition_unfolding,[],[f45,f60])).
% 15.58/2.49  
% 15.58/2.49  fof(f12,axiom,(
% 15.58/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f33,plain,(
% 15.58/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.58/2.49    inference(nnf_transformation,[],[f12])).
% 15.58/2.49  
% 15.58/2.49  fof(f52,plain,(
% 15.58/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f33])).
% 15.58/2.49  
% 15.58/2.49  fof(f5,axiom,(
% 15.58/2.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f43,plain,(
% 15.58/2.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.58/2.49    inference(cnf_transformation,[],[f5])).
% 15.58/2.49  
% 15.58/2.49  fof(f62,plain,(
% 15.58/2.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 15.58/2.49    inference(definition_unfolding,[],[f43,f60])).
% 15.58/2.49  
% 15.58/2.49  fof(f9,axiom,(
% 15.58/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f21,plain,(
% 15.58/2.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f9])).
% 15.58/2.49  
% 15.58/2.49  fof(f32,plain,(
% 15.58/2.49    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.58/2.49    inference(nnf_transformation,[],[f21])).
% 15.58/2.49  
% 15.58/2.49  fof(f47,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f32])).
% 15.58/2.49  
% 15.58/2.49  fof(f13,axiom,(
% 15.58/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f23,plain,(
% 15.58/2.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f13])).
% 15.58/2.49  
% 15.58/2.49  fof(f24,plain,(
% 15.58/2.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.58/2.49    inference(flattening,[],[f23])).
% 15.58/2.49  
% 15.58/2.49  fof(f53,plain,(
% 15.58/2.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f24])).
% 15.58/2.49  
% 15.58/2.49  fof(f51,plain,(
% 15.58/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f33])).
% 15.58/2.49  
% 15.58/2.49  fof(f16,conjecture,(
% 15.58/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f17,negated_conjecture,(
% 15.58/2.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 15.58/2.49    inference(negated_conjecture,[],[f16])).
% 15.58/2.49  
% 15.58/2.49  fof(f28,plain,(
% 15.58/2.49    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.58/2.49    inference(ennf_transformation,[],[f17])).
% 15.58/2.49  
% 15.58/2.49  fof(f29,plain,(
% 15.58/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.58/2.49    inference(flattening,[],[f28])).
% 15.58/2.49  
% 15.58/2.49  fof(f35,plain,(
% 15.58/2.49    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),sK1) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.58/2.49    introduced(choice_axiom,[])).
% 15.58/2.49  
% 15.58/2.49  fof(f34,plain,(
% 15.58/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.58/2.49    introduced(choice_axiom,[])).
% 15.58/2.49  
% 15.58/2.49  fof(f36,plain,(
% 15.58/2.49    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.58/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35,f34])).
% 15.58/2.49  
% 15.58/2.49  fof(f57,plain,(
% 15.58/2.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.58/2.49    inference(cnf_transformation,[],[f36])).
% 15.58/2.49  
% 15.58/2.49  fof(f15,axiom,(
% 15.58/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f27,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.58/2.49    inference(ennf_transformation,[],[f15])).
% 15.58/2.49  
% 15.58/2.49  fof(f55,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f27])).
% 15.58/2.49  
% 15.58/2.49  fof(f14,axiom,(
% 15.58/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f18,plain,(
% 15.58/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 15.58/2.49    inference(pure_predicate_removal,[],[f14])).
% 15.58/2.49  
% 15.58/2.49  fof(f25,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.58/2.49    inference(ennf_transformation,[],[f18])).
% 15.58/2.49  
% 15.58/2.49  fof(f26,plain,(
% 15.58/2.49    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.58/2.49    inference(flattening,[],[f25])).
% 15.58/2.49  
% 15.58/2.49  fof(f54,plain,(
% 15.58/2.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.58/2.49    inference(cnf_transformation,[],[f26])).
% 15.58/2.49  
% 15.58/2.49  fof(f56,plain,(
% 15.58/2.49    l1_pre_topc(sK0)),
% 15.58/2.49    inference(cnf_transformation,[],[f36])).
% 15.58/2.49  
% 15.58/2.49  fof(f58,plain,(
% 15.58/2.49    v4_pre_topc(sK1,sK0)),
% 15.58/2.49    inference(cnf_transformation,[],[f36])).
% 15.58/2.49  
% 15.58/2.49  fof(f10,axiom,(
% 15.58/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f22,plain,(
% 15.58/2.49    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f10])).
% 15.58/2.49  
% 15.58/2.49  fof(f49,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f22])).
% 15.58/2.49  
% 15.58/2.49  fof(f48,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f32])).
% 15.58/2.49  
% 15.58/2.49  fof(f59,plain,(
% 15.58/2.49    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 15.58/2.49    inference(cnf_transformation,[],[f36])).
% 15.58/2.49  
% 15.58/2.49  fof(f8,axiom,(
% 15.58/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.58/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.58/2.49  
% 15.58/2.49  fof(f20,plain,(
% 15.58/2.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.58/2.49    inference(ennf_transformation,[],[f8])).
% 15.58/2.49  
% 15.58/2.49  fof(f46,plain,(
% 15.58/2.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.58/2.49    inference(cnf_transformation,[],[f20])).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4,plain,
% 15.58/2.49      ( r1_tarski(k1_xboole_0,X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_813,plain,
% 15.58/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_7,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_12,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.58/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_130,plain,
% 15.58/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.58/2.49      inference(prop_impl,[status(thm)],[c_12]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_131,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_130]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_161,plain,
% 15.58/2.49      ( ~ r1_tarski(X0,X1)
% 15.58/2.49      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_7,c_131]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_803,plain,
% 15.58/2.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 15.58/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1696,plain,
% 15.58/2.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_813,c_803]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_5,plain,
% 15.58/2.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 15.58/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1716,plain,
% 15.58/2.49      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_1696,c_5]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_10,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ r1_tarski(X0,X2)
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 15.58/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_164,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ r1_tarski(X2,X1)
% 15.58/2.49      | ~ r1_tarski(X2,X0)
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_10,c_131]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_268,plain,
% 15.58/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.58/2.49      inference(prop_impl,[status(thm)],[c_12]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_269,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_268]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_302,plain,
% 15.58/2.49      ( ~ r1_tarski(X0,X1)
% 15.58/2.49      | ~ r1_tarski(X2,X1)
% 15.58/2.49      | ~ r1_tarski(X2,X0)
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_164,c_269]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_800,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(X2,X0) != iProver_top
% 15.58/2.49      | r1_tarski(X2,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2020,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 15.58/2.49      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_1716,c_800]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_55,plain,
% 15.58/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_11629,plain,
% 15.58/2.49      ( r1_tarski(k1_xboole_0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 15.58/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_2020,c_55]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_11630,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 15.58/2.49      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_11629]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_11636,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 15.58/2.49      inference(forward_subsumption_resolution,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_11630,c_813]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_812,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.58/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_14,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.58/2.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.58/2.49      | ~ l1_pre_topc(X1) ),
% 15.58/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_810,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.58/2.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.58/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_13,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.58/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_811,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.58/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2273,plain,
% 15.58/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.58/2.49      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
% 15.58/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_810,c_811]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_19,negated_conjecture,
% 15.58/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.58/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_805,plain,
% 15.58/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_16,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.58/2.49      | ~ l1_pre_topc(X1)
% 15.58/2.49      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_808,plain,
% 15.58/2.49      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
% 15.58/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.58/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3161,plain,
% 15.58/2.49      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
% 15.58/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_805,c_808]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_15,plain,
% 15.58/2.49      ( ~ v4_pre_topc(X0,X1)
% 15.58/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.58/2.49      | ~ l1_pre_topc(X1)
% 15.58/2.49      | k2_pre_topc(X1,X0) = X0 ),
% 15.58/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_809,plain,
% 15.58/2.49      ( k2_pre_topc(X0,X1) = X1
% 15.58/2.49      | v4_pre_topc(X1,X0) != iProver_top
% 15.58/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.58/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2428,plain,
% 15.58/2.49      ( k2_pre_topc(sK0,sK1) = sK1
% 15.58/2.49      | v4_pre_topc(sK1,sK0) != iProver_top
% 15.58/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_805,c_809]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_20,negated_conjecture,
% 15.58/2.49      ( l1_pre_topc(sK0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_18,negated_conjecture,
% 15.58/2.49      ( v4_pre_topc(sK1,sK0) ),
% 15.58/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_987,plain,
% 15.58/2.49      ( ~ v4_pre_topc(sK1,sK0)
% 15.58/2.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.58/2.49      | ~ l1_pre_topc(sK0)
% 15.58/2.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 15.58/2.49      inference(instantiation,[status(thm)],[c_15]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_2470,plain,
% 15.58/2.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_2428,c_20,c_19,c_18,c_987]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3164,plain,
% 15.58/2.49      ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
% 15.58/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.58/2.49      inference(light_normalisation,[status(thm)],[c_3161,c_2470]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_21,plain,
% 15.58/2.49      ( l1_pre_topc(sK0) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3629,plain,
% 15.58/2.49      ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_3164,c_21]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_11,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
% 15.58/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_165,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ r1_tarski(X2,X1)
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_11,c_131]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_303,plain,
% 15.58/2.49      ( ~ r1_tarski(X0,X1)
% 15.58/2.49      | ~ r1_tarski(X2,X1)
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_165,c_269]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_799,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(X2,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3634,plain,
% 15.58/2.49      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
% 15.58/2.49      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_3629,c_799]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1047,plain,
% 15.58/2.49      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 15.58/2.49      inference(resolution,[status(thm)],[c_13,c_19]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1048,plain,
% 15.58/2.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4092,plain,
% 15.58/2.49      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
% 15.58/2.49      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_3634,c_1048]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4093,plain,
% 15.58/2.49      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 15.58/2.49      inference(renaming,[status(thm)],[c_4092]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_9,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.58/2.49      | r1_tarski(X0,X2)
% 15.58/2.49      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 15.58/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_163,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | ~ r1_tarski(X2,X1)
% 15.58/2.49      | r1_tarski(X2,X0)
% 15.58/2.49      | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_9,c_131]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_301,plain,
% 15.58/2.49      ( ~ r1_tarski(X0,X1)
% 15.58/2.49      | ~ r1_tarski(X2,X1)
% 15.58/2.49      | r1_tarski(X2,X0)
% 15.58/2.49      | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_163,c_269]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_801,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(X2,X1) != iProver_top
% 15.58/2.49      | r1_tarski(X2,X0) = iProver_top
% 15.58/2.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4100,plain,
% 15.58/2.49      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 15.58/2.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 15.58/2.49      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top
% 15.58/2.49      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_4093,c_801]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_17,negated_conjecture,
% 15.58/2.49      ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 15.58/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_24,plain,
% 15.58/2.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_8,plain,
% 15.58/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.58/2.49      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 15.58/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_162,plain,
% 15.58/2.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 15.58/2.49      | ~ r1_tarski(X2,X0) ),
% 15.58/2.49      inference(bin_hyper_res,[status(thm)],[c_8,c_131]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_802,plain,
% 15.58/2.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 15.58/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 15.58/2.49      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_1595,plain,
% 15.58/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.49      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_802,c_811]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_3633,plain,
% 15.58/2.49      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 15.58/2.49      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_3629,c_1595]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_4123,plain,
% 15.58/2.49      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_4100,c_24,c_1048,c_3633]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_21071,plain,
% 15.58/2.49      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.58/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_2273,c_4123]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_23715,plain,
% 15.58/2.49      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.58/2.49      inference(global_propositional_subsumption,
% 15.58/2.49                [status(thm)],
% 15.58/2.49                [c_21071,c_21]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_23720,plain,
% 15.58/2.49      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_812,c_23715]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(c_45007,plain,
% 15.58/2.49      ( r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 15.58/2.49      inference(superposition,[status(thm)],[c_11636,c_23720]) ).
% 15.58/2.49  
% 15.58/2.49  cnf(contradiction,plain,
% 15.58/2.49      ( $false ),
% 15.58/2.49      inference(minisat,[status(thm)],[c_45007,c_1048]) ).
% 15.58/2.49  
% 15.58/2.49  
% 15.58/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.58/2.49  
% 15.58/2.49  ------                               Statistics
% 15.58/2.49  
% 15.58/2.49  ------ Selected
% 15.58/2.49  
% 15.58/2.49  total_time:                             1.921
% 15.58/2.49  
%------------------------------------------------------------------------------
