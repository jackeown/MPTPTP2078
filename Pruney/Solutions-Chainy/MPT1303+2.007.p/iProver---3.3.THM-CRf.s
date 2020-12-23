%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:23 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 258 expanded)
%              Number of clauses        :   48 (  67 expanded)
%              Number of leaves         :   17 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  252 ( 681 expanded)
%              Number of equality atoms :   79 ( 169 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v1_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29,f28,f27])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_645,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_101,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_101])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_102])).

cnf(c_636,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_1071,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_645,c_636])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_644,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1875,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X2,X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_644])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_637,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_180,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_181,plain,
    ( ~ v1_tops_2(X0,sK0)
    | v1_tops_2(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_635,plain,
    ( v1_tops_2(X0,sK0) != iProver_top
    | v1_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_1191,plain,
    ( v1_tops_2(X0,sK0) != iProver_top
    | v1_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_635])).

cnf(c_2134,plain,
    ( v1_tops_2(X0,sK0) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_1191])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,negated_conjecture,
    ( v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_930,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_931,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_818,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1060,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1061,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_2236,plain,
    ( v1_tops_2(X0,sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_15,c_17,c_931,c_1061])).

cnf(c_2246,plain,
    ( v1_tops_2(k9_subset_1(X0,X1,X0),sK0) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_2236])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_638,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1076,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_641])).

cnf(c_1336,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) ),
    inference(superposition,[status(thm)],[c_1076,c_636])).

cnf(c_1755,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_1071,c_1336])).

cnf(c_9,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_640,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2507,plain,
    ( v1_tops_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1755,c_640])).

cnf(c_2511,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2246,c_2507])).

cnf(c_898,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_901,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2511,c_901])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/1.00  
% 2.46/1.00  ------  iProver source info
% 2.46/1.00  
% 2.46/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.46/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/1.00  git: non_committed_changes: false
% 2.46/1.00  git: last_make_outside_of_git: false
% 2.46/1.00  
% 2.46/1.00  ------ 
% 2.46/1.00  
% 2.46/1.00  ------ Input Options
% 2.46/1.00  
% 2.46/1.00  --out_options                           all
% 2.46/1.00  --tptp_safe_out                         true
% 2.46/1.00  --problem_path                          ""
% 2.46/1.00  --include_path                          ""
% 2.46/1.00  --clausifier                            res/vclausify_rel
% 2.46/1.00  --clausifier_options                    --mode clausify
% 2.46/1.00  --stdin                                 false
% 2.46/1.00  --stats_out                             all
% 2.46/1.00  
% 2.46/1.00  ------ General Options
% 2.46/1.00  
% 2.46/1.00  --fof                                   false
% 2.46/1.00  --time_out_real                         305.
% 2.46/1.00  --time_out_virtual                      -1.
% 2.46/1.00  --symbol_type_check                     false
% 2.46/1.00  --clausify_out                          false
% 2.46/1.00  --sig_cnt_out                           false
% 2.46/1.00  --trig_cnt_out                          false
% 2.46/1.00  --trig_cnt_out_tolerance                1.
% 2.46/1.00  --trig_cnt_out_sk_spl                   false
% 2.46/1.00  --abstr_cl_out                          false
% 2.46/1.00  
% 2.46/1.00  ------ Global Options
% 2.46/1.00  
% 2.46/1.00  --schedule                              default
% 2.46/1.00  --add_important_lit                     false
% 2.46/1.00  --prop_solver_per_cl                    1000
% 2.46/1.00  --min_unsat_core                        false
% 2.46/1.00  --soft_assumptions                      false
% 2.46/1.00  --soft_lemma_size                       3
% 2.46/1.00  --prop_impl_unit_size                   0
% 2.46/1.00  --prop_impl_unit                        []
% 2.46/1.00  --share_sel_clauses                     true
% 2.46/1.00  --reset_solvers                         false
% 2.46/1.00  --bc_imp_inh                            [conj_cone]
% 2.46/1.00  --conj_cone_tolerance                   3.
% 2.46/1.00  --extra_neg_conj                        none
% 2.46/1.00  --large_theory_mode                     true
% 2.46/1.00  --prolific_symb_bound                   200
% 2.46/1.00  --lt_threshold                          2000
% 2.46/1.00  --clause_weak_htbl                      true
% 2.46/1.00  --gc_record_bc_elim                     false
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing Options
% 2.46/1.00  
% 2.46/1.00  --preprocessing_flag                    true
% 2.46/1.00  --time_out_prep_mult                    0.1
% 2.46/1.00  --splitting_mode                        input
% 2.46/1.00  --splitting_grd                         true
% 2.46/1.00  --splitting_cvd                         false
% 2.46/1.00  --splitting_cvd_svl                     false
% 2.46/1.00  --splitting_nvd                         32
% 2.46/1.00  --sub_typing                            true
% 2.46/1.00  --prep_gs_sim                           true
% 2.46/1.00  --prep_unflatten                        true
% 2.46/1.00  --prep_res_sim                          true
% 2.46/1.00  --prep_upred                            true
% 2.46/1.00  --prep_sem_filter                       exhaustive
% 2.46/1.00  --prep_sem_filter_out                   false
% 2.46/1.00  --pred_elim                             true
% 2.46/1.00  --res_sim_input                         true
% 2.46/1.00  --eq_ax_congr_red                       true
% 2.46/1.00  --pure_diseq_elim                       true
% 2.46/1.00  --brand_transform                       false
% 2.46/1.00  --non_eq_to_eq                          false
% 2.46/1.00  --prep_def_merge                        true
% 2.46/1.00  --prep_def_merge_prop_impl              false
% 2.46/1.00  --prep_def_merge_mbd                    true
% 2.46/1.00  --prep_def_merge_tr_red                 false
% 2.46/1.00  --prep_def_merge_tr_cl                  false
% 2.46/1.00  --smt_preprocessing                     true
% 2.46/1.00  --smt_ac_axioms                         fast
% 2.46/1.00  --preprocessed_out                      false
% 2.46/1.00  --preprocessed_stats                    false
% 2.46/1.00  
% 2.46/1.00  ------ Abstraction refinement Options
% 2.46/1.00  
% 2.46/1.00  --abstr_ref                             []
% 2.46/1.00  --abstr_ref_prep                        false
% 2.46/1.00  --abstr_ref_until_sat                   false
% 2.46/1.00  --abstr_ref_sig_restrict                funpre
% 2.46/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.00  --abstr_ref_under                       []
% 2.46/1.00  
% 2.46/1.00  ------ SAT Options
% 2.46/1.00  
% 2.46/1.00  --sat_mode                              false
% 2.46/1.00  --sat_fm_restart_options                ""
% 2.46/1.00  --sat_gr_def                            false
% 2.46/1.00  --sat_epr_types                         true
% 2.46/1.00  --sat_non_cyclic_types                  false
% 2.46/1.00  --sat_finite_models                     false
% 2.46/1.00  --sat_fm_lemmas                         false
% 2.46/1.00  --sat_fm_prep                           false
% 2.46/1.00  --sat_fm_uc_incr                        true
% 2.46/1.00  --sat_out_model                         small
% 2.46/1.00  --sat_out_clauses                       false
% 2.46/1.00  
% 2.46/1.00  ------ QBF Options
% 2.46/1.00  
% 2.46/1.00  --qbf_mode                              false
% 2.46/1.00  --qbf_elim_univ                         false
% 2.46/1.00  --qbf_dom_inst                          none
% 2.46/1.00  --qbf_dom_pre_inst                      false
% 2.46/1.00  --qbf_sk_in                             false
% 2.46/1.00  --qbf_pred_elim                         true
% 2.46/1.00  --qbf_split                             512
% 2.46/1.00  
% 2.46/1.00  ------ BMC1 Options
% 2.46/1.00  
% 2.46/1.00  --bmc1_incremental                      false
% 2.46/1.00  --bmc1_axioms                           reachable_all
% 2.46/1.00  --bmc1_min_bound                        0
% 2.46/1.00  --bmc1_max_bound                        -1
% 2.46/1.00  --bmc1_max_bound_default                -1
% 2.46/1.00  --bmc1_symbol_reachability              true
% 2.46/1.00  --bmc1_property_lemmas                  false
% 2.46/1.00  --bmc1_k_induction                      false
% 2.46/1.00  --bmc1_non_equiv_states                 false
% 2.46/1.00  --bmc1_deadlock                         false
% 2.46/1.00  --bmc1_ucm                              false
% 2.46/1.00  --bmc1_add_unsat_core                   none
% 2.46/1.00  --bmc1_unsat_core_children              false
% 2.46/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.00  --bmc1_out_stat                         full
% 2.46/1.00  --bmc1_ground_init                      false
% 2.46/1.00  --bmc1_pre_inst_next_state              false
% 2.46/1.00  --bmc1_pre_inst_state                   false
% 2.46/1.00  --bmc1_pre_inst_reach_state             false
% 2.46/1.00  --bmc1_out_unsat_core                   false
% 2.46/1.00  --bmc1_aig_witness_out                  false
% 2.46/1.00  --bmc1_verbose                          false
% 2.46/1.00  --bmc1_dump_clauses_tptp                false
% 2.46/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.00  --bmc1_dump_file                        -
% 2.46/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.00  --bmc1_ucm_extend_mode                  1
% 2.46/1.00  --bmc1_ucm_init_mode                    2
% 2.46/1.00  --bmc1_ucm_cone_mode                    none
% 2.46/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.00  --bmc1_ucm_relax_model                  4
% 2.46/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.00  --bmc1_ucm_layered_model                none
% 2.46/1.00  --bmc1_ucm_max_lemma_size               10
% 2.46/1.00  
% 2.46/1.00  ------ AIG Options
% 2.46/1.00  
% 2.46/1.00  --aig_mode                              false
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation Options
% 2.46/1.00  
% 2.46/1.00  --instantiation_flag                    true
% 2.46/1.00  --inst_sos_flag                         false
% 2.46/1.00  --inst_sos_phase                        true
% 2.46/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel_side                     num_symb
% 2.46/1.00  --inst_solver_per_active                1400
% 2.46/1.00  --inst_solver_calls_frac                1.
% 2.46/1.00  --inst_passive_queue_type               priority_queues
% 2.46/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.00  --inst_passive_queues_freq              [25;2]
% 2.46/1.00  --inst_dismatching                      true
% 2.46/1.00  --inst_eager_unprocessed_to_passive     true
% 2.46/1.00  --inst_prop_sim_given                   true
% 2.46/1.00  --inst_prop_sim_new                     false
% 2.46/1.00  --inst_subs_new                         false
% 2.46/1.00  --inst_eq_res_simp                      false
% 2.46/1.00  --inst_subs_given                       false
% 2.46/1.00  --inst_orphan_elimination               true
% 2.46/1.00  --inst_learning_loop_flag               true
% 2.46/1.00  --inst_learning_start                   3000
% 2.46/1.00  --inst_learning_factor                  2
% 2.46/1.00  --inst_start_prop_sim_after_learn       3
% 2.46/1.00  --inst_sel_renew                        solver
% 2.46/1.00  --inst_lit_activity_flag                true
% 2.46/1.00  --inst_restr_to_given                   false
% 2.46/1.00  --inst_activity_threshold               500
% 2.46/1.00  --inst_out_proof                        true
% 2.46/1.00  
% 2.46/1.00  ------ Resolution Options
% 2.46/1.00  
% 2.46/1.00  --resolution_flag                       true
% 2.46/1.00  --res_lit_sel                           adaptive
% 2.46/1.00  --res_lit_sel_side                      none
% 2.46/1.00  --res_ordering                          kbo
% 2.46/1.00  --res_to_prop_solver                    active
% 2.46/1.00  --res_prop_simpl_new                    false
% 2.46/1.00  --res_prop_simpl_given                  true
% 2.46/1.00  --res_passive_queue_type                priority_queues
% 2.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.00  --res_passive_queues_freq               [15;5]
% 2.46/1.00  --res_forward_subs                      full
% 2.46/1.00  --res_backward_subs                     full
% 2.46/1.00  --res_forward_subs_resolution           true
% 2.46/1.00  --res_backward_subs_resolution          true
% 2.46/1.00  --res_orphan_elimination                true
% 2.46/1.00  --res_time_limit                        2.
% 2.46/1.00  --res_out_proof                         true
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Options
% 2.46/1.00  
% 2.46/1.00  --superposition_flag                    true
% 2.46/1.00  --sup_passive_queue_type                priority_queues
% 2.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.00  --demod_completeness_check              fast
% 2.46/1.00  --demod_use_ground                      true
% 2.46/1.00  --sup_to_prop_solver                    passive
% 2.46/1.00  --sup_prop_simpl_new                    true
% 2.46/1.00  --sup_prop_simpl_given                  true
% 2.46/1.00  --sup_fun_splitting                     false
% 2.46/1.00  --sup_smt_interval                      50000
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Simplification Setup
% 2.46/1.00  
% 2.46/1.00  --sup_indices_passive                   []
% 2.46/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_full_bw                           [BwDemod]
% 2.46/1.00  --sup_immed_triv                        [TrivRules]
% 2.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_immed_bw_main                     []
% 2.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  
% 2.46/1.00  ------ Combination Options
% 2.46/1.00  
% 2.46/1.00  --comb_res_mult                         3
% 2.46/1.00  --comb_sup_mult                         2
% 2.46/1.00  --comb_inst_mult                        10
% 2.46/1.00  
% 2.46/1.00  ------ Debug Options
% 2.46/1.00  
% 2.46/1.00  --dbg_backtrace                         false
% 2.46/1.00  --dbg_dump_prop_clauses                 false
% 2.46/1.00  --dbg_dump_prop_clauses_file            -
% 2.46/1.00  --dbg_out_stat                          false
% 2.46/1.00  ------ Parsing...
% 2.46/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/1.00  ------ Proving...
% 2.46/1.00  ------ Problem Properties 
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  clauses                                 12
% 2.46/1.00  conjectures                             4
% 2.46/1.00  EPR                                     4
% 2.46/1.00  Horn                                    12
% 2.46/1.00  unary                                   5
% 2.46/1.00  binary                                  4
% 2.46/1.00  lits                                    24
% 2.46/1.00  lits eq                                 2
% 2.46/1.00  fd_pure                                 0
% 2.46/1.00  fd_pseudo                               0
% 2.46/1.00  fd_cond                                 0
% 2.46/1.00  fd_pseudo_cond                          1
% 2.46/1.00  AC symbols                              0
% 2.46/1.00  
% 2.46/1.00  ------ Schedule dynamic 5 is on 
% 2.46/1.00  
% 2.46/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  ------ 
% 2.46/1.00  Current options:
% 2.46/1.00  ------ 
% 2.46/1.00  
% 2.46/1.00  ------ Input Options
% 2.46/1.00  
% 2.46/1.00  --out_options                           all
% 2.46/1.00  --tptp_safe_out                         true
% 2.46/1.00  --problem_path                          ""
% 2.46/1.00  --include_path                          ""
% 2.46/1.00  --clausifier                            res/vclausify_rel
% 2.46/1.00  --clausifier_options                    --mode clausify
% 2.46/1.00  --stdin                                 false
% 2.46/1.00  --stats_out                             all
% 2.46/1.00  
% 2.46/1.00  ------ General Options
% 2.46/1.00  
% 2.46/1.00  --fof                                   false
% 2.46/1.00  --time_out_real                         305.
% 2.46/1.00  --time_out_virtual                      -1.
% 2.46/1.00  --symbol_type_check                     false
% 2.46/1.00  --clausify_out                          false
% 2.46/1.00  --sig_cnt_out                           false
% 2.46/1.00  --trig_cnt_out                          false
% 2.46/1.00  --trig_cnt_out_tolerance                1.
% 2.46/1.00  --trig_cnt_out_sk_spl                   false
% 2.46/1.00  --abstr_cl_out                          false
% 2.46/1.00  
% 2.46/1.00  ------ Global Options
% 2.46/1.00  
% 2.46/1.00  --schedule                              default
% 2.46/1.00  --add_important_lit                     false
% 2.46/1.00  --prop_solver_per_cl                    1000
% 2.46/1.00  --min_unsat_core                        false
% 2.46/1.00  --soft_assumptions                      false
% 2.46/1.00  --soft_lemma_size                       3
% 2.46/1.00  --prop_impl_unit_size                   0
% 2.46/1.00  --prop_impl_unit                        []
% 2.46/1.00  --share_sel_clauses                     true
% 2.46/1.00  --reset_solvers                         false
% 2.46/1.00  --bc_imp_inh                            [conj_cone]
% 2.46/1.00  --conj_cone_tolerance                   3.
% 2.46/1.00  --extra_neg_conj                        none
% 2.46/1.00  --large_theory_mode                     true
% 2.46/1.00  --prolific_symb_bound                   200
% 2.46/1.00  --lt_threshold                          2000
% 2.46/1.00  --clause_weak_htbl                      true
% 2.46/1.00  --gc_record_bc_elim                     false
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing Options
% 2.46/1.00  
% 2.46/1.00  --preprocessing_flag                    true
% 2.46/1.00  --time_out_prep_mult                    0.1
% 2.46/1.00  --splitting_mode                        input
% 2.46/1.00  --splitting_grd                         true
% 2.46/1.00  --splitting_cvd                         false
% 2.46/1.00  --splitting_cvd_svl                     false
% 2.46/1.00  --splitting_nvd                         32
% 2.46/1.00  --sub_typing                            true
% 2.46/1.00  --prep_gs_sim                           true
% 2.46/1.00  --prep_unflatten                        true
% 2.46/1.00  --prep_res_sim                          true
% 2.46/1.00  --prep_upred                            true
% 2.46/1.00  --prep_sem_filter                       exhaustive
% 2.46/1.00  --prep_sem_filter_out                   false
% 2.46/1.00  --pred_elim                             true
% 2.46/1.00  --res_sim_input                         true
% 2.46/1.00  --eq_ax_congr_red                       true
% 2.46/1.00  --pure_diseq_elim                       true
% 2.46/1.00  --brand_transform                       false
% 2.46/1.00  --non_eq_to_eq                          false
% 2.46/1.00  --prep_def_merge                        true
% 2.46/1.00  --prep_def_merge_prop_impl              false
% 2.46/1.00  --prep_def_merge_mbd                    true
% 2.46/1.00  --prep_def_merge_tr_red                 false
% 2.46/1.00  --prep_def_merge_tr_cl                  false
% 2.46/1.00  --smt_preprocessing                     true
% 2.46/1.00  --smt_ac_axioms                         fast
% 2.46/1.00  --preprocessed_out                      false
% 2.46/1.00  --preprocessed_stats                    false
% 2.46/1.00  
% 2.46/1.00  ------ Abstraction refinement Options
% 2.46/1.00  
% 2.46/1.00  --abstr_ref                             []
% 2.46/1.00  --abstr_ref_prep                        false
% 2.46/1.00  --abstr_ref_until_sat                   false
% 2.46/1.00  --abstr_ref_sig_restrict                funpre
% 2.46/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.00  --abstr_ref_under                       []
% 2.46/1.00  
% 2.46/1.00  ------ SAT Options
% 2.46/1.00  
% 2.46/1.00  --sat_mode                              false
% 2.46/1.00  --sat_fm_restart_options                ""
% 2.46/1.00  --sat_gr_def                            false
% 2.46/1.00  --sat_epr_types                         true
% 2.46/1.00  --sat_non_cyclic_types                  false
% 2.46/1.00  --sat_finite_models                     false
% 2.46/1.00  --sat_fm_lemmas                         false
% 2.46/1.00  --sat_fm_prep                           false
% 2.46/1.00  --sat_fm_uc_incr                        true
% 2.46/1.00  --sat_out_model                         small
% 2.46/1.00  --sat_out_clauses                       false
% 2.46/1.00  
% 2.46/1.00  ------ QBF Options
% 2.46/1.00  
% 2.46/1.00  --qbf_mode                              false
% 2.46/1.00  --qbf_elim_univ                         false
% 2.46/1.00  --qbf_dom_inst                          none
% 2.46/1.00  --qbf_dom_pre_inst                      false
% 2.46/1.00  --qbf_sk_in                             false
% 2.46/1.00  --qbf_pred_elim                         true
% 2.46/1.00  --qbf_split                             512
% 2.46/1.00  
% 2.46/1.00  ------ BMC1 Options
% 2.46/1.00  
% 2.46/1.00  --bmc1_incremental                      false
% 2.46/1.00  --bmc1_axioms                           reachable_all
% 2.46/1.00  --bmc1_min_bound                        0
% 2.46/1.00  --bmc1_max_bound                        -1
% 2.46/1.00  --bmc1_max_bound_default                -1
% 2.46/1.00  --bmc1_symbol_reachability              true
% 2.46/1.00  --bmc1_property_lemmas                  false
% 2.46/1.00  --bmc1_k_induction                      false
% 2.46/1.00  --bmc1_non_equiv_states                 false
% 2.46/1.00  --bmc1_deadlock                         false
% 2.46/1.00  --bmc1_ucm                              false
% 2.46/1.00  --bmc1_add_unsat_core                   none
% 2.46/1.00  --bmc1_unsat_core_children              false
% 2.46/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.00  --bmc1_out_stat                         full
% 2.46/1.00  --bmc1_ground_init                      false
% 2.46/1.00  --bmc1_pre_inst_next_state              false
% 2.46/1.00  --bmc1_pre_inst_state                   false
% 2.46/1.00  --bmc1_pre_inst_reach_state             false
% 2.46/1.00  --bmc1_out_unsat_core                   false
% 2.46/1.00  --bmc1_aig_witness_out                  false
% 2.46/1.00  --bmc1_verbose                          false
% 2.46/1.00  --bmc1_dump_clauses_tptp                false
% 2.46/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.00  --bmc1_dump_file                        -
% 2.46/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.00  --bmc1_ucm_extend_mode                  1
% 2.46/1.00  --bmc1_ucm_init_mode                    2
% 2.46/1.00  --bmc1_ucm_cone_mode                    none
% 2.46/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.00  --bmc1_ucm_relax_model                  4
% 2.46/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.00  --bmc1_ucm_layered_model                none
% 2.46/1.00  --bmc1_ucm_max_lemma_size               10
% 2.46/1.00  
% 2.46/1.00  ------ AIG Options
% 2.46/1.00  
% 2.46/1.00  --aig_mode                              false
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation Options
% 2.46/1.00  
% 2.46/1.00  --instantiation_flag                    true
% 2.46/1.00  --inst_sos_flag                         false
% 2.46/1.00  --inst_sos_phase                        true
% 2.46/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel_side                     none
% 2.46/1.00  --inst_solver_per_active                1400
% 2.46/1.00  --inst_solver_calls_frac                1.
% 2.46/1.00  --inst_passive_queue_type               priority_queues
% 2.46/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.00  --inst_passive_queues_freq              [25;2]
% 2.46/1.00  --inst_dismatching                      true
% 2.46/1.00  --inst_eager_unprocessed_to_passive     true
% 2.46/1.00  --inst_prop_sim_given                   true
% 2.46/1.00  --inst_prop_sim_new                     false
% 2.46/1.00  --inst_subs_new                         false
% 2.46/1.00  --inst_eq_res_simp                      false
% 2.46/1.00  --inst_subs_given                       false
% 2.46/1.00  --inst_orphan_elimination               true
% 2.46/1.00  --inst_learning_loop_flag               true
% 2.46/1.00  --inst_learning_start                   3000
% 2.46/1.00  --inst_learning_factor                  2
% 2.46/1.00  --inst_start_prop_sim_after_learn       3
% 2.46/1.00  --inst_sel_renew                        solver
% 2.46/1.00  --inst_lit_activity_flag                true
% 2.46/1.00  --inst_restr_to_given                   false
% 2.46/1.00  --inst_activity_threshold               500
% 2.46/1.00  --inst_out_proof                        true
% 2.46/1.00  
% 2.46/1.00  ------ Resolution Options
% 2.46/1.00  
% 2.46/1.00  --resolution_flag                       false
% 2.46/1.00  --res_lit_sel                           adaptive
% 2.46/1.00  --res_lit_sel_side                      none
% 2.46/1.00  --res_ordering                          kbo
% 2.46/1.00  --res_to_prop_solver                    active
% 2.46/1.00  --res_prop_simpl_new                    false
% 2.46/1.00  --res_prop_simpl_given                  true
% 2.46/1.00  --res_passive_queue_type                priority_queues
% 2.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.00  --res_passive_queues_freq               [15;5]
% 2.46/1.00  --res_forward_subs                      full
% 2.46/1.00  --res_backward_subs                     full
% 2.46/1.00  --res_forward_subs_resolution           true
% 2.46/1.00  --res_backward_subs_resolution          true
% 2.46/1.00  --res_orphan_elimination                true
% 2.46/1.00  --res_time_limit                        2.
% 2.46/1.00  --res_out_proof                         true
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Options
% 2.46/1.00  
% 2.46/1.00  --superposition_flag                    true
% 2.46/1.00  --sup_passive_queue_type                priority_queues
% 2.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.00  --demod_completeness_check              fast
% 2.46/1.00  --demod_use_ground                      true
% 2.46/1.00  --sup_to_prop_solver                    passive
% 2.46/1.00  --sup_prop_simpl_new                    true
% 2.46/1.00  --sup_prop_simpl_given                  true
% 2.46/1.00  --sup_fun_splitting                     false
% 2.46/1.00  --sup_smt_interval                      50000
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Simplification Setup
% 2.46/1.00  
% 2.46/1.00  --sup_indices_passive                   []
% 2.46/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_full_bw                           [BwDemod]
% 2.46/1.00  --sup_immed_triv                        [TrivRules]
% 2.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_immed_bw_main                     []
% 2.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  
% 2.46/1.00  ------ Combination Options
% 2.46/1.00  
% 2.46/1.00  --comb_res_mult                         3
% 2.46/1.00  --comb_sup_mult                         2
% 2.46/1.00  --comb_inst_mult                        10
% 2.46/1.00  
% 2.46/1.00  ------ Debug Options
% 2.46/1.00  
% 2.46/1.00  --dbg_backtrace                         false
% 2.46/1.00  --dbg_dump_prop_clauses                 false
% 2.46/1.00  --dbg_dump_prop_clauses_file            -
% 2.46/1.00  --dbg_out_stat                          false
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  ------ Proving...
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS status Theorem for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  fof(f1,axiom,(
% 2.46/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f24,plain,(
% 2.46/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/1.00    inference(nnf_transformation,[],[f1])).
% 2.46/1.00  
% 2.46/1.00  fof(f25,plain,(
% 2.46/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/1.00    inference(flattening,[],[f24])).
% 2.46/1.00  
% 2.46/1.00  fof(f31,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.46/1.00    inference(cnf_transformation,[],[f25])).
% 2.46/1.00  
% 2.46/1.00  fof(f61,plain,(
% 2.46/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.46/1.00    inference(equality_resolution,[],[f31])).
% 2.46/1.00  
% 2.46/1.00  fof(f10,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f19,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f10])).
% 2.46/1.00  
% 2.46/1.00  fof(f42,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f19])).
% 2.46/1.00  
% 2.46/1.00  fof(f11,axiom,(
% 2.46/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f43,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f11])).
% 2.46/1.00  
% 2.46/1.00  fof(f4,axiom,(
% 2.46/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f36,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f4])).
% 2.46/1.00  
% 2.46/1.00  fof(f5,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f37,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f5])).
% 2.46/1.00  
% 2.46/1.00  fof(f6,axiom,(
% 2.46/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f38,plain,(
% 2.46/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f6])).
% 2.46/1.00  
% 2.46/1.00  fof(f7,axiom,(
% 2.46/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f39,plain,(
% 2.46/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f7])).
% 2.46/1.00  
% 2.46/1.00  fof(f8,axiom,(
% 2.46/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f40,plain,(
% 2.46/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f8])).
% 2.46/1.00  
% 2.46/1.00  fof(f9,axiom,(
% 2.46/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f41,plain,(
% 2.46/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f9])).
% 2.46/1.00  
% 2.46/1.00  fof(f52,plain,(
% 2.46/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.46/1.00    inference(definition_unfolding,[],[f40,f41])).
% 2.46/1.00  
% 2.46/1.00  fof(f53,plain,(
% 2.46/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.46/1.00    inference(definition_unfolding,[],[f39,f52])).
% 2.46/1.00  
% 2.46/1.00  fof(f54,plain,(
% 2.46/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.46/1.00    inference(definition_unfolding,[],[f38,f53])).
% 2.46/1.00  
% 2.46/1.00  fof(f55,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.46/1.00    inference(definition_unfolding,[],[f37,f54])).
% 2.46/1.00  
% 2.46/1.00  fof(f56,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.46/1.00    inference(definition_unfolding,[],[f36,f55])).
% 2.46/1.00  
% 2.46/1.00  fof(f57,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.46/1.00    inference(definition_unfolding,[],[f43,f56])).
% 2.46/1.00  
% 2.46/1.00  fof(f59,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.46/1.00    inference(definition_unfolding,[],[f42,f57])).
% 2.46/1.00  
% 2.46/1.00  fof(f12,axiom,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f26,plain,(
% 2.46/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.46/1.00    inference(nnf_transformation,[],[f12])).
% 2.46/1.00  
% 2.46/1.00  fof(f45,plain,(
% 2.46/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f26])).
% 2.46/1.00  
% 2.46/1.00  fof(f2,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f16,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.46/1.00    inference(ennf_transformation,[],[f2])).
% 2.46/1.00  
% 2.46/1.00  fof(f34,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f16])).
% 2.46/1.00  
% 2.46/1.00  fof(f58,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(definition_unfolding,[],[f34,f57])).
% 2.46/1.00  
% 2.46/1.00  fof(f14,conjecture,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f15,negated_conjecture,(
% 2.46/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.46/1.00    inference(negated_conjecture,[],[f14])).
% 2.46/1.00  
% 2.46/1.00  fof(f22,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f15])).
% 2.46/1.00  
% 2.46/1.00  fof(f23,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f22])).
% 2.46/1.00  
% 2.46/1.00  fof(f29,plain,(
% 2.46/1.00    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f28,plain,(
% 2.46/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v1_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f27,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f30,plain,(
% 2.46/1.00    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 2.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29,f28,f27])).
% 2.46/1.00  
% 2.46/1.00  fof(f48,plain,(
% 2.46/1.00    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.46/1.00    inference(cnf_transformation,[],[f30])).
% 2.46/1.00  
% 2.46/1.00  fof(f13,axiom,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f20,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f13])).
% 2.46/1.00  
% 2.46/1.00  fof(f21,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f20])).
% 2.46/1.00  
% 2.46/1.00  fof(f46,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f21])).
% 2.46/1.00  
% 2.46/1.00  fof(f47,plain,(
% 2.46/1.00    l1_pre_topc(sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f30])).
% 2.46/1.00  
% 2.46/1.00  fof(f50,plain,(
% 2.46/1.00    v1_tops_2(sK1,sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f30])).
% 2.46/1.00  
% 2.46/1.00  fof(f44,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f26])).
% 2.46/1.00  
% 2.46/1.00  fof(f3,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f17,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.46/1.00    inference(ennf_transformation,[],[f3])).
% 2.46/1.00  
% 2.46/1.00  fof(f18,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.46/1.00    inference(flattening,[],[f17])).
% 2.46/1.00  
% 2.46/1.00  fof(f35,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f18])).
% 2.46/1.00  
% 2.46/1.00  fof(f49,plain,(
% 2.46/1.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.46/1.00    inference(cnf_transformation,[],[f30])).
% 2.46/1.00  
% 2.46/1.00  fof(f51,plain,(
% 2.46/1.00    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f30])).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2,plain,
% 2.46/1.00      ( r1_tarski(X0,X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_645,plain,
% 2.46/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/1.00      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_101,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.46/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_102,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_101]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_125,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1)
% 2.46/1.00      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.46/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_102]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_636,plain,
% 2.46/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 2.46/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1071,plain,
% 2.46/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_645,c_636]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1)
% 2.46/1.00      | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_644,plain,
% 2.46/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1875,plain,
% 2.46/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.46/1.00      | r1_tarski(k9_subset_1(X2,X0,X2),X1) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1071,c_644]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_12,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.46/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_637,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_642,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_8,plain,
% 2.46/1.00      ( ~ v1_tops_2(X0,X1)
% 2.46/1.00      | v1_tops_2(X2,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.46/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.46/1.00      | ~ r1_tarski(X2,X0)
% 2.46/1.00      | ~ l1_pre_topc(X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_13,negated_conjecture,
% 2.46/1.00      ( l1_pre_topc(sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_180,plain,
% 2.46/1.00      ( ~ v1_tops_2(X0,X1)
% 2.46/1.00      | v1_tops_2(X2,X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.46/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.46/1.00      | ~ r1_tarski(X2,X0)
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_181,plain,
% 2.46/1.00      ( ~ v1_tops_2(X0,sK0)
% 2.46/1.00      | v1_tops_2(X1,sK0)
% 2.46/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.46/1.00      | ~ r1_tarski(X1,X0) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_180]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_635,plain,
% 2.46/1.00      ( v1_tops_2(X0,sK0) != iProver_top
% 2.46/1.00      | v1_tops_2(X1,sK0) = iProver_top
% 2.46/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.46/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1191,plain,
% 2.46/1.00      ( v1_tops_2(X0,sK0) != iProver_top
% 2.46/1.00      | v1_tops_2(X1,sK0) = iProver_top
% 2.46/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.46/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.46/1.00      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_642,c_635]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2134,plain,
% 2.46/1.00      ( v1_tops_2(X0,sK0) = iProver_top
% 2.46/1.00      | v1_tops_2(sK1,sK0) != iProver_top
% 2.46/1.00      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_637,c_1191]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_15,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_10,negated_conjecture,
% 2.46/1.00      ( v1_tops_2(sK1,sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_17,plain,
% 2.46/1.00      ( v1_tops_2(sK1,sK0) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_797,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.46/1.00      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_930,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.46/1.00      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_797]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_931,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.46/1.00      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.46/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_818,plain,
% 2.46/1.00      ( ~ r1_tarski(X0,X1)
% 2.46/1.00      | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1060,plain,
% 2.46/1.00      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | ~ r1_tarski(X0,sK1)
% 2.46/1.00      | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_818]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1061,plain,
% 2.46/1.00      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top
% 2.46/1.00      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2236,plain,
% 2.46/1.00      ( v1_tops_2(X0,sK0) = iProver_top
% 2.46/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_2134,c_15,c_17,c_931,c_1061]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2246,plain,
% 2.46/1.00      ( v1_tops_2(k9_subset_1(X0,X1,X0),sK0) = iProver_top
% 2.46/1.00      | r1_tarski(X1,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1875,c_2236]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_11,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.46/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_638,plain,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_641,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.46/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1076,plain,
% 2.46/1.00      ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_638,c_641]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1336,plain,
% 2.46/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1076,c_636]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1755,plain,
% 2.46/1.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 2.46/1.00      inference(demodulation,[status(thm)],[c_1071,c_1336]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_9,negated_conjecture,
% 2.46/1.00      ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_640,plain,
% 2.46/1.00      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2507,plain,
% 2.46/1.00      ( v1_tops_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 2.46/1.00      inference(demodulation,[status(thm)],[c_1755,c_640]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2511,plain,
% 2.46/1.00      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_2246,c_2507]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_898,plain,
% 2.46/1.00      ( r1_tarski(sK1,sK1) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_901,plain,
% 2.46/1.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(contradiction,plain,
% 2.46/1.00      ( $false ),
% 2.46/1.00      inference(minisat,[status(thm)],[c_2511,c_901]) ).
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  ------                               Statistics
% 2.46/1.00  
% 2.46/1.00  ------ General
% 2.46/1.00  
% 2.46/1.00  abstr_ref_over_cycles:                  0
% 2.46/1.00  abstr_ref_under_cycles:                 0
% 2.46/1.00  gc_basic_clause_elim:                   0
% 2.46/1.00  forced_gc_time:                         0
% 2.46/1.00  parsing_time:                           0.016
% 2.46/1.00  unif_index_cands_time:                  0.
% 2.46/1.00  unif_index_add_time:                    0.
% 2.46/1.00  orderings_time:                         0.
% 2.46/1.00  out_proof_time:                         0.009
% 2.46/1.00  total_time:                             0.113
% 2.46/1.00  num_of_symbols:                         40
% 2.46/1.00  num_of_terms:                           1912
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing
% 2.46/1.00  
% 2.46/1.00  num_of_splits:                          0
% 2.46/1.00  num_of_split_atoms:                     0
% 2.46/1.00  num_of_reused_defs:                     0
% 2.46/1.00  num_eq_ax_congr_red:                    27
% 2.46/1.00  num_of_sem_filtered_clauses:            1
% 2.46/1.00  num_of_subtypes:                        0
% 2.46/1.00  monotx_restored_types:                  0
% 2.46/1.00  sat_num_of_epr_types:                   0
% 2.46/1.00  sat_num_of_non_cyclic_types:            0
% 2.46/1.00  sat_guarded_non_collapsed_types:        0
% 2.46/1.00  num_pure_diseq_elim:                    0
% 2.46/1.00  simp_replaced_by:                       0
% 2.46/1.00  res_preprocessed:                       68
% 2.46/1.00  prep_upred:                             0
% 2.46/1.00  prep_unflattend:                        1
% 2.46/1.00  smt_new_axioms:                         0
% 2.46/1.00  pred_elim_cands:                        3
% 2.46/1.00  pred_elim:                              1
% 2.46/1.00  pred_elim_cl:                           1
% 2.46/1.00  pred_elim_cycles:                       3
% 2.46/1.00  merged_defs:                            8
% 2.46/1.00  merged_defs_ncl:                        0
% 2.46/1.00  bin_hyper_res:                          9
% 2.46/1.00  prep_cycles:                            4
% 2.46/1.00  pred_elim_time:                         0.
% 2.46/1.00  splitting_time:                         0.
% 2.46/1.00  sem_filter_time:                        0.
% 2.46/1.00  monotx_time:                            0.
% 2.46/1.00  subtype_inf_time:                       0.
% 2.46/1.00  
% 2.46/1.00  ------ Problem properties
% 2.46/1.00  
% 2.46/1.00  clauses:                                12
% 2.46/1.00  conjectures:                            4
% 2.46/1.00  epr:                                    4
% 2.46/1.00  horn:                                   12
% 2.46/1.00  ground:                                 4
% 2.46/1.00  unary:                                  5
% 2.46/1.00  binary:                                 4
% 2.46/1.00  lits:                                   24
% 2.46/1.00  lits_eq:                                2
% 2.46/1.00  fd_pure:                                0
% 2.46/1.00  fd_pseudo:                              0
% 2.46/1.00  fd_cond:                                0
% 2.46/1.00  fd_pseudo_cond:                         1
% 2.46/1.00  ac_symbols:                             0
% 2.46/1.00  
% 2.46/1.00  ------ Propositional Solver
% 2.46/1.00  
% 2.46/1.00  prop_solver_calls:                      28
% 2.46/1.00  prop_fast_solver_calls:                 380
% 2.46/1.00  smt_solver_calls:                       0
% 2.46/1.00  smt_fast_solver_calls:                  0
% 2.46/1.00  prop_num_of_clauses:                    842
% 2.46/1.00  prop_preprocess_simplified:             2836
% 2.46/1.00  prop_fo_subsumed:                       4
% 2.46/1.00  prop_solver_time:                       0.
% 2.46/1.00  smt_solver_time:                        0.
% 2.46/1.00  smt_fast_solver_time:                   0.
% 2.46/1.00  prop_fast_solver_time:                  0.
% 2.46/1.00  prop_unsat_core_time:                   0.
% 2.46/1.00  
% 2.46/1.00  ------ QBF
% 2.46/1.00  
% 2.46/1.00  qbf_q_res:                              0
% 2.46/1.00  qbf_num_tautologies:                    0
% 2.46/1.00  qbf_prep_cycles:                        0
% 2.46/1.00  
% 2.46/1.00  ------ BMC1
% 2.46/1.00  
% 2.46/1.00  bmc1_current_bound:                     -1
% 2.46/1.00  bmc1_last_solved_bound:                 -1
% 2.46/1.00  bmc1_unsat_core_size:                   -1
% 2.46/1.00  bmc1_unsat_core_parents_size:           -1
% 2.46/1.00  bmc1_merge_next_fun:                    0
% 2.46/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation
% 2.46/1.00  
% 2.46/1.00  inst_num_of_clauses:                    239
% 2.46/1.00  inst_num_in_passive:                    38
% 2.46/1.00  inst_num_in_active:                     150
% 2.46/1.00  inst_num_in_unprocessed:                52
% 2.46/1.00  inst_num_of_loops:                      160
% 2.46/1.00  inst_num_of_learning_restarts:          0
% 2.46/1.00  inst_num_moves_active_passive:          6
% 2.46/1.00  inst_lit_activity:                      0
% 2.46/1.00  inst_lit_activity_moves:                0
% 2.46/1.00  inst_num_tautologies:                   0
% 2.46/1.00  inst_num_prop_implied:                  0
% 2.46/1.00  inst_num_existing_simplified:           0
% 2.46/1.00  inst_num_eq_res_simplified:             0
% 2.46/1.00  inst_num_child_elim:                    0
% 2.46/1.00  inst_num_of_dismatching_blockings:      88
% 2.46/1.00  inst_num_of_non_proper_insts:           407
% 2.46/1.00  inst_num_of_duplicates:                 0
% 2.46/1.00  inst_inst_num_from_inst_to_res:         0
% 2.46/1.00  inst_dismatching_checking_time:         0.
% 2.46/1.00  
% 2.46/1.00  ------ Resolution
% 2.46/1.00  
% 2.46/1.00  res_num_of_clauses:                     0
% 2.46/1.00  res_num_in_passive:                     0
% 2.46/1.00  res_num_in_active:                      0
% 2.46/1.00  res_num_of_loops:                       72
% 2.46/1.00  res_forward_subset_subsumed:            48
% 2.46/1.00  res_backward_subset_subsumed:           4
% 2.46/1.00  res_forward_subsumed:                   0
% 2.46/1.00  res_backward_subsumed:                  0
% 2.46/1.00  res_forward_subsumption_resolution:     0
% 2.46/1.00  res_backward_subsumption_resolution:    0
% 2.46/1.00  res_clause_to_clause_subsumption:       160
% 2.46/1.00  res_orphan_elimination:                 0
% 2.46/1.00  res_tautology_del:                      62
% 2.46/1.00  res_num_eq_res_simplified:              0
% 2.46/1.00  res_num_sel_changes:                    0
% 2.46/1.00  res_moves_from_active_to_pass:          0
% 2.46/1.00  
% 2.46/1.00  ------ Superposition
% 2.46/1.00  
% 2.46/1.00  sup_time_total:                         0.
% 2.46/1.00  sup_time_generating:                    0.
% 2.46/1.00  sup_time_sim_full:                      0.
% 2.46/1.00  sup_time_sim_immed:                     0.
% 2.46/1.00  
% 2.46/1.00  sup_num_of_clauses:                     43
% 2.46/1.00  sup_num_in_active:                      29
% 2.46/1.00  sup_num_in_passive:                     14
% 2.46/1.00  sup_num_of_loops:                       31
% 2.46/1.00  sup_fw_superposition:                   27
% 2.46/1.00  sup_bw_superposition:                   15
% 2.46/1.00  sup_immediate_simplified:               1
% 2.46/1.00  sup_given_eliminated:                   0
% 2.46/1.00  comparisons_done:                       0
% 2.46/1.00  comparisons_avoided:                    0
% 2.46/1.00  
% 2.46/1.00  ------ Simplifications
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  sim_fw_subset_subsumed:                 1
% 2.46/1.00  sim_bw_subset_subsumed:                 0
% 2.46/1.00  sim_fw_subsumed:                        0
% 2.46/1.00  sim_bw_subsumed:                        0
% 2.46/1.00  sim_fw_subsumption_res:                 0
% 2.46/1.00  sim_bw_subsumption_res:                 0
% 2.46/1.00  sim_tautology_del:                      4
% 2.46/1.00  sim_eq_tautology_del:                   1
% 2.46/1.00  sim_eq_res_simp:                        0
% 2.46/1.00  sim_fw_demodulated:                     0
% 2.46/1.00  sim_bw_demodulated:                     3
% 2.46/1.00  sim_light_normalised:                   0
% 2.46/1.00  sim_joinable_taut:                      0
% 2.46/1.00  sim_joinable_simp:                      0
% 2.46/1.00  sim_ac_normalised:                      0
% 2.46/1.00  sim_smt_subsumption:                    0
% 2.46/1.00  
%------------------------------------------------------------------------------
