%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:23 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 271 expanded)
%              Number of clauses        :   58 ( 103 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  253 ( 870 expanded)
%              Number of equality atoms :   75 ( 125 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f26,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25,f24,f23])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_668,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1046,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_672])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_110,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_110])).

cnf(c_135,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_111])).

cnf(c_667,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_2827,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) ),
    inference(superposition,[status(thm)],[c_1046,c_667])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_111])).

cnf(c_665,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_1874,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_1046,c_665])).

cnf(c_2832,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2827,c_1874])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_669,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1045,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_669,c_672])).

cnf(c_1873,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1045,c_665])).

cnf(c_3587,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2832,c_1873])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_675,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1872,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_675,c_665])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_136,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_111])).

cnf(c_666,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_2348,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_666,c_672])).

cnf(c_673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_198,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_199,plain,
    ( ~ v1_tops_2(X0,sK0)
    | v1_tops_2(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_664,plain,
    ( v1_tops_2(X0,sK0) != iProver_top
    | v1_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_1058,plain,
    ( v1_tops_2(X0,sK0) != iProver_top
    | v1_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_664])).

cnf(c_1550,plain,
    ( v1_tops_2(X0,sK0) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_1058])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_941,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_942,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_849,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1019,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_1025,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_2013,plain,
    ( v1_tops_2(X0,sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1550,c_16,c_18,c_942,c_1025])).

cnf(c_2758,plain,
    ( v1_tops_2(k9_subset_1(sK1,X0,X1),sK0) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2348,c_2013])).

cnf(c_2994,plain,
    ( v1_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_2758])).

cnf(c_1387,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1390,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_4802,plain,
    ( v1_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2994,c_1390])).

cnf(c_4809,plain,
    ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3587,c_4802])).

cnf(c_10,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_671,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2023,plain,
    ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1873,c_671])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4809,c_2023])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.65/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.98  
% 2.65/0.98  ------  iProver source info
% 2.65/0.98  
% 2.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.98  git: non_committed_changes: false
% 2.65/0.98  git: last_make_outside_of_git: false
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     num_symb
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       true
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  ------ Parsing...
% 2.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.98  ------ Proving...
% 2.65/0.98  ------ Problem Properties 
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  clauses                                 13
% 2.65/0.98  conjectures                             4
% 2.65/0.98  EPR                                     4
% 2.65/0.98  Horn                                    13
% 2.65/0.98  unary                                   5
% 2.65/0.98  binary                                  5
% 2.65/0.98  lits                                    26
% 2.65/0.98  lits eq                                 3
% 2.65/0.98  fd_pure                                 0
% 2.65/0.98  fd_pseudo                               0
% 2.65/0.98  fd_cond                                 0
% 2.65/0.98  fd_pseudo_cond                          1
% 2.65/0.98  AC symbols                              0
% 2.65/0.98  
% 2.65/0.98  ------ Schedule dynamic 5 is on 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  Current options:
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     none
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       false
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ Proving...
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS status Theorem for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  fof(f9,conjecture,(
% 2.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f10,negated_conjecture,(
% 2.65/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.65/0.98    inference(negated_conjecture,[],[f9])).
% 2.65/0.98  
% 2.65/0.98  fof(f18,plain,(
% 2.65/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f10])).
% 2.65/0.98  
% 2.65/0.98  fof(f19,plain,(
% 2.65/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.65/0.98    inference(flattening,[],[f18])).
% 2.65/0.98  
% 2.65/0.98  fof(f25,plain,(
% 2.65/0.98    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f24,plain,(
% 2.65/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v1_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f23,plain,(
% 2.65/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f26,plain,(
% 2.65/0.98    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 2.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25,f24,f23])).
% 2.65/0.98  
% 2.65/0.98  fof(f39,plain,(
% 2.65/0.98    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.65/0.98    inference(cnf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  fof(f7,axiom,(
% 2.65/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f22,plain,(
% 2.65/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.65/0.98    inference(nnf_transformation,[],[f7])).
% 2.65/0.98  
% 2.65/0.98  fof(f35,plain,(
% 2.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f22])).
% 2.65/0.98  
% 2.65/0.98  fof(f3,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f13,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f3])).
% 2.65/0.98  
% 2.65/0.98  fof(f31,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f13])).
% 2.65/0.98  
% 2.65/0.98  fof(f36,plain,(
% 2.65/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f22])).
% 2.65/0.98  
% 2.65/0.98  fof(f5,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f15,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f5])).
% 2.65/0.98  
% 2.65/0.98  fof(f33,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f15])).
% 2.65/0.98  
% 2.65/0.98  fof(f6,axiom,(
% 2.65/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f34,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f6])).
% 2.65/0.98  
% 2.65/0.98  fof(f43,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.65/0.98    inference(definition_unfolding,[],[f33,f34])).
% 2.65/0.98  
% 2.65/0.98  fof(f40,plain,(
% 2.65/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.65/0.98    inference(cnf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  fof(f1,axiom,(
% 2.65/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f20,plain,(
% 2.65/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.98    inference(nnf_transformation,[],[f1])).
% 2.65/0.98  
% 2.65/0.98  fof(f21,plain,(
% 2.65/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.98    inference(flattening,[],[f20])).
% 2.65/0.98  
% 2.65/0.98  fof(f27,plain,(
% 2.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.65/0.98    inference(cnf_transformation,[],[f21])).
% 2.65/0.98  
% 2.65/0.98  fof(f45,plain,(
% 2.65/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.65/0.98    inference(equality_resolution,[],[f27])).
% 2.65/0.98  
% 2.65/0.98  fof(f4,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f14,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f4])).
% 2.65/0.98  
% 2.65/0.98  fof(f32,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f14])).
% 2.65/0.98  
% 2.65/0.98  fof(f8,axiom,(
% 2.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f16,plain,(
% 2.65/0.98    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f8])).
% 2.65/0.98  
% 2.65/0.98  fof(f17,plain,(
% 2.65/0.98    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.65/0.98    inference(flattening,[],[f16])).
% 2.65/0.98  
% 2.65/0.98  fof(f37,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f17])).
% 2.65/0.98  
% 2.65/0.98  fof(f38,plain,(
% 2.65/0.98    l1_pre_topc(sK0)),
% 2.65/0.98    inference(cnf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  fof(f41,plain,(
% 2.65/0.98    v1_tops_2(sK1,sK0)),
% 2.65/0.98    inference(cnf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  fof(f2,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f11,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.65/0.98    inference(ennf_transformation,[],[f2])).
% 2.65/0.98  
% 2.65/0.98  fof(f12,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.65/0.98    inference(flattening,[],[f11])).
% 2.65/0.98  
% 2.65/0.98  fof(f30,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f12])).
% 2.65/0.98  
% 2.65/0.98  fof(f42,plain,(
% 2.65/0.98    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 2.65/0.98    inference(cnf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  cnf(c_13,negated_conjecture,
% 2.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.65/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_668,plain,
% 2.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_8,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_672,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.65/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1046,plain,
% 2.65/0.98      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_668,c_672]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.65/0.98      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_7,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_110,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.65/0.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_111,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.65/0.98      inference(renaming,[status(thm)],[c_110]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_135,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,X1)
% 2.65/0.98      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.65/0.98      inference(bin_hyper_res,[status(thm)],[c_4,c_111]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_667,plain,
% 2.65/0.98      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 2.65/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_135]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2827,plain,
% 2.65/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1046,c_667]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_6,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.65/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_137,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,X1)
% 2.65/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.65/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_111]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_665,plain,
% 2.65/0.98      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.65/0.98      | r1_tarski(X2,X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1874,plain,
% 2.65/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1046,c_665]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2832,plain,
% 2.65/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1)) ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_2827,c_1874]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_12,negated_conjecture,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.65/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_669,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1045,plain,
% 2.65/0.98      ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_669,c_672]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1873,plain,
% 2.65/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1045,c_665]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3587,plain,
% 2.65/0.98      ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2832,c_1873]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2,plain,
% 2.65/0.98      ( r1_tarski(X0,X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_675,plain,
% 2.65/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1872,plain,
% 2.65/0.98      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_675,c_665]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.65/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_136,plain,
% 2.65/0.98      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 2.65/0.98      | ~ r1_tarski(X2,X0) ),
% 2.65/0.98      inference(bin_hyper_res,[status(thm)],[c_5,c_111]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_666,plain,
% 2.65/0.98      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 2.65/0.98      | r1_tarski(X2,X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2348,plain,
% 2.65/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.65/0.98      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_666,c_672]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_673,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.65/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_9,plain,
% 2.65/0.98      ( ~ v1_tops_2(X0,X1)
% 2.65/0.98      | v1_tops_2(X2,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.65/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.65/0.98      | ~ r1_tarski(X2,X0)
% 2.65/0.98      | ~ l1_pre_topc(X1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_14,negated_conjecture,
% 2.65/0.98      ( l1_pre_topc(sK0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_198,plain,
% 2.65/0.98      ( ~ v1_tops_2(X0,X1)
% 2.65/0.98      | v1_tops_2(X2,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.65/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.65/0.98      | ~ r1_tarski(X2,X0)
% 2.65/0.98      | sK0 != X1 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_199,plain,
% 2.65/0.98      ( ~ v1_tops_2(X0,sK0)
% 2.65/0.98      | v1_tops_2(X1,sK0)
% 2.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.65/0.98      | ~ r1_tarski(X1,X0) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_198]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_664,plain,
% 2.65/0.98      ( v1_tops_2(X0,sK0) != iProver_top
% 2.65/0.98      | v1_tops_2(X1,sK0) = iProver_top
% 2.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.65/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1058,plain,
% 2.65/0.98      ( v1_tops_2(X0,sK0) != iProver_top
% 2.65/0.98      | v1_tops_2(X1,sK0) = iProver_top
% 2.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.65/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.65/0.98      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_673,c_664]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1550,plain,
% 2.65/0.98      ( v1_tops_2(X0,sK0) = iProver_top
% 2.65/0.98      | v1_tops_2(sK1,sK0) != iProver_top
% 2.65/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_668,c_1058]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_16,plain,
% 2.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_11,negated_conjecture,
% 2.65/0.98      ( v1_tops_2(sK1,sK0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_18,plain,
% 2.65/0.98      ( v1_tops_2(sK1,sK0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_838,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.65/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_941,plain,
% 2.65/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.65/0.98      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_838]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_942,plain,
% 2.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.65/0.98      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_849,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,X1)
% 2.65/0.98      | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1019,plain,
% 2.65/0.98      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.98      | ~ r1_tarski(X0,sK1)
% 2.65/0.98      | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_849]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1025,plain,
% 2.65/0.98      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.65/0.98      | r1_tarski(X0,sK1) != iProver_top
% 2.65/0.98      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2013,plain,
% 2.65/0.98      ( v1_tops_2(X0,sK0) = iProver_top
% 2.65/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_1550,c_16,c_18,c_942,c_1025]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2758,plain,
% 2.65/0.98      ( v1_tops_2(k9_subset_1(sK1,X0,X1),sK0) = iProver_top
% 2.65/0.98      | r1_tarski(X1,sK1) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2348,c_2013]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2994,plain,
% 2.65/0.98      ( v1_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top
% 2.65/0.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1872,c_2758]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1387,plain,
% 2.65/0.98      ( r1_tarski(sK1,sK1) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1390,plain,
% 2.65/0.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1387]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4802,plain,
% 2.65/0.98      ( v1_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2994,c_1390]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4809,plain,
% 2.65/0.98      ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_3587,c_4802]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_10,negated_conjecture,
% 2.65/0.98      ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_671,plain,
% 2.65/0.98      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2023,plain,
% 2.65/0.98      ( v1_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1873,c_671]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(contradiction,plain,
% 2.65/0.98      ( $false ),
% 2.65/0.98      inference(minisat,[status(thm)],[c_4809,c_2023]) ).
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  ------                               Statistics
% 2.65/0.98  
% 2.65/0.98  ------ General
% 2.65/0.98  
% 2.65/0.98  abstr_ref_over_cycles:                  0
% 2.65/0.98  abstr_ref_under_cycles:                 0
% 2.65/0.98  gc_basic_clause_elim:                   0
% 2.65/0.98  forced_gc_time:                         0
% 2.65/0.98  parsing_time:                           0.009
% 2.65/0.98  unif_index_cands_time:                  0.
% 2.65/0.98  unif_index_add_time:                    0.
% 2.65/0.98  orderings_time:                         0.
% 2.65/0.98  out_proof_time:                         0.008
% 2.65/0.98  total_time:                             0.174
% 2.65/0.98  num_of_symbols:                         43
% 2.65/0.98  num_of_terms:                           4828
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing
% 2.65/0.98  
% 2.65/0.98  num_of_splits:                          0
% 2.65/0.98  num_of_split_atoms:                     0
% 2.65/0.98  num_of_reused_defs:                     0
% 2.65/0.98  num_eq_ax_congr_red:                    12
% 2.65/0.98  num_of_sem_filtered_clauses:            1
% 2.65/0.98  num_of_subtypes:                        0
% 2.65/0.98  monotx_restored_types:                  0
% 2.65/0.98  sat_num_of_epr_types:                   0
% 2.65/0.98  sat_num_of_non_cyclic_types:            0
% 2.65/0.98  sat_guarded_non_collapsed_types:        0
% 2.65/0.98  num_pure_diseq_elim:                    0
% 2.65/0.98  simp_replaced_by:                       0
% 2.65/0.98  res_preprocessed:                       70
% 2.65/0.98  prep_upred:                             0
% 2.65/0.98  prep_unflattend:                        1
% 2.65/0.98  smt_new_axioms:                         0
% 2.65/0.98  pred_elim_cands:                        3
% 2.65/0.98  pred_elim:                              1
% 2.65/0.98  pred_elim_cl:                           1
% 2.65/0.98  pred_elim_cycles:                       3
% 2.65/0.98  merged_defs:                            8
% 2.65/0.98  merged_defs_ncl:                        0
% 2.65/0.98  bin_hyper_res:                          11
% 2.65/0.98  prep_cycles:                            4
% 2.65/0.98  pred_elim_time:                         0.001
% 2.65/0.98  splitting_time:                         0.
% 2.65/0.98  sem_filter_time:                        0.
% 2.65/0.98  monotx_time:                            0.
% 2.65/0.98  subtype_inf_time:                       0.
% 2.65/0.98  
% 2.65/0.98  ------ Problem properties
% 2.65/0.98  
% 2.65/0.98  clauses:                                13
% 2.65/0.98  conjectures:                            4
% 2.65/0.98  epr:                                    4
% 2.65/0.98  horn:                                   13
% 2.65/0.98  ground:                                 4
% 2.65/0.98  unary:                                  5
% 2.65/0.98  binary:                                 5
% 2.65/0.98  lits:                                   26
% 2.65/0.98  lits_eq:                                3
% 2.65/0.98  fd_pure:                                0
% 2.65/0.98  fd_pseudo:                              0
% 2.65/0.98  fd_cond:                                0
% 2.65/0.98  fd_pseudo_cond:                         1
% 2.65/0.98  ac_symbols:                             0
% 2.65/0.98  
% 2.65/0.98  ------ Propositional Solver
% 2.65/0.98  
% 2.65/0.98  prop_solver_calls:                      30
% 2.65/0.98  prop_fast_solver_calls:                 450
% 2.65/0.98  smt_solver_calls:                       0
% 2.65/0.98  smt_fast_solver_calls:                  0
% 2.65/0.98  prop_num_of_clauses:                    1851
% 2.65/0.98  prop_preprocess_simplified:             4225
% 2.65/0.98  prop_fo_subsumed:                       9
% 2.65/0.98  prop_solver_time:                       0.
% 2.65/0.98  smt_solver_time:                        0.
% 2.65/0.98  smt_fast_solver_time:                   0.
% 2.65/0.98  prop_fast_solver_time:                  0.
% 2.65/0.98  prop_unsat_core_time:                   0.
% 2.65/0.98  
% 2.65/0.98  ------ QBF
% 2.65/0.98  
% 2.65/0.98  qbf_q_res:                              0
% 2.65/0.98  qbf_num_tautologies:                    0
% 2.65/0.98  qbf_prep_cycles:                        0
% 2.65/0.98  
% 2.65/0.98  ------ BMC1
% 2.65/0.98  
% 2.65/0.98  bmc1_current_bound:                     -1
% 2.65/0.98  bmc1_last_solved_bound:                 -1
% 2.65/0.98  bmc1_unsat_core_size:                   -1
% 2.65/0.98  bmc1_unsat_core_parents_size:           -1
% 2.65/0.98  bmc1_merge_next_fun:                    0
% 2.65/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation
% 2.65/0.98  
% 2.65/0.98  inst_num_of_clauses:                    502
% 2.65/0.98  inst_num_in_passive:                    108
% 2.65/0.98  inst_num_in_active:                     257
% 2.65/0.98  inst_num_in_unprocessed:                137
% 2.65/0.98  inst_num_of_loops:                      270
% 2.65/0.98  inst_num_of_learning_restarts:          0
% 2.65/0.98  inst_num_moves_active_passive:          8
% 2.65/0.98  inst_lit_activity:                      0
% 2.65/0.98  inst_lit_activity_moves:                0
% 2.65/0.98  inst_num_tautologies:                   0
% 2.65/0.98  inst_num_prop_implied:                  0
% 2.65/0.98  inst_num_existing_simplified:           0
% 2.65/0.98  inst_num_eq_res_simplified:             0
% 2.65/0.98  inst_num_child_elim:                    0
% 2.65/0.98  inst_num_of_dismatching_blockings:      287
% 2.65/0.98  inst_num_of_non_proper_insts:           734
% 2.65/0.98  inst_num_of_duplicates:                 0
% 2.65/0.98  inst_inst_num_from_inst_to_res:         0
% 2.65/0.98  inst_dismatching_checking_time:         0.
% 2.65/0.98  
% 2.65/0.98  ------ Resolution
% 2.65/0.98  
% 2.65/0.98  res_num_of_clauses:                     0
% 2.65/0.98  res_num_in_passive:                     0
% 2.65/0.98  res_num_in_active:                      0
% 2.65/0.98  res_num_of_loops:                       74
% 2.65/0.98  res_forward_subset_subsumed:            79
% 2.65/0.98  res_backward_subset_subsumed:           4
% 2.65/0.98  res_forward_subsumed:                   0
% 2.65/0.98  res_backward_subsumed:                  0
% 2.65/0.98  res_forward_subsumption_resolution:     0
% 2.65/0.98  res_backward_subsumption_resolution:    0
% 2.65/0.98  res_clause_to_clause_subsumption:       415
% 2.65/0.98  res_orphan_elimination:                 0
% 2.65/0.98  res_tautology_del:                      122
% 2.65/0.98  res_num_eq_res_simplified:              0
% 2.65/0.98  res_num_sel_changes:                    0
% 2.65/0.98  res_moves_from_active_to_pass:          0
% 2.65/0.98  
% 2.65/0.98  ------ Superposition
% 2.65/0.98  
% 2.65/0.98  sup_time_total:                         0.
% 2.65/0.98  sup_time_generating:                    0.
% 2.65/0.98  sup_time_sim_full:                      0.
% 2.65/0.98  sup_time_sim_immed:                     0.
% 2.65/0.98  
% 2.65/0.98  sup_num_of_clauses:                     97
% 2.65/0.98  sup_num_in_active:                      53
% 2.65/0.98  sup_num_in_passive:                     44
% 2.65/0.98  sup_num_of_loops:                       53
% 2.65/0.98  sup_fw_superposition:                   68
% 2.65/0.98  sup_bw_superposition:                   69
% 2.65/0.98  sup_immediate_simplified:               38
% 2.65/0.98  sup_given_eliminated:                   0
% 2.65/0.98  comparisons_done:                       0
% 2.65/0.98  comparisons_avoided:                    0
% 2.65/0.98  
% 2.65/0.98  ------ Simplifications
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  sim_fw_subset_subsumed:                 11
% 2.65/0.98  sim_bw_subset_subsumed:                 9
% 2.65/0.98  sim_fw_subsumed:                        14
% 2.65/0.98  sim_bw_subsumed:                        0
% 2.65/0.98  sim_fw_subsumption_res:                 1
% 2.65/0.98  sim_bw_subsumption_res:                 0
% 2.65/0.98  sim_tautology_del:                      6
% 2.65/0.98  sim_eq_tautology_del:                   1
% 2.65/0.98  sim_eq_res_simp:                        0
% 2.65/0.98  sim_fw_demodulated:                     7
% 2.65/0.98  sim_bw_demodulated:                     1
% 2.65/0.98  sim_light_normalised:                   8
% 2.65/0.98  sim_joinable_taut:                      0
% 2.65/0.98  sim_joinable_simp:                      0
% 2.65/0.98  sim_ac_normalised:                      0
% 2.65/0.98  sim_smt_subsumption:                    0
% 2.65/0.98  
%------------------------------------------------------------------------------
