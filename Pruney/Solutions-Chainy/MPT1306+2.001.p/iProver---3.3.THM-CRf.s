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
% DateTime   : Thu Dec  3 12:16:30 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 205 expanded)
%              Number of clauses        :   72 (  91 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  277 ( 634 expanded)
%              Number of equality atoms :  100 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v2_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v2_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22,f21])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_598,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_598,c_2])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_596,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1032,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_596])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_92,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_93,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_92])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_93])).

cnf(c_590,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_116])).

cnf(c_1662,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1032,c_590])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_115,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_93])).

cnf(c_591,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_1515,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_596])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_592,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_597,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_169,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_170,plain,
    ( ~ v2_tops_2(X0,sK0)
    | v2_tops_2(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_589,plain,
    ( v2_tops_2(X0,sK0) != iProver_top
    | v2_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_1148,plain,
    ( v2_tops_2(X0,sK0) != iProver_top
    | v2_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_589])).

cnf(c_1994,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | v2_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_1148])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,negated_conjecture,
    ( v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,plain,
    ( v2_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_827,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_996,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_997,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_824,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1121,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_1127,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_2163,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1994,c_15,c_17,c_997,c_1127])).

cnf(c_2774,plain,
    ( v2_tops_2(k9_subset_1(sK1,X0,X1),sK0) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_2163])).

cnf(c_4492,plain,
    ( v2_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_2774])).

cnf(c_730,plain,
    ( k2_subset_1(sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_300,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_736,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_979,plain,
    ( m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_980,plain,
    ( m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_301,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_860,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_1083,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1202,plain,
    ( k2_subset_1(sK1) != sK1
    | sK1 = k2_subset_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_302,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1226,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_682,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_748,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1))
    | X0 != k2_subset_1(sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_1741,plain,
    ( ~ m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1))
    | m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | sK1 != k2_subset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1742,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | sK1 != k2_subset_1(sK1)
    | m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2063,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_2064,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2063])).

cnf(c_4811,plain,
    ( v2_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4492,c_730,c_736,c_980,c_1202,c_1226,c_1742,c_2064])).

cnf(c_4818,plain,
    ( v2_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_4811])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_593,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1030,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_596])).

cnf(c_1173,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1030,c_590])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_595,plain,
    ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1240,plain,
    ( v2_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1173,c_595])).

cnf(c_5405,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4818,c_1240])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/0.99  
% 2.58/0.99  ------  iProver source info
% 2.58/0.99  
% 2.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/0.99  git: non_committed_changes: false
% 2.58/0.99  git: last_make_outside_of_git: false
% 2.58/0.99  
% 2.58/0.99  ------ 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options
% 2.58/0.99  
% 2.58/0.99  --out_options                           all
% 2.58/0.99  --tptp_safe_out                         true
% 2.58/0.99  --problem_path                          ""
% 2.58/0.99  --include_path                          ""
% 2.58/0.99  --clausifier                            res/vclausify_rel
% 2.58/0.99  --clausifier_options                    --mode clausify
% 2.58/0.99  --stdin                                 false
% 2.58/0.99  --stats_out                             all
% 2.58/0.99  
% 2.58/0.99  ------ General Options
% 2.58/0.99  
% 2.58/0.99  --fof                                   false
% 2.58/0.99  --time_out_real                         305.
% 2.58/0.99  --time_out_virtual                      -1.
% 2.58/0.99  --symbol_type_check                     false
% 2.58/0.99  --clausify_out                          false
% 2.58/0.99  --sig_cnt_out                           false
% 2.58/0.99  --trig_cnt_out                          false
% 2.58/0.99  --trig_cnt_out_tolerance                1.
% 2.58/0.99  --trig_cnt_out_sk_spl                   false
% 2.58/0.99  --abstr_cl_out                          false
% 2.58/0.99  
% 2.58/0.99  ------ Global Options
% 2.58/0.99  
% 2.58/0.99  --schedule                              default
% 2.58/0.99  --add_important_lit                     false
% 2.58/0.99  --prop_solver_per_cl                    1000
% 2.58/0.99  --min_unsat_core                        false
% 2.58/0.99  --soft_assumptions                      false
% 2.58/0.99  --soft_lemma_size                       3
% 2.58/0.99  --prop_impl_unit_size                   0
% 2.58/0.99  --prop_impl_unit                        []
% 2.58/0.99  --share_sel_clauses                     true
% 2.58/0.99  --reset_solvers                         false
% 2.58/0.99  --bc_imp_inh                            [conj_cone]
% 2.58/0.99  --conj_cone_tolerance                   3.
% 2.58/0.99  --extra_neg_conj                        none
% 2.58/0.99  --large_theory_mode                     true
% 2.58/0.99  --prolific_symb_bound                   200
% 2.58/0.99  --lt_threshold                          2000
% 2.58/0.99  --clause_weak_htbl                      true
% 2.58/0.99  --gc_record_bc_elim                     false
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing Options
% 2.58/0.99  
% 2.58/0.99  --preprocessing_flag                    true
% 2.58/0.99  --time_out_prep_mult                    0.1
% 2.58/0.99  --splitting_mode                        input
% 2.58/0.99  --splitting_grd                         true
% 2.58/0.99  --splitting_cvd                         false
% 2.58/0.99  --splitting_cvd_svl                     false
% 2.58/0.99  --splitting_nvd                         32
% 2.58/0.99  --sub_typing                            true
% 2.58/0.99  --prep_gs_sim                           true
% 2.58/0.99  --prep_unflatten                        true
% 2.58/0.99  --prep_res_sim                          true
% 2.58/0.99  --prep_upred                            true
% 2.58/0.99  --prep_sem_filter                       exhaustive
% 2.58/0.99  --prep_sem_filter_out                   false
% 2.58/0.99  --pred_elim                             true
% 2.58/0.99  --res_sim_input                         true
% 2.58/0.99  --eq_ax_congr_red                       true
% 2.58/0.99  --pure_diseq_elim                       true
% 2.58/0.99  --brand_transform                       false
% 2.58/0.99  --non_eq_to_eq                          false
% 2.58/0.99  --prep_def_merge                        true
% 2.58/0.99  --prep_def_merge_prop_impl              false
% 2.58/0.99  --prep_def_merge_mbd                    true
% 2.58/0.99  --prep_def_merge_tr_red                 false
% 2.58/0.99  --prep_def_merge_tr_cl                  false
% 2.58/0.99  --smt_preprocessing                     true
% 2.58/0.99  --smt_ac_axioms                         fast
% 2.58/0.99  --preprocessed_out                      false
% 2.58/0.99  --preprocessed_stats                    false
% 2.58/0.99  
% 2.58/0.99  ------ Abstraction refinement Options
% 2.58/0.99  
% 2.58/0.99  --abstr_ref                             []
% 2.58/0.99  --abstr_ref_prep                        false
% 2.58/0.99  --abstr_ref_until_sat                   false
% 2.58/0.99  --abstr_ref_sig_restrict                funpre
% 2.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.99  --abstr_ref_under                       []
% 2.58/0.99  
% 2.58/0.99  ------ SAT Options
% 2.58/0.99  
% 2.58/0.99  --sat_mode                              false
% 2.58/0.99  --sat_fm_restart_options                ""
% 2.58/0.99  --sat_gr_def                            false
% 2.58/0.99  --sat_epr_types                         true
% 2.58/0.99  --sat_non_cyclic_types                  false
% 2.58/0.99  --sat_finite_models                     false
% 2.58/0.99  --sat_fm_lemmas                         false
% 2.58/0.99  --sat_fm_prep                           false
% 2.58/0.99  --sat_fm_uc_incr                        true
% 2.58/0.99  --sat_out_model                         small
% 2.58/0.99  --sat_out_clauses                       false
% 2.58/0.99  
% 2.58/0.99  ------ QBF Options
% 2.58/0.99  
% 2.58/0.99  --qbf_mode                              false
% 2.58/0.99  --qbf_elim_univ                         false
% 2.58/0.99  --qbf_dom_inst                          none
% 2.58/0.99  --qbf_dom_pre_inst                      false
% 2.58/0.99  --qbf_sk_in                             false
% 2.58/0.99  --qbf_pred_elim                         true
% 2.58/0.99  --qbf_split                             512
% 2.58/0.99  
% 2.58/0.99  ------ BMC1 Options
% 2.58/0.99  
% 2.58/0.99  --bmc1_incremental                      false
% 2.58/0.99  --bmc1_axioms                           reachable_all
% 2.58/0.99  --bmc1_min_bound                        0
% 2.58/0.99  --bmc1_max_bound                        -1
% 2.58/0.99  --bmc1_max_bound_default                -1
% 2.58/0.99  --bmc1_symbol_reachability              true
% 2.58/0.99  --bmc1_property_lemmas                  false
% 2.58/0.99  --bmc1_k_induction                      false
% 2.58/0.99  --bmc1_non_equiv_states                 false
% 2.58/0.99  --bmc1_deadlock                         false
% 2.58/0.99  --bmc1_ucm                              false
% 2.58/0.99  --bmc1_add_unsat_core                   none
% 2.58/0.99  --bmc1_unsat_core_children              false
% 2.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.99  --bmc1_out_stat                         full
% 2.58/0.99  --bmc1_ground_init                      false
% 2.58/0.99  --bmc1_pre_inst_next_state              false
% 2.58/0.99  --bmc1_pre_inst_state                   false
% 2.58/0.99  --bmc1_pre_inst_reach_state             false
% 2.58/0.99  --bmc1_out_unsat_core                   false
% 2.58/0.99  --bmc1_aig_witness_out                  false
% 2.58/0.99  --bmc1_verbose                          false
% 2.58/0.99  --bmc1_dump_clauses_tptp                false
% 2.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.99  --bmc1_dump_file                        -
% 2.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.99  --bmc1_ucm_extend_mode                  1
% 2.58/0.99  --bmc1_ucm_init_mode                    2
% 2.58/0.99  --bmc1_ucm_cone_mode                    none
% 2.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.99  --bmc1_ucm_relax_model                  4
% 2.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.99  --bmc1_ucm_layered_model                none
% 2.58/0.99  --bmc1_ucm_max_lemma_size               10
% 2.58/0.99  
% 2.58/0.99  ------ AIG Options
% 2.58/0.99  
% 2.58/0.99  --aig_mode                              false
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation Options
% 2.58/0.99  
% 2.58/0.99  --instantiation_flag                    true
% 2.58/0.99  --inst_sos_flag                         false
% 2.58/0.99  --inst_sos_phase                        true
% 2.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel_side                     num_symb
% 2.58/0.99  --inst_solver_per_active                1400
% 2.58/0.99  --inst_solver_calls_frac                1.
% 2.58/0.99  --inst_passive_queue_type               priority_queues
% 2.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.99  --inst_passive_queues_freq              [25;2]
% 2.58/0.99  --inst_dismatching                      true
% 2.58/0.99  --inst_eager_unprocessed_to_passive     true
% 2.58/0.99  --inst_prop_sim_given                   true
% 2.58/0.99  --inst_prop_sim_new                     false
% 2.58/0.99  --inst_subs_new                         false
% 2.58/0.99  --inst_eq_res_simp                      false
% 2.58/0.99  --inst_subs_given                       false
% 2.58/0.99  --inst_orphan_elimination               true
% 2.58/0.99  --inst_learning_loop_flag               true
% 2.58/0.99  --inst_learning_start                   3000
% 2.58/0.99  --inst_learning_factor                  2
% 2.58/0.99  --inst_start_prop_sim_after_learn       3
% 2.58/0.99  --inst_sel_renew                        solver
% 2.58/0.99  --inst_lit_activity_flag                true
% 2.58/0.99  --inst_restr_to_given                   false
% 2.58/0.99  --inst_activity_threshold               500
% 2.58/0.99  --inst_out_proof                        true
% 2.58/0.99  
% 2.58/0.99  ------ Resolution Options
% 2.58/0.99  
% 2.58/0.99  --resolution_flag                       true
% 2.58/0.99  --res_lit_sel                           adaptive
% 2.58/0.99  --res_lit_sel_side                      none
% 2.58/0.99  --res_ordering                          kbo
% 2.58/0.99  --res_to_prop_solver                    active
% 2.58/0.99  --res_prop_simpl_new                    false
% 2.58/0.99  --res_prop_simpl_given                  true
% 2.58/0.99  --res_passive_queue_type                priority_queues
% 2.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.99  --res_passive_queues_freq               [15;5]
% 2.58/0.99  --res_forward_subs                      full
% 2.58/0.99  --res_backward_subs                     full
% 2.58/0.99  --res_forward_subs_resolution           true
% 2.58/0.99  --res_backward_subs_resolution          true
% 2.58/0.99  --res_orphan_elimination                true
% 2.58/0.99  --res_time_limit                        2.
% 2.58/0.99  --res_out_proof                         true
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Options
% 2.58/0.99  
% 2.58/0.99  --superposition_flag                    true
% 2.58/0.99  --sup_passive_queue_type                priority_queues
% 2.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.99  --demod_completeness_check              fast
% 2.58/0.99  --demod_use_ground                      true
% 2.58/0.99  --sup_to_prop_solver                    passive
% 2.58/0.99  --sup_prop_simpl_new                    true
% 2.58/0.99  --sup_prop_simpl_given                  true
% 2.58/0.99  --sup_fun_splitting                     false
% 2.58/0.99  --sup_smt_interval                      50000
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Simplification Setup
% 2.58/0.99  
% 2.58/0.99  --sup_indices_passive                   []
% 2.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_full_bw                           [BwDemod]
% 2.58/0.99  --sup_immed_triv                        [TrivRules]
% 2.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_immed_bw_main                     []
% 2.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  
% 2.58/0.99  ------ Combination Options
% 2.58/0.99  
% 2.58/0.99  --comb_res_mult                         3
% 2.58/0.99  --comb_sup_mult                         2
% 2.58/0.99  --comb_inst_mult                        10
% 2.58/0.99  
% 2.58/0.99  ------ Debug Options
% 2.58/0.99  
% 2.58/0.99  --dbg_backtrace                         false
% 2.58/0.99  --dbg_dump_prop_clauses                 false
% 2.58/0.99  --dbg_dump_prop_clauses_file            -
% 2.58/0.99  --dbg_out_stat                          false
% 2.58/0.99  ------ Parsing...
% 2.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/0.99  ------ Proving...
% 2.58/0.99  ------ Problem Properties 
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  clauses                                 13
% 2.58/0.99  conjectures                             4
% 2.58/0.99  EPR                                     2
% 2.58/0.99  Horn                                    13
% 2.58/0.99  unary                                   7
% 2.58/0.99  binary                                  4
% 2.58/0.99  lits                                    23
% 2.58/0.99  lits eq                                 3
% 2.58/0.99  fd_pure                                 0
% 2.58/0.99  fd_pseudo                               0
% 2.58/0.99  fd_cond                                 0
% 2.58/0.99  fd_pseudo_cond                          0
% 2.58/0.99  AC symbols                              0
% 2.58/0.99  
% 2.58/0.99  ------ Schedule dynamic 5 is on 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  ------ 
% 2.58/0.99  Current options:
% 2.58/0.99  ------ 
% 2.58/0.99  
% 2.58/0.99  ------ Input Options
% 2.58/0.99  
% 2.58/0.99  --out_options                           all
% 2.58/0.99  --tptp_safe_out                         true
% 2.58/0.99  --problem_path                          ""
% 2.58/0.99  --include_path                          ""
% 2.58/0.99  --clausifier                            res/vclausify_rel
% 2.58/0.99  --clausifier_options                    --mode clausify
% 2.58/0.99  --stdin                                 false
% 2.58/0.99  --stats_out                             all
% 2.58/0.99  
% 2.58/0.99  ------ General Options
% 2.58/0.99  
% 2.58/0.99  --fof                                   false
% 2.58/0.99  --time_out_real                         305.
% 2.58/0.99  --time_out_virtual                      -1.
% 2.58/0.99  --symbol_type_check                     false
% 2.58/0.99  --clausify_out                          false
% 2.58/0.99  --sig_cnt_out                           false
% 2.58/0.99  --trig_cnt_out                          false
% 2.58/0.99  --trig_cnt_out_tolerance                1.
% 2.58/0.99  --trig_cnt_out_sk_spl                   false
% 2.58/0.99  --abstr_cl_out                          false
% 2.58/0.99  
% 2.58/0.99  ------ Global Options
% 2.58/0.99  
% 2.58/0.99  --schedule                              default
% 2.58/0.99  --add_important_lit                     false
% 2.58/0.99  --prop_solver_per_cl                    1000
% 2.58/0.99  --min_unsat_core                        false
% 2.58/0.99  --soft_assumptions                      false
% 2.58/0.99  --soft_lemma_size                       3
% 2.58/0.99  --prop_impl_unit_size                   0
% 2.58/0.99  --prop_impl_unit                        []
% 2.58/0.99  --share_sel_clauses                     true
% 2.58/0.99  --reset_solvers                         false
% 2.58/0.99  --bc_imp_inh                            [conj_cone]
% 2.58/0.99  --conj_cone_tolerance                   3.
% 2.58/0.99  --extra_neg_conj                        none
% 2.58/0.99  --large_theory_mode                     true
% 2.58/0.99  --prolific_symb_bound                   200
% 2.58/0.99  --lt_threshold                          2000
% 2.58/0.99  --clause_weak_htbl                      true
% 2.58/0.99  --gc_record_bc_elim                     false
% 2.58/0.99  
% 2.58/0.99  ------ Preprocessing Options
% 2.58/0.99  
% 2.58/0.99  --preprocessing_flag                    true
% 2.58/0.99  --time_out_prep_mult                    0.1
% 2.58/0.99  --splitting_mode                        input
% 2.58/0.99  --splitting_grd                         true
% 2.58/0.99  --splitting_cvd                         false
% 2.58/0.99  --splitting_cvd_svl                     false
% 2.58/0.99  --splitting_nvd                         32
% 2.58/0.99  --sub_typing                            true
% 2.58/0.99  --prep_gs_sim                           true
% 2.58/0.99  --prep_unflatten                        true
% 2.58/0.99  --prep_res_sim                          true
% 2.58/0.99  --prep_upred                            true
% 2.58/0.99  --prep_sem_filter                       exhaustive
% 2.58/0.99  --prep_sem_filter_out                   false
% 2.58/0.99  --pred_elim                             true
% 2.58/0.99  --res_sim_input                         true
% 2.58/0.99  --eq_ax_congr_red                       true
% 2.58/0.99  --pure_diseq_elim                       true
% 2.58/0.99  --brand_transform                       false
% 2.58/0.99  --non_eq_to_eq                          false
% 2.58/0.99  --prep_def_merge                        true
% 2.58/0.99  --prep_def_merge_prop_impl              false
% 2.58/0.99  --prep_def_merge_mbd                    true
% 2.58/0.99  --prep_def_merge_tr_red                 false
% 2.58/0.99  --prep_def_merge_tr_cl                  false
% 2.58/0.99  --smt_preprocessing                     true
% 2.58/0.99  --smt_ac_axioms                         fast
% 2.58/0.99  --preprocessed_out                      false
% 2.58/0.99  --preprocessed_stats                    false
% 2.58/0.99  
% 2.58/0.99  ------ Abstraction refinement Options
% 2.58/0.99  
% 2.58/0.99  --abstr_ref                             []
% 2.58/0.99  --abstr_ref_prep                        false
% 2.58/0.99  --abstr_ref_until_sat                   false
% 2.58/0.99  --abstr_ref_sig_restrict                funpre
% 2.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/0.99  --abstr_ref_under                       []
% 2.58/0.99  
% 2.58/0.99  ------ SAT Options
% 2.58/0.99  
% 2.58/0.99  --sat_mode                              false
% 2.58/0.99  --sat_fm_restart_options                ""
% 2.58/0.99  --sat_gr_def                            false
% 2.58/0.99  --sat_epr_types                         true
% 2.58/0.99  --sat_non_cyclic_types                  false
% 2.58/0.99  --sat_finite_models                     false
% 2.58/0.99  --sat_fm_lemmas                         false
% 2.58/0.99  --sat_fm_prep                           false
% 2.58/0.99  --sat_fm_uc_incr                        true
% 2.58/0.99  --sat_out_model                         small
% 2.58/0.99  --sat_out_clauses                       false
% 2.58/0.99  
% 2.58/0.99  ------ QBF Options
% 2.58/0.99  
% 2.58/0.99  --qbf_mode                              false
% 2.58/0.99  --qbf_elim_univ                         false
% 2.58/0.99  --qbf_dom_inst                          none
% 2.58/0.99  --qbf_dom_pre_inst                      false
% 2.58/0.99  --qbf_sk_in                             false
% 2.58/0.99  --qbf_pred_elim                         true
% 2.58/0.99  --qbf_split                             512
% 2.58/0.99  
% 2.58/0.99  ------ BMC1 Options
% 2.58/0.99  
% 2.58/0.99  --bmc1_incremental                      false
% 2.58/0.99  --bmc1_axioms                           reachable_all
% 2.58/0.99  --bmc1_min_bound                        0
% 2.58/0.99  --bmc1_max_bound                        -1
% 2.58/0.99  --bmc1_max_bound_default                -1
% 2.58/0.99  --bmc1_symbol_reachability              true
% 2.58/0.99  --bmc1_property_lemmas                  false
% 2.58/0.99  --bmc1_k_induction                      false
% 2.58/0.99  --bmc1_non_equiv_states                 false
% 2.58/0.99  --bmc1_deadlock                         false
% 2.58/0.99  --bmc1_ucm                              false
% 2.58/0.99  --bmc1_add_unsat_core                   none
% 2.58/0.99  --bmc1_unsat_core_children              false
% 2.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/0.99  --bmc1_out_stat                         full
% 2.58/0.99  --bmc1_ground_init                      false
% 2.58/0.99  --bmc1_pre_inst_next_state              false
% 2.58/0.99  --bmc1_pre_inst_state                   false
% 2.58/0.99  --bmc1_pre_inst_reach_state             false
% 2.58/0.99  --bmc1_out_unsat_core                   false
% 2.58/0.99  --bmc1_aig_witness_out                  false
% 2.58/0.99  --bmc1_verbose                          false
% 2.58/0.99  --bmc1_dump_clauses_tptp                false
% 2.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.58/0.99  --bmc1_dump_file                        -
% 2.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.58/0.99  --bmc1_ucm_extend_mode                  1
% 2.58/0.99  --bmc1_ucm_init_mode                    2
% 2.58/0.99  --bmc1_ucm_cone_mode                    none
% 2.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.58/0.99  --bmc1_ucm_relax_model                  4
% 2.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/0.99  --bmc1_ucm_layered_model                none
% 2.58/0.99  --bmc1_ucm_max_lemma_size               10
% 2.58/0.99  
% 2.58/0.99  ------ AIG Options
% 2.58/0.99  
% 2.58/0.99  --aig_mode                              false
% 2.58/0.99  
% 2.58/0.99  ------ Instantiation Options
% 2.58/0.99  
% 2.58/0.99  --instantiation_flag                    true
% 2.58/0.99  --inst_sos_flag                         false
% 2.58/0.99  --inst_sos_phase                        true
% 2.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/0.99  --inst_lit_sel_side                     none
% 2.58/0.99  --inst_solver_per_active                1400
% 2.58/0.99  --inst_solver_calls_frac                1.
% 2.58/0.99  --inst_passive_queue_type               priority_queues
% 2.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/0.99  --inst_passive_queues_freq              [25;2]
% 2.58/0.99  --inst_dismatching                      true
% 2.58/0.99  --inst_eager_unprocessed_to_passive     true
% 2.58/0.99  --inst_prop_sim_given                   true
% 2.58/0.99  --inst_prop_sim_new                     false
% 2.58/0.99  --inst_subs_new                         false
% 2.58/0.99  --inst_eq_res_simp                      false
% 2.58/0.99  --inst_subs_given                       false
% 2.58/0.99  --inst_orphan_elimination               true
% 2.58/0.99  --inst_learning_loop_flag               true
% 2.58/0.99  --inst_learning_start                   3000
% 2.58/0.99  --inst_learning_factor                  2
% 2.58/0.99  --inst_start_prop_sim_after_learn       3
% 2.58/0.99  --inst_sel_renew                        solver
% 2.58/0.99  --inst_lit_activity_flag                true
% 2.58/0.99  --inst_restr_to_given                   false
% 2.58/0.99  --inst_activity_threshold               500
% 2.58/0.99  --inst_out_proof                        true
% 2.58/0.99  
% 2.58/0.99  ------ Resolution Options
% 2.58/0.99  
% 2.58/0.99  --resolution_flag                       false
% 2.58/0.99  --res_lit_sel                           adaptive
% 2.58/0.99  --res_lit_sel_side                      none
% 2.58/0.99  --res_ordering                          kbo
% 2.58/0.99  --res_to_prop_solver                    active
% 2.58/0.99  --res_prop_simpl_new                    false
% 2.58/0.99  --res_prop_simpl_given                  true
% 2.58/0.99  --res_passive_queue_type                priority_queues
% 2.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/0.99  --res_passive_queues_freq               [15;5]
% 2.58/0.99  --res_forward_subs                      full
% 2.58/0.99  --res_backward_subs                     full
% 2.58/0.99  --res_forward_subs_resolution           true
% 2.58/0.99  --res_backward_subs_resolution          true
% 2.58/0.99  --res_orphan_elimination                true
% 2.58/0.99  --res_time_limit                        2.
% 2.58/0.99  --res_out_proof                         true
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Options
% 2.58/0.99  
% 2.58/0.99  --superposition_flag                    true
% 2.58/0.99  --sup_passive_queue_type                priority_queues
% 2.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.58/0.99  --demod_completeness_check              fast
% 2.58/0.99  --demod_use_ground                      true
% 2.58/0.99  --sup_to_prop_solver                    passive
% 2.58/0.99  --sup_prop_simpl_new                    true
% 2.58/0.99  --sup_prop_simpl_given                  true
% 2.58/0.99  --sup_fun_splitting                     false
% 2.58/0.99  --sup_smt_interval                      50000
% 2.58/0.99  
% 2.58/0.99  ------ Superposition Simplification Setup
% 2.58/0.99  
% 2.58/0.99  --sup_indices_passive                   []
% 2.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_full_bw                           [BwDemod]
% 2.58/0.99  --sup_immed_triv                        [TrivRules]
% 2.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_immed_bw_main                     []
% 2.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/0.99  
% 2.58/0.99  ------ Combination Options
% 2.58/0.99  
% 2.58/0.99  --comb_res_mult                         3
% 2.58/0.99  --comb_sup_mult                         2
% 2.58/0.99  --comb_inst_mult                        10
% 2.58/0.99  
% 2.58/0.99  ------ Debug Options
% 2.58/0.99  
% 2.58/0.99  --dbg_backtrace                         false
% 2.58/0.99  --dbg_dump_prop_clauses                 false
% 2.58/0.99  --dbg_dump_prop_clauses_file            -
% 2.58/0.99  --dbg_out_stat                          false
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  ------ Proving...
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  % SZS status Theorem for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99   Resolution empty clause
% 2.58/0.99  
% 2.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  fof(f2,axiom,(
% 2.58/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f26,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f2])).
% 2.58/0.99  
% 2.58/0.99  fof(f4,axiom,(
% 2.58/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f28,plain,(
% 2.58/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f4])).
% 2.58/0.99  
% 2.58/0.99  fof(f3,axiom,(
% 2.58/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f27,plain,(
% 2.58/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.58/0.99    inference(cnf_transformation,[],[f3])).
% 2.58/0.99  
% 2.58/0.99  fof(f8,axiom,(
% 2.58/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f20,plain,(
% 2.58/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.58/0.99    inference(nnf_transformation,[],[f8])).
% 2.58/0.99  
% 2.58/0.99  fof(f32,plain,(
% 2.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f20])).
% 2.58/0.99  
% 2.58/0.99  fof(f6,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f15,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f6])).
% 2.58/0.99  
% 2.58/0.99  fof(f30,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f15])).
% 2.58/0.99  
% 2.58/0.99  fof(f7,axiom,(
% 2.58/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f31,plain,(
% 2.58/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f7])).
% 2.58/0.99  
% 2.58/0.99  fof(f40,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(definition_unfolding,[],[f30,f31])).
% 2.58/0.99  
% 2.58/0.99  fof(f33,plain,(
% 2.58/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f20])).
% 2.58/0.99  
% 2.58/0.99  fof(f5,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f14,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.58/0.99    inference(ennf_transformation,[],[f5])).
% 2.58/0.99  
% 2.58/0.99  fof(f29,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.99    inference(cnf_transformation,[],[f14])).
% 2.58/0.99  
% 2.58/0.99  fof(f10,conjecture,(
% 2.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f11,negated_conjecture,(
% 2.58/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.58/0.99    inference(negated_conjecture,[],[f10])).
% 2.58/0.99  
% 2.58/0.99  fof(f18,plain,(
% 2.58/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f11])).
% 2.58/0.99  
% 2.58/0.99  fof(f19,plain,(
% 2.58/0.99    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.58/0.99    inference(flattening,[],[f18])).
% 2.58/0.99  
% 2.58/0.99  fof(f23,plain,(
% 2.58/0.99    ( ! [X0,X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v2_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f22,plain,(
% 2.58/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v2_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f21,plain,(
% 2.58/0.99    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 2.58/0.99    introduced(choice_axiom,[])).
% 2.58/0.99  
% 2.58/0.99  fof(f24,plain,(
% 2.58/0.99    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 2.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22,f21])).
% 2.58/0.99  
% 2.58/0.99  fof(f36,plain,(
% 2.58/0.99    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.99    inference(cnf_transformation,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  fof(f9,axiom,(
% 2.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f16,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(ennf_transformation,[],[f9])).
% 2.58/0.99  
% 2.58/0.99  fof(f17,plain,(
% 2.58/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.58/0.99    inference(flattening,[],[f16])).
% 2.58/0.99  
% 2.58/0.99  fof(f34,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f17])).
% 2.58/0.99  
% 2.58/0.99  fof(f35,plain,(
% 2.58/0.99    l1_pre_topc(sK0)),
% 2.58/0.99    inference(cnf_transformation,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  fof(f38,plain,(
% 2.58/0.99    v2_tops_2(sK1,sK0)),
% 2.58/0.99    inference(cnf_transformation,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  fof(f1,axiom,(
% 2.58/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/0.99  
% 2.58/0.99  fof(f12,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.58/0.99    inference(ennf_transformation,[],[f1])).
% 2.58/0.99  
% 2.58/0.99  fof(f13,plain,(
% 2.58/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.58/0.99    inference(flattening,[],[f12])).
% 2.58/0.99  
% 2.58/0.99  fof(f25,plain,(
% 2.58/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.58/0.99    inference(cnf_transformation,[],[f13])).
% 2.58/0.99  
% 2.58/0.99  fof(f37,plain,(
% 2.58/0.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.99    inference(cnf_transformation,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  fof(f39,plain,(
% 2.58/0.99    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 2.58/0.99    inference(cnf_transformation,[],[f24])).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1,plain,
% 2.58/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_3,plain,
% 2.58/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_598,plain,
% 2.58/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2,plain,
% 2.58/0.99      ( k2_subset_1(X0) = X0 ),
% 2.58/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_604,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.58/0.99      inference(light_normalisation,[status(thm)],[c_598,c_2]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_7,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_596,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.58/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1032,plain,
% 2.58/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_604,c_596]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_6,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_92,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.58/0.99      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_93,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.58/0.99      inference(renaming,[status(thm)],[c_92]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_116,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1)
% 2.58/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.58/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_93]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_590,plain,
% 2.58/0.99      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 2.58/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_116]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1662,plain,
% 2.58/0.99      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_1032,c_590]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.58/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_115,plain,
% 2.58/0.99      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 2.58/0.99      | ~ r1_tarski(X2,X0) ),
% 2.58/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_93]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_591,plain,
% 2.58/0.99      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 2.58/0.99      | r1_tarski(X2,X0) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1515,plain,
% 2.58/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.58/0.99      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_591,c_596]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_12,negated_conjecture,
% 2.58/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.58/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_592,plain,
% 2.58/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_597,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.58/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_8,plain,
% 2.58/0.99      ( ~ v2_tops_2(X0,X1)
% 2.58/0.99      | v2_tops_2(X2,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.58/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.58/0.99      | ~ r1_tarski(X2,X0)
% 2.58/0.99      | ~ l1_pre_topc(X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_13,negated_conjecture,
% 2.58/0.99      ( l1_pre_topc(sK0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_169,plain,
% 2.58/0.99      ( ~ v2_tops_2(X0,X1)
% 2.58/0.99      | v2_tops_2(X2,X1)
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.58/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.58/0.99      | ~ r1_tarski(X2,X0)
% 2.58/0.99      | sK0 != X1 ),
% 2.58/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_170,plain,
% 2.58/0.99      ( ~ v2_tops_2(X0,sK0)
% 2.58/0.99      | v2_tops_2(X1,sK0)
% 2.58/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.58/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.58/0.99      | ~ r1_tarski(X1,X0) ),
% 2.58/0.99      inference(unflattening,[status(thm)],[c_169]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_589,plain,
% 2.58/0.99      ( v2_tops_2(X0,sK0) != iProver_top
% 2.58/0.99      | v2_tops_2(X1,sK0) = iProver_top
% 2.58/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.58/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.58/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1148,plain,
% 2.58/0.99      ( v2_tops_2(X0,sK0) != iProver_top
% 2.58/0.99      | v2_tops_2(X1,sK0) = iProver_top
% 2.58/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.58/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.58/0.99      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_597,c_589]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1994,plain,
% 2.58/0.99      ( v2_tops_2(X0,sK0) = iProver_top
% 2.58/0.99      | v2_tops_2(sK1,sK0) != iProver_top
% 2.58/0.99      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.58/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_592,c_1148]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_15,plain,
% 2.58/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_10,negated_conjecture,
% 2.58/0.99      ( v2_tops_2(sK1,sK0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_17,plain,
% 2.58/0.99      ( v2_tops_2(sK1,sK0) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_827,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.58/0.99      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_996,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.58/0.99      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_827]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_997,plain,
% 2.58/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.58/0.99      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_0,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.58/0.99      inference(cnf_transformation,[],[f25]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_824,plain,
% 2.58/0.99      ( ~ r1_tarski(X0,X1)
% 2.58/0.99      | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.58/0.99      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1121,plain,
% 2.58/0.99      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.58/0.99      | ~ r1_tarski(X0,sK1)
% 2.58/0.99      | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_824]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1127,plain,
% 2.58/0.99      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.58/0.99      | r1_tarski(X0,sK1) != iProver_top
% 2.58/0.99      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2163,plain,
% 2.58/0.99      ( v2_tops_2(X0,sK0) = iProver_top | r1_tarski(X0,sK1) != iProver_top ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_1994,c_15,c_17,c_997,c_1127]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2774,plain,
% 2.58/0.99      ( v2_tops_2(k9_subset_1(sK1,X0,X1),sK0) = iProver_top
% 2.58/0.99      | r1_tarski(X1,sK1) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_1515,c_2163]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4492,plain,
% 2.58/0.99      ( v2_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top
% 2.58/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_1662,c_2774]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_730,plain,
% 2.58/0.99      ( k2_subset_1(sK1) = sK1 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_300,plain,( X0 = X0 ),theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_736,plain,
% 2.58/0.99      ( sK1 = sK1 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_300]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_979,plain,
% 2.58/0.99      ( m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1)) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_980,plain,
% 2.58/0.99      ( m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_979]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_301,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_860,plain,
% 2.58/0.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_301]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1083,plain,
% 2.58/0.99      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_860]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1202,plain,
% 2.58/0.99      ( k2_subset_1(sK1) != sK1 | sK1 = k2_subset_1(sK1) | sK1 != sK1 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1083]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_302,plain,
% 2.58/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.58/0.99      theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1226,plain,
% 2.58/0.99      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_302]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_303,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.58/0.99      theory(equality) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_682,plain,
% 2.58/0.99      ( m1_subset_1(X0,X1)
% 2.58/0.99      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 2.58/0.99      | X1 != k1_zfmisc_1(X2)
% 2.58/0.99      | X0 != k2_subset_1(X2) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_303]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_748,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/0.99      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 2.58/0.99      | X0 != k2_subset_1(X1)
% 2.58/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_682]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1047,plain,
% 2.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK1))
% 2.58/0.99      | ~ m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1))
% 2.58/0.99      | X0 != k2_subset_1(sK1)
% 2.58/0.99      | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_748]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1741,plain,
% 2.58/0.99      ( ~ m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1))
% 2.58/0.99      | m1_subset_1(sK1,k1_zfmisc_1(sK1))
% 2.58/0.99      | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 2.58/0.99      | sK1 != k2_subset_1(sK1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_1047]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1742,plain,
% 2.58/0.99      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 2.58/0.99      | sK1 != k2_subset_1(sK1)
% 2.58/0.99      | m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(sK1)) != iProver_top
% 2.58/0.99      | m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_852,plain,
% 2.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) | r1_tarski(X0,sK1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2063,plain,
% 2.58/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) | r1_tarski(sK1,sK1) ),
% 2.58/0.99      inference(instantiation,[status(thm)],[c_852]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_2064,plain,
% 2.58/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
% 2.58/0.99      | r1_tarski(sK1,sK1) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_2063]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4811,plain,
% 2.58/0.99      ( v2_tops_2(k1_setfam_1(k2_tarski(X0,sK1)),sK0) = iProver_top ),
% 2.58/0.99      inference(global_propositional_subsumption,
% 2.58/0.99                [status(thm)],
% 2.58/0.99                [c_4492,c_730,c_736,c_980,c_1202,c_1226,c_1742,c_2064]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_4818,plain,
% 2.58/0.99      ( v2_tops_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) = iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_1,c_4811]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_11,negated_conjecture,
% 2.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.58/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_593,plain,
% 2.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1030,plain,
% 2.58/0.99      ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_593,c_596]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1173,plain,
% 2.58/0.99      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_1030,c_590]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_9,negated_conjecture,
% 2.58/0.99      ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 2.58/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_595,plain,
% 2.58/0.99      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 2.58/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_1240,plain,
% 2.58/0.99      ( v2_tops_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 2.58/0.99      inference(demodulation,[status(thm)],[c_1173,c_595]) ).
% 2.58/0.99  
% 2.58/0.99  cnf(c_5405,plain,
% 2.58/0.99      ( $false ),
% 2.58/0.99      inference(superposition,[status(thm)],[c_4818,c_1240]) ).
% 2.58/0.99  
% 2.58/0.99  
% 2.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/0.99  
% 2.58/0.99  ------                               Statistics
% 2.58/0.99  
% 2.58/0.99  ------ General
% 2.58/0.99  
% 2.58/0.99  abstr_ref_over_cycles:                  0
% 2.58/1.00  abstr_ref_under_cycles:                 0
% 2.58/1.00  gc_basic_clause_elim:                   0
% 2.58/1.00  forced_gc_time:                         0
% 2.58/1.00  parsing_time:                           0.009
% 2.58/1.00  unif_index_cands_time:                  0.
% 2.58/1.00  unif_index_add_time:                    0.
% 2.58/1.00  orderings_time:                         0.
% 2.58/1.00  out_proof_time:                         0.01
% 2.58/1.00  total_time:                             0.189
% 2.58/1.00  num_of_symbols:                         44
% 2.58/1.00  num_of_terms:                           4504
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing
% 2.58/1.00  
% 2.58/1.00  num_of_splits:                          0
% 2.58/1.00  num_of_split_atoms:                     0
% 2.58/1.00  num_of_reused_defs:                     0
% 2.58/1.00  num_eq_ax_congr_red:                    15
% 2.58/1.00  num_of_sem_filtered_clauses:            1
% 2.58/1.00  num_of_subtypes:                        0
% 2.58/1.00  monotx_restored_types:                  0
% 2.58/1.00  sat_num_of_epr_types:                   0
% 2.58/1.00  sat_num_of_non_cyclic_types:            0
% 2.58/1.00  sat_guarded_non_collapsed_types:        0
% 2.58/1.00  num_pure_diseq_elim:                    0
% 2.58/1.00  simp_replaced_by:                       0
% 2.58/1.00  res_preprocessed:                       70
% 2.58/1.00  prep_upred:                             0
% 2.58/1.00  prep_unflattend:                        1
% 2.58/1.00  smt_new_axioms:                         0
% 2.58/1.00  pred_elim_cands:                        3
% 2.58/1.00  pred_elim:                              1
% 2.58/1.00  pred_elim_cl:                           1
% 2.58/1.00  pred_elim_cycles:                       3
% 2.58/1.00  merged_defs:                            8
% 2.58/1.00  merged_defs_ncl:                        0
% 2.58/1.00  bin_hyper_res:                          10
% 2.58/1.00  prep_cycles:                            4
% 2.58/1.00  pred_elim_time:                         0.001
% 2.58/1.00  splitting_time:                         0.
% 2.58/1.00  sem_filter_time:                        0.
% 2.58/1.00  monotx_time:                            0.
% 2.58/1.00  subtype_inf_time:                       0.
% 2.58/1.00  
% 2.58/1.00  ------ Problem properties
% 2.58/1.00  
% 2.58/1.00  clauses:                                13
% 2.58/1.00  conjectures:                            4
% 2.58/1.00  epr:                                    2
% 2.58/1.00  horn:                                   13
% 2.58/1.00  ground:                                 4
% 2.58/1.00  unary:                                  7
% 2.58/1.00  binary:                                 4
% 2.58/1.00  lits:                                   23
% 2.58/1.00  lits_eq:                                3
% 2.58/1.00  fd_pure:                                0
% 2.58/1.00  fd_pseudo:                              0
% 2.58/1.00  fd_cond:                                0
% 2.58/1.00  fd_pseudo_cond:                         0
% 2.58/1.00  ac_symbols:                             0
% 2.58/1.00  
% 2.58/1.00  ------ Propositional Solver
% 2.58/1.00  
% 2.58/1.00  prop_solver_calls:                      30
% 2.58/1.00  prop_fast_solver_calls:                 488
% 2.58/1.00  smt_solver_calls:                       0
% 2.58/1.00  smt_fast_solver_calls:                  0
% 2.58/1.00  prop_num_of_clauses:                    2149
% 2.58/1.00  prop_preprocess_simplified:             4138
% 2.58/1.00  prop_fo_subsumed:                       13
% 2.58/1.00  prop_solver_time:                       0.
% 2.58/1.00  smt_solver_time:                        0.
% 2.58/1.00  smt_fast_solver_time:                   0.
% 2.58/1.00  prop_fast_solver_time:                  0.
% 2.58/1.00  prop_unsat_core_time:                   0.
% 2.58/1.00  
% 2.58/1.00  ------ QBF
% 2.58/1.00  
% 2.58/1.00  qbf_q_res:                              0
% 2.58/1.00  qbf_num_tautologies:                    0
% 2.58/1.00  qbf_prep_cycles:                        0
% 2.58/1.00  
% 2.58/1.00  ------ BMC1
% 2.58/1.00  
% 2.58/1.00  bmc1_current_bound:                     -1
% 2.58/1.00  bmc1_last_solved_bound:                 -1
% 2.58/1.00  bmc1_unsat_core_size:                   -1
% 2.58/1.00  bmc1_unsat_core_parents_size:           -1
% 2.58/1.00  bmc1_merge_next_fun:                    0
% 2.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation
% 2.58/1.00  
% 2.58/1.00  inst_num_of_clauses:                    609
% 2.58/1.00  inst_num_in_passive:                    38
% 2.58/1.00  inst_num_in_active:                     338
% 2.58/1.00  inst_num_in_unprocessed:                233
% 2.58/1.00  inst_num_of_loops:                      350
% 2.58/1.00  inst_num_of_learning_restarts:          0
% 2.58/1.00  inst_num_moves_active_passive:          7
% 2.58/1.00  inst_lit_activity:                      0
% 2.58/1.00  inst_lit_activity_moves:                0
% 2.58/1.00  inst_num_tautologies:                   0
% 2.58/1.00  inst_num_prop_implied:                  0
% 2.58/1.00  inst_num_existing_simplified:           0
% 2.58/1.00  inst_num_eq_res_simplified:             0
% 2.58/1.00  inst_num_child_elim:                    0
% 2.58/1.00  inst_num_of_dismatching_blockings:      240
% 2.58/1.00  inst_num_of_non_proper_insts:           739
% 2.58/1.00  inst_num_of_duplicates:                 0
% 2.58/1.00  inst_inst_num_from_inst_to_res:         0
% 2.58/1.00  inst_dismatching_checking_time:         0.
% 2.58/1.00  
% 2.58/1.00  ------ Resolution
% 2.58/1.00  
% 2.58/1.00  res_num_of_clauses:                     0
% 2.58/1.00  res_num_in_passive:                     0
% 2.58/1.00  res_num_in_active:                      0
% 2.58/1.00  res_num_of_loops:                       74
% 2.58/1.00  res_forward_subset_subsumed:            87
% 2.58/1.00  res_backward_subset_subsumed:           4
% 2.58/1.00  res_forward_subsumed:                   0
% 2.58/1.00  res_backward_subsumed:                  0
% 2.58/1.00  res_forward_subsumption_resolution:     0
% 2.58/1.00  res_backward_subsumption_resolution:    0
% 2.58/1.00  res_clause_to_clause_subsumption:       531
% 2.58/1.00  res_orphan_elimination:                 0
% 2.58/1.00  res_tautology_del:                      100
% 2.58/1.00  res_num_eq_res_simplified:              0
% 2.58/1.00  res_num_sel_changes:                    0
% 2.58/1.00  res_moves_from_active_to_pass:          0
% 2.58/1.00  
% 2.58/1.00  ------ Superposition
% 2.58/1.00  
% 2.58/1.00  sup_time_total:                         0.
% 2.58/1.00  sup_time_generating:                    0.
% 2.58/1.00  sup_time_sim_full:                      0.
% 2.58/1.00  sup_time_sim_immed:                     0.
% 2.58/1.00  
% 2.58/1.00  sup_num_of_clauses:                     123
% 2.58/1.00  sup_num_in_active:                      69
% 2.58/1.00  sup_num_in_passive:                     54
% 2.58/1.00  sup_num_of_loops:                       69
% 2.58/1.00  sup_fw_superposition:                   151
% 2.58/1.00  sup_bw_superposition:                   70
% 2.58/1.00  sup_immediate_simplified:               26
% 2.58/1.00  sup_given_eliminated:                   0
% 2.58/1.00  comparisons_done:                       0
% 2.58/1.00  comparisons_avoided:                    0
% 2.58/1.00  
% 2.58/1.00  ------ Simplifications
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  sim_fw_subset_subsumed:                 5
% 2.58/1.00  sim_bw_subset_subsumed:                 17
% 2.58/1.00  sim_fw_subsumed:                        12
% 2.58/1.00  sim_bw_subsumed:                        0
% 2.58/1.00  sim_fw_subsumption_res:                 1
% 2.58/1.00  sim_bw_subsumption_res:                 0
% 2.58/1.00  sim_tautology_del:                      12
% 2.58/1.00  sim_eq_tautology_del:                   0
% 2.58/1.00  sim_eq_res_simp:                        0
% 2.58/1.00  sim_fw_demodulated:                     5
% 2.58/1.00  sim_bw_demodulated:                     1
% 2.58/1.00  sim_light_normalised:                   5
% 2.58/1.00  sim_joinable_taut:                      0
% 2.58/1.00  sim_joinable_simp:                      0
% 2.58/1.00  sim_ac_normalised:                      0
% 2.58/1.00  sim_smt_subsumption:                    0
% 2.58/1.00  
%------------------------------------------------------------------------------
