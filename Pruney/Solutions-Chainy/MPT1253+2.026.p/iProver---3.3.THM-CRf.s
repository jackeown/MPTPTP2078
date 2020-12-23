%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:11 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 451 expanded)
%              Number of clauses        :   73 ( 163 expanded)
%              Number of leaves         :   14 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  298 (1385 expanded)
%              Number of equality atoms :  102 ( 204 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),sK1)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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

fof(f30,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29,f28])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_197,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_609,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) = iProver_top
    | r1_tarski(X0_43,X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47)))
    | m1_subset_1(k2_pre_topc(X0_47,X0_43),k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_611,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_47,X0_43),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_190,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_616,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47)
    | k9_subset_1(u1_struct_0(X0_47),k2_pre_topc(X0_47,X0_43),k2_pre_topc(X0_47,k3_subset_1(u1_struct_0(X0_47),X0_43))) = k2_tops_1(X0_47,X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_613,plain,
    ( k9_subset_1(u1_struct_0(X0_47),k2_pre_topc(X0_47,X0_43),k2_pre_topc(X0_47,k3_subset_1(u1_struct_0(X0_47),X0_43))) = k2_tops_1(X0_47,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_1287,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_613])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_246,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_1717,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1287,c_14,c_13,c_246])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_194,plain,
    ( ~ v4_pre_topc(X0_43,X0_47)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47)
    | k2_pre_topc(X0_47,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_612,plain,
    ( k2_pre_topc(X0_47,X0_43) = X0_43
    | v4_pre_topc(X0_43,X0_47) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_1100,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_612])).

cnf(c_12,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_243,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_1565,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1100,c_14,c_13,c_12,c_243])).

cnf(c_1719,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1717,c_1565])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_101,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_101])).

cnf(c_130,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_102])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_622,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X2_43,X1_43) != iProver_top
    | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_4324,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_622])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_736,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_737,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_4464,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4324,c_16,c_737])).

cnf(c_4465,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4464])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_102])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(X2_43,X0_43)
    | ~ r1_tarski(k3_subset_1(X1_43,X0_43),k3_subset_1(X1_43,X2_43)) ),
    inference(subtyping,[status(esa)],[c_128])).

cnf(c_620,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X2_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X0_43) = iProver_top
    | r1_tarski(k3_subset_1(X1_43,X0_43),k3_subset_1(X1_43,X2_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_4470,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4465,c_620])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_610,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_976,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_610])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_126,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_102])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | k5_xboole_0(X1_43,k1_setfam_1(k2_tarski(X1_43,X0_43))) = k3_subset_1(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_126])).

cnf(c_618,plain,
    ( k5_xboole_0(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))) = k3_subset_1(X0_43,X1_43)
    | r1_tarski(X1_43,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_1896,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_976,c_618])).

cnf(c_0,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_198,plain,
    ( r1_tarski(k5_xboole_0(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))),X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_608,plain,
    ( r1_tarski(k5_xboole_0(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))),X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_2023,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_608])).

cnf(c_1091,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | r1_tarski(k2_pre_topc(X0_47,X0_43),u1_struct_0(X0_47)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_610])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_127,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_102])).

cnf(c_187,plain,
    ( m1_subset_1(k9_subset_1(X0_43,X1_43,X2_43),k1_zfmisc_1(X0_43))
    | ~ r1_tarski(X2_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_127])).

cnf(c_619,plain,
    ( m1_subset_1(k9_subset_1(X0_43,X1_43,X2_43),k1_zfmisc_1(X0_43)) = iProver_top
    | r1_tarski(X2_43,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_1315,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(k9_subset_1(X1_43,X2_43,X0_43),X1_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_610])).

cnf(c_1721,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_1315])).

cnf(c_2855,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1721])).

cnf(c_15,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2981,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2855,c_15])).

cnf(c_2982,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2981])).

cnf(c_2987,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_2982])).

cnf(c_4984,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4470,c_16,c_18,c_2023,c_2987])).

cnf(c_4990,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_4984])).

cnf(c_5154,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4990,c_15])).

cnf(c_5159,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_5154])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5159,c_2023])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n017.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 09:36:46 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  % Running in FOF mode
% 3.72/0.88  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.88  
% 3.72/0.88  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.88  
% 3.72/0.88  ------  iProver source info
% 3.72/0.88  
% 3.72/0.88  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.88  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.88  git: non_committed_changes: false
% 3.72/0.88  git: last_make_outside_of_git: false
% 3.72/0.88  
% 3.72/0.88  ------ 
% 3.72/0.88  ------ Parsing...
% 3.72/0.88  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.88  
% 3.72/0.88  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/0.88  
% 3.72/0.88  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.88  
% 3.72/0.88  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.88  ------ Proving...
% 3.72/0.88  ------ Problem Properties 
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  clauses                                 15
% 3.72/0.88  conjectures                             4
% 3.72/0.88  EPR                                     2
% 3.72/0.88  Horn                                    15
% 3.72/0.88  unary                                   5
% 3.72/0.88  binary                                  4
% 3.72/0.88  lits                                    34
% 3.72/0.88  lits eq                                 3
% 3.72/0.88  fd_pure                                 0
% 3.72/0.88  fd_pseudo                               0
% 3.72/0.88  fd_cond                                 0
% 3.72/0.88  fd_pseudo_cond                          0
% 3.72/0.88  AC symbols                              0
% 3.72/0.88  
% 3.72/0.88  ------ Input Options Time Limit: Unbounded
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  ------ 
% 3.72/0.88  Current options:
% 3.72/0.88  ------ 
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  ------ Proving...
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  % SZS status Theorem for theBenchmark.p
% 3.72/0.88  
% 3.72/0.88  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.88  
% 3.72/0.88  fof(f8,axiom,(
% 3.72/0.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f27,plain,(
% 3.72/0.88    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.72/0.88    inference(nnf_transformation,[],[f8])).
% 3.72/0.88  
% 3.72/0.88  fof(f40,plain,(
% 3.72/0.88    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  
% 3.72/0.88  fof(f9,axiom,(
% 3.72/0.88    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f19,plain,(
% 3.72/0.88    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.72/0.88    inference(ennf_transformation,[],[f9])).
% 3.72/0.88  
% 3.72/0.88  fof(f20,plain,(
% 3.72/0.88    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.72/0.88    inference(flattening,[],[f19])).
% 3.72/0.88  
% 3.72/0.88  fof(f41,plain,(
% 3.72/0.88    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f20])).
% 3.72/0.88  
% 3.72/0.88  fof(f12,conjecture,(
% 3.72/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f13,negated_conjecture,(
% 3.72/0.88    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.72/0.88    inference(negated_conjecture,[],[f12])).
% 3.72/0.88  
% 3.72/0.88  fof(f24,plain,(
% 3.72/0.88    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f13])).
% 3.72/0.88  
% 3.72/0.88  fof(f25,plain,(
% 3.72/0.88    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.72/0.88    inference(flattening,[],[f24])).
% 3.72/0.88  
% 3.72/0.88  fof(f29,plain,(
% 3.72/0.88    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),sK1) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  
% 3.72/0.88  fof(f28,plain,(
% 3.72/0.88    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.72/0.88    introduced(choice_axiom,[])).
% 3.72/0.88  
% 3.72/0.88  fof(f30,plain,(
% 3.72/0.88    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.72/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29,f28])).
% 3.72/0.88  
% 3.72/0.88  fof(f45,plain,(
% 3.72/0.88    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.72/0.88    inference(cnf_transformation,[],[f30])).
% 3.72/0.88  
% 3.72/0.88  fof(f11,axiom,(
% 3.72/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f23,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f11])).
% 3.72/0.88  
% 3.72/0.88  fof(f43,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f23])).
% 3.72/0.88  
% 3.72/0.88  fof(f44,plain,(
% 3.72/0.88    l1_pre_topc(sK0)),
% 3.72/0.88    inference(cnf_transformation,[],[f30])).
% 3.72/0.88  
% 3.72/0.88  fof(f10,axiom,(
% 3.72/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f14,plain,(
% 3.72/0.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.72/0.88    inference(pure_predicate_removal,[],[f10])).
% 3.72/0.88  
% 3.72/0.88  fof(f21,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f14])).
% 3.72/0.88  
% 3.72/0.88  fof(f22,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.72/0.88    inference(flattening,[],[f21])).
% 3.72/0.88  
% 3.72/0.88  fof(f42,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f22])).
% 3.72/0.88  
% 3.72/0.88  fof(f46,plain,(
% 3.72/0.88    v4_pre_topc(sK1,sK0)),
% 3.72/0.88    inference(cnf_transformation,[],[f30])).
% 3.72/0.88  
% 3.72/0.88  fof(f6,axiom,(
% 3.72/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f18,plain,(
% 3.72/0.88    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.88    inference(ennf_transformation,[],[f6])).
% 3.72/0.88  
% 3.72/0.88  fof(f37,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f18])).
% 3.72/0.88  
% 3.72/0.88  fof(f39,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  
% 3.72/0.88  fof(f5,axiom,(
% 3.72/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f17,plain,(
% 3.72/0.88    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.88    inference(ennf_transformation,[],[f5])).
% 3.72/0.88  
% 3.72/0.88  fof(f26,plain,(
% 3.72/0.88    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.88    inference(nnf_transformation,[],[f17])).
% 3.72/0.88  
% 3.72/0.88  fof(f36,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f26])).
% 3.72/0.88  
% 3.72/0.88  fof(f47,plain,(
% 3.72/0.88    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.72/0.88    inference(cnf_transformation,[],[f30])).
% 3.72/0.88  
% 3.72/0.88  fof(f3,axiom,(
% 3.72/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f15,plain,(
% 3.72/0.88    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.88    inference(ennf_transformation,[],[f3])).
% 3.72/0.88  
% 3.72/0.88  fof(f33,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f15])).
% 3.72/0.88  
% 3.72/0.88  fof(f1,axiom,(
% 3.72/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f31,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f1])).
% 3.72/0.88  
% 3.72/0.88  fof(f7,axiom,(
% 3.72/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f38,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f7])).
% 3.72/0.88  
% 3.72/0.88  fof(f48,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.72/0.88    inference(definition_unfolding,[],[f31,f38])).
% 3.72/0.88  
% 3.72/0.88  fof(f50,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/0.88    inference(definition_unfolding,[],[f33,f48])).
% 3.72/0.88  
% 3.72/0.88  fof(f2,axiom,(
% 3.72/0.88    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f32,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f2])).
% 3.72/0.88  
% 3.72/0.88  fof(f49,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 3.72/0.88    inference(definition_unfolding,[],[f32,f48])).
% 3.72/0.88  
% 3.72/0.88  fof(f4,axiom,(
% 3.72/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.72/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.88  
% 3.72/0.88  fof(f16,plain,(
% 3.72/0.88    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.72/0.88    inference(ennf_transformation,[],[f4])).
% 3.72/0.88  
% 3.72/0.88  fof(f34,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f16])).
% 3.72/0.88  
% 3.72/0.88  cnf(c_6,plain,
% 3.72/0.88      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/0.88      inference(cnf_transformation,[],[f40]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_197,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.72/0.88      | ~ r1_tarski(X0_43,X1_43) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_6]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_609,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) = iProver_top
% 3.72/0.88      | r1_tarski(X0_43,X1_43) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_197]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_8,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/0.88      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/0.88      | ~ l1_pre_topc(X1) ),
% 3.72/0.88      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_195,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47)))
% 3.72/0.88      | m1_subset_1(k2_pre_topc(X0_47,X0_43),k1_zfmisc_1(u1_struct_0(X0_47)))
% 3.72/0.88      | ~ l1_pre_topc(X0_47) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_8]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_611,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 3.72/0.88      | m1_subset_1(k2_pre_topc(X0_47,X0_43),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 3.72/0.88      | l1_pre_topc(X0_47) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_13,negated_conjecture,
% 3.72/0.88      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.72/0.88      inference(cnf_transformation,[],[f45]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_190,negated_conjecture,
% 3.72/0.88      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_13]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_616,plain,
% 3.72/0.88      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_10,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/0.88      | ~ l1_pre_topc(X1)
% 3.72/0.88      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 3.72/0.88      inference(cnf_transformation,[],[f43]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_193,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47)))
% 3.72/0.88      | ~ l1_pre_topc(X0_47)
% 3.72/0.88      | k9_subset_1(u1_struct_0(X0_47),k2_pre_topc(X0_47,X0_43),k2_pre_topc(X0_47,k3_subset_1(u1_struct_0(X0_47),X0_43))) = k2_tops_1(X0_47,X0_43) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_10]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_613,plain,
% 3.72/0.88      ( k9_subset_1(u1_struct_0(X0_47),k2_pre_topc(X0_47,X0_43),k2_pre_topc(X0_47,k3_subset_1(u1_struct_0(X0_47),X0_43))) = k2_tops_1(X0_47,X0_43)
% 3.72/0.88      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 3.72/0.88      | l1_pre_topc(X0_47) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1287,plain,
% 3.72/0.88      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
% 3.72/0.88      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_616,c_613]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_14,negated_conjecture,
% 3.72/0.88      ( l1_pre_topc(sK0) ),
% 3.72/0.88      inference(cnf_transformation,[],[f44]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_246,plain,
% 3.72/0.88      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.72/0.88      | ~ l1_pre_topc(sK0)
% 3.72/0.88      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.72/0.88      inference(instantiation,[status(thm)],[c_193]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1717,plain,
% 3.72/0.88      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.72/0.88      inference(global_propositional_subsumption,
% 3.72/0.88                [status(thm)],
% 3.72/0.88                [c_1287,c_14,c_13,c_246]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_9,plain,
% 3.72/0.88      ( ~ v4_pre_topc(X0,X1)
% 3.72/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/0.88      | ~ l1_pre_topc(X1)
% 3.72/0.88      | k2_pre_topc(X1,X0) = X0 ),
% 3.72/0.88      inference(cnf_transformation,[],[f42]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_194,plain,
% 3.72/0.88      ( ~ v4_pre_topc(X0_43,X0_47)
% 3.72/0.88      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47)))
% 3.72/0.88      | ~ l1_pre_topc(X0_47)
% 3.72/0.88      | k2_pre_topc(X0_47,X0_43) = X0_43 ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_9]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_612,plain,
% 3.72/0.88      ( k2_pre_topc(X0_47,X0_43) = X0_43
% 3.72/0.88      | v4_pre_topc(X0_43,X0_47) != iProver_top
% 3.72/0.88      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 3.72/0.88      | l1_pre_topc(X0_47) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1100,plain,
% 3.72/0.88      ( k2_pre_topc(sK0,sK1) = sK1
% 3.72/0.88      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.72/0.88      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_616,c_612]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_12,negated_conjecture,
% 3.72/0.88      ( v4_pre_topc(sK1,sK0) ),
% 3.72/0.88      inference(cnf_transformation,[],[f46]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_243,plain,
% 3.72/0.88      ( ~ v4_pre_topc(sK1,sK0)
% 3.72/0.88      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.72/0.88      | ~ l1_pre_topc(sK0)
% 3.72/0.88      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.72/0.88      inference(instantiation,[status(thm)],[c_194]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1565,plain,
% 3.72/0.88      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.72/0.88      inference(global_propositional_subsumption,
% 3.72/0.88                [status(thm)],
% 3.72/0.88                [c_1100,c_14,c_13,c_12,c_243]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1719,plain,
% 3.72/0.88      ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.72/0.88      inference(light_normalisation,[status(thm)],[c_1717,c_1565]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_5,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.88      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.72/0.88      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
% 3.72/0.88      inference(cnf_transformation,[],[f37]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_101,plain,
% 3.72/0.88      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.72/0.88      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_102,plain,
% 3.72/0.88      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/0.88      inference(renaming,[status(thm)],[c_101]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_130,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.88      | ~ r1_tarski(X2,X1)
% 3.72/0.88      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X0))) ),
% 3.72/0.88      inference(bin_hyper_res,[status(thm)],[c_5,c_102]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_184,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.72/0.88      | ~ r1_tarski(X2_43,X1_43)
% 3.72/0.88      | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_130]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_622,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 3.72/0.88      | r1_tarski(X2_43,X1_43) != iProver_top
% 3.72/0.88      | r1_tarski(k3_subset_1(X1_43,X2_43),k3_subset_1(X1_43,k9_subset_1(X1_43,X2_43,X0_43))) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_4324,plain,
% 3.72/0.88      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
% 3.72/0.88      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_1719,c_622]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_16,plain,
% 3.72/0.88      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_7,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.72/0.88      inference(cnf_transformation,[],[f39]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_196,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.72/0.88      | r1_tarski(X0_43,X1_43) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_7]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_736,plain,
% 3.72/0.88      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.72/0.88      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.72/0.88      inference(instantiation,[status(thm)],[c_196]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_737,plain,
% 3.72/0.88      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_4464,plain,
% 3.72/0.88      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
% 3.72/0.88      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.72/0.88      inference(global_propositional_subsumption,
% 3.72/0.88                [status(thm)],
% 3.72/0.88                [c_4324,c_16,c_737]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_4465,plain,
% 3.72/0.88      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 3.72/0.88      inference(renaming,[status(thm)],[c_4464]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_3,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.88      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.72/0.88      | r1_tarski(X0,X2)
% 3.72/0.88      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 3.72/0.88      inference(cnf_transformation,[],[f36]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_128,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.88      | ~ r1_tarski(X2,X1)
% 3.72/0.88      | r1_tarski(X2,X0)
% 3.72/0.88      | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 3.72/0.88      inference(bin_hyper_res,[status(thm)],[c_3,c_102]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_186,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.72/0.88      | ~ r1_tarski(X2_43,X1_43)
% 3.72/0.88      | r1_tarski(X2_43,X0_43)
% 3.72/0.88      | ~ r1_tarski(k3_subset_1(X1_43,X0_43),k3_subset_1(X1_43,X2_43)) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_128]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_620,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 3.72/0.88      | r1_tarski(X2_43,X1_43) != iProver_top
% 3.72/0.88      | r1_tarski(X2_43,X0_43) = iProver_top
% 3.72/0.88      | r1_tarski(k3_subset_1(X1_43,X0_43),k3_subset_1(X1_43,X2_43)) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_4470,plain,
% 3.72/0.88      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 3.72/0.88      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_4465,c_620]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_11,negated_conjecture,
% 3.72/0.88      ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 3.72/0.88      inference(cnf_transformation,[],[f47]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_18,plain,
% 3.72/0.88      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_610,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 3.72/0.88      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_976,plain,
% 3.72/0.88      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_616,c_610]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.88      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 3.72/0.88      inference(cnf_transformation,[],[f50]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_126,plain,
% 3.72/0.88      ( ~ r1_tarski(X0,X1)
% 3.72/0.88      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 3.72/0.88      inference(bin_hyper_res,[status(thm)],[c_1,c_102]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_188,plain,
% 3.72/0.88      ( ~ r1_tarski(X0_43,X1_43)
% 3.72/0.88      | k5_xboole_0(X1_43,k1_setfam_1(k2_tarski(X1_43,X0_43))) = k3_subset_1(X1_43,X0_43) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_126]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_618,plain,
% 3.72/0.88      ( k5_xboole_0(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))) = k3_subset_1(X0_43,X1_43)
% 3.72/0.88      | r1_tarski(X1_43,X0_43) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1896,plain,
% 3.72/0.88      ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_976,c_618]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_0,plain,
% 3.72/0.88      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 3.72/0.88      inference(cnf_transformation,[],[f49]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_198,plain,
% 3.72/0.88      ( r1_tarski(k5_xboole_0(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))),X0_43) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_0]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_608,plain,
% 3.72/0.88      ( r1_tarski(k5_xboole_0(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))),X0_43) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_2023,plain,
% 3.72/0.88      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_1896,c_608]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1091,plain,
% 3.72/0.88      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 3.72/0.88      | r1_tarski(k2_pre_topc(X0_47,X0_43),u1_struct_0(X0_47)) = iProver_top
% 3.72/0.88      | l1_pre_topc(X0_47) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_611,c_610]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_2,plain,
% 3.72/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.88      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.72/0.88      inference(cnf_transformation,[],[f34]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_127,plain,
% 3.72/0.88      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.72/0.88      | ~ r1_tarski(X2,X0) ),
% 3.72/0.88      inference(bin_hyper_res,[status(thm)],[c_2,c_102]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_187,plain,
% 3.72/0.88      ( m1_subset_1(k9_subset_1(X0_43,X1_43,X2_43),k1_zfmisc_1(X0_43))
% 3.72/0.88      | ~ r1_tarski(X2_43,X0_43) ),
% 3.72/0.88      inference(subtyping,[status(esa)],[c_127]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_619,plain,
% 3.72/0.88      ( m1_subset_1(k9_subset_1(X0_43,X1_43,X2_43),k1_zfmisc_1(X0_43)) = iProver_top
% 3.72/0.88      | r1_tarski(X2_43,X0_43) != iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1315,plain,
% 3.72/0.88      ( r1_tarski(X0_43,X1_43) != iProver_top
% 3.72/0.88      | r1_tarski(k9_subset_1(X1_43,X2_43,X0_43),X1_43) = iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_619,c_610]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_1721,plain,
% 3.72/0.88      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 3.72/0.88      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_1719,c_1315]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_2855,plain,
% 3.72/0.88      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 3.72/0.88      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_1091,c_1721]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_15,plain,
% 3.72/0.88      ( l1_pre_topc(sK0) = iProver_top ),
% 3.72/0.88      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_2981,plain,
% 3.72/0.88      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 3.72/0.88      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.72/0.88      inference(global_propositional_subsumption,
% 3.72/0.88                [status(thm)],
% 3.72/0.88                [c_2855,c_15]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_2982,plain,
% 3.72/0.88      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.72/0.88      inference(renaming,[status(thm)],[c_2981]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_2987,plain,
% 3.72/0.88      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 3.72/0.88      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_609,c_2982]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_4984,plain,
% 3.72/0.88      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.72/0.88      inference(global_propositional_subsumption,
% 3.72/0.88                [status(thm)],
% 3.72/0.88                [c_4470,c_16,c_18,c_2023,c_2987]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_4990,plain,
% 3.72/0.88      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/0.88      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_611,c_4984]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_5154,plain,
% 3.72/0.88      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.72/0.88      inference(global_propositional_subsumption,
% 3.72/0.88                [status(thm)],
% 3.72/0.88                [c_4990,c_15]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(c_5159,plain,
% 3.72/0.88      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top ),
% 3.72/0.88      inference(superposition,[status(thm)],[c_609,c_5154]) ).
% 3.72/0.88  
% 3.72/0.88  cnf(contradiction,plain,
% 3.72/0.88      ( $false ),
% 3.72/0.88      inference(minisat,[status(thm)],[c_5159,c_2023]) ).
% 3.72/0.88  
% 3.72/0.88  
% 3.72/0.88  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.88  
% 3.72/0.88  ------                               Statistics
% 3.72/0.88  
% 3.72/0.88  ------ Selected
% 3.72/0.88  
% 3.72/0.88  total_time:                             0.251
% 3.72/0.88  
%------------------------------------------------------------------------------
