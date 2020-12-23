%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:42 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 265 expanded)
%              Number of clauses        :   47 (  65 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  226 ( 781 expanded)
%              Number of equality atoms :   93 ( 130 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33,f32])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f62])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f63])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_617,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_619,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1437,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_617,c_619])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_715,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_616])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_621,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1107,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_tops_1(sK0,sK1))))) = sK1 ),
    inference(superposition,[status(thm)],[c_715,c_621])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_620,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_984,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_620])).

cnf(c_1173,plain,
    ( r1_tarski(k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_tops_1(sK0,sK1)))),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_984])).

cnf(c_1514,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1437,c_1173])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_613,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_821,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_613])).

cnf(c_1245,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_617,c_821])).

cnf(c_6,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_207,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_209,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_207,c_13,c_12])).

cnf(c_1252,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1245,c_209])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_615,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_916,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_617,c_615])).

cnf(c_1258,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1252,c_916])).

cnf(c_1520,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1514,c_1258])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_618,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_630,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_618,c_209])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1520,c_630])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.65/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/1.01  
% 2.65/1.01  ------  iProver source info
% 2.65/1.01  
% 2.65/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.65/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/1.01  git: non_committed_changes: false
% 2.65/1.01  git: last_make_outside_of_git: false
% 2.65/1.01  
% 2.65/1.01  ------ 
% 2.65/1.01  
% 2.65/1.01  ------ Input Options
% 2.65/1.01  
% 2.65/1.01  --out_options                           all
% 2.65/1.01  --tptp_safe_out                         true
% 2.65/1.01  --problem_path                          ""
% 2.65/1.01  --include_path                          ""
% 2.65/1.01  --clausifier                            res/vclausify_rel
% 2.65/1.01  --clausifier_options                    --mode clausify
% 2.65/1.01  --stdin                                 false
% 2.65/1.01  --stats_out                             all
% 2.65/1.01  
% 2.65/1.01  ------ General Options
% 2.65/1.01  
% 2.65/1.01  --fof                                   false
% 2.65/1.01  --time_out_real                         305.
% 2.65/1.01  --time_out_virtual                      -1.
% 2.65/1.01  --symbol_type_check                     false
% 2.65/1.01  --clausify_out                          false
% 2.65/1.01  --sig_cnt_out                           false
% 2.65/1.01  --trig_cnt_out                          false
% 2.65/1.01  --trig_cnt_out_tolerance                1.
% 2.65/1.01  --trig_cnt_out_sk_spl                   false
% 2.65/1.01  --abstr_cl_out                          false
% 2.65/1.01  
% 2.65/1.01  ------ Global Options
% 2.65/1.01  
% 2.65/1.01  --schedule                              default
% 2.65/1.01  --add_important_lit                     false
% 2.65/1.01  --prop_solver_per_cl                    1000
% 2.65/1.01  --min_unsat_core                        false
% 2.65/1.01  --soft_assumptions                      false
% 2.65/1.01  --soft_lemma_size                       3
% 2.65/1.01  --prop_impl_unit_size                   0
% 2.65/1.01  --prop_impl_unit                        []
% 2.65/1.01  --share_sel_clauses                     true
% 2.65/1.01  --reset_solvers                         false
% 2.65/1.01  --bc_imp_inh                            [conj_cone]
% 2.65/1.01  --conj_cone_tolerance                   3.
% 2.65/1.01  --extra_neg_conj                        none
% 2.65/1.01  --large_theory_mode                     true
% 2.65/1.01  --prolific_symb_bound                   200
% 2.65/1.01  --lt_threshold                          2000
% 2.65/1.01  --clause_weak_htbl                      true
% 2.65/1.01  --gc_record_bc_elim                     false
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing Options
% 2.65/1.01  
% 2.65/1.01  --preprocessing_flag                    true
% 2.65/1.01  --time_out_prep_mult                    0.1
% 2.65/1.01  --splitting_mode                        input
% 2.65/1.01  --splitting_grd                         true
% 2.65/1.01  --splitting_cvd                         false
% 2.65/1.01  --splitting_cvd_svl                     false
% 2.65/1.01  --splitting_nvd                         32
% 2.65/1.01  --sub_typing                            true
% 2.65/1.01  --prep_gs_sim                           true
% 2.65/1.01  --prep_unflatten                        true
% 2.65/1.01  --prep_res_sim                          true
% 2.65/1.01  --prep_upred                            true
% 2.65/1.01  --prep_sem_filter                       exhaustive
% 2.65/1.01  --prep_sem_filter_out                   false
% 2.65/1.01  --pred_elim                             true
% 2.65/1.01  --res_sim_input                         true
% 2.65/1.01  --eq_ax_congr_red                       true
% 2.65/1.01  --pure_diseq_elim                       true
% 2.65/1.01  --brand_transform                       false
% 2.65/1.01  --non_eq_to_eq                          false
% 2.65/1.01  --prep_def_merge                        true
% 2.65/1.01  --prep_def_merge_prop_impl              false
% 2.65/1.01  --prep_def_merge_mbd                    true
% 2.65/1.01  --prep_def_merge_tr_red                 false
% 2.65/1.01  --prep_def_merge_tr_cl                  false
% 2.65/1.01  --smt_preprocessing                     true
% 2.65/1.01  --smt_ac_axioms                         fast
% 2.65/1.01  --preprocessed_out                      false
% 2.65/1.01  --preprocessed_stats                    false
% 2.65/1.01  
% 2.65/1.01  ------ Abstraction refinement Options
% 2.65/1.01  
% 2.65/1.01  --abstr_ref                             []
% 2.65/1.01  --abstr_ref_prep                        false
% 2.65/1.01  --abstr_ref_until_sat                   false
% 2.65/1.01  --abstr_ref_sig_restrict                funpre
% 2.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/1.01  --abstr_ref_under                       []
% 2.65/1.01  
% 2.65/1.01  ------ SAT Options
% 2.65/1.01  
% 2.65/1.01  --sat_mode                              false
% 2.65/1.01  --sat_fm_restart_options                ""
% 2.65/1.01  --sat_gr_def                            false
% 2.65/1.01  --sat_epr_types                         true
% 2.65/1.01  --sat_non_cyclic_types                  false
% 2.65/1.01  --sat_finite_models                     false
% 2.65/1.01  --sat_fm_lemmas                         false
% 2.65/1.01  --sat_fm_prep                           false
% 2.65/1.01  --sat_fm_uc_incr                        true
% 2.65/1.01  --sat_out_model                         small
% 2.65/1.01  --sat_out_clauses                       false
% 2.65/1.01  
% 2.65/1.01  ------ QBF Options
% 2.65/1.01  
% 2.65/1.01  --qbf_mode                              false
% 2.65/1.01  --qbf_elim_univ                         false
% 2.65/1.01  --qbf_dom_inst                          none
% 2.65/1.01  --qbf_dom_pre_inst                      false
% 2.65/1.01  --qbf_sk_in                             false
% 2.65/1.01  --qbf_pred_elim                         true
% 2.65/1.01  --qbf_split                             512
% 2.65/1.01  
% 2.65/1.01  ------ BMC1 Options
% 2.65/1.01  
% 2.65/1.01  --bmc1_incremental                      false
% 2.65/1.01  --bmc1_axioms                           reachable_all
% 2.65/1.01  --bmc1_min_bound                        0
% 2.65/1.01  --bmc1_max_bound                        -1
% 2.65/1.01  --bmc1_max_bound_default                -1
% 2.65/1.01  --bmc1_symbol_reachability              true
% 2.65/1.01  --bmc1_property_lemmas                  false
% 2.65/1.01  --bmc1_k_induction                      false
% 2.65/1.01  --bmc1_non_equiv_states                 false
% 2.65/1.01  --bmc1_deadlock                         false
% 2.65/1.01  --bmc1_ucm                              false
% 2.65/1.01  --bmc1_add_unsat_core                   none
% 2.65/1.01  --bmc1_unsat_core_children              false
% 2.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/1.01  --bmc1_out_stat                         full
% 2.65/1.01  --bmc1_ground_init                      false
% 2.65/1.01  --bmc1_pre_inst_next_state              false
% 2.65/1.01  --bmc1_pre_inst_state                   false
% 2.65/1.01  --bmc1_pre_inst_reach_state             false
% 2.65/1.01  --bmc1_out_unsat_core                   false
% 2.65/1.01  --bmc1_aig_witness_out                  false
% 2.65/1.01  --bmc1_verbose                          false
% 2.65/1.01  --bmc1_dump_clauses_tptp                false
% 2.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.65/1.01  --bmc1_dump_file                        -
% 2.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.65/1.01  --bmc1_ucm_extend_mode                  1
% 2.65/1.01  --bmc1_ucm_init_mode                    2
% 2.65/1.01  --bmc1_ucm_cone_mode                    none
% 2.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.65/1.01  --bmc1_ucm_relax_model                  4
% 2.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/1.01  --bmc1_ucm_layered_model                none
% 2.65/1.01  --bmc1_ucm_max_lemma_size               10
% 2.65/1.01  
% 2.65/1.01  ------ AIG Options
% 2.65/1.01  
% 2.65/1.01  --aig_mode                              false
% 2.65/1.01  
% 2.65/1.01  ------ Instantiation Options
% 2.65/1.01  
% 2.65/1.01  --instantiation_flag                    true
% 2.65/1.01  --inst_sos_flag                         false
% 2.65/1.01  --inst_sos_phase                        true
% 2.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel_side                     num_symb
% 2.65/1.01  --inst_solver_per_active                1400
% 2.65/1.01  --inst_solver_calls_frac                1.
% 2.65/1.01  --inst_passive_queue_type               priority_queues
% 2.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/1.01  --inst_passive_queues_freq              [25;2]
% 2.65/1.01  --inst_dismatching                      true
% 2.65/1.01  --inst_eager_unprocessed_to_passive     true
% 2.65/1.01  --inst_prop_sim_given                   true
% 2.65/1.01  --inst_prop_sim_new                     false
% 2.65/1.01  --inst_subs_new                         false
% 2.65/1.01  --inst_eq_res_simp                      false
% 2.65/1.01  --inst_subs_given                       false
% 2.65/1.01  --inst_orphan_elimination               true
% 2.65/1.01  --inst_learning_loop_flag               true
% 2.65/1.01  --inst_learning_start                   3000
% 2.65/1.01  --inst_learning_factor                  2
% 2.65/1.01  --inst_start_prop_sim_after_learn       3
% 2.65/1.01  --inst_sel_renew                        solver
% 2.65/1.01  --inst_lit_activity_flag                true
% 2.65/1.01  --inst_restr_to_given                   false
% 2.65/1.01  --inst_activity_threshold               500
% 2.65/1.01  --inst_out_proof                        true
% 2.65/1.01  
% 2.65/1.01  ------ Resolution Options
% 2.65/1.01  
% 2.65/1.01  --resolution_flag                       true
% 2.65/1.01  --res_lit_sel                           adaptive
% 2.65/1.01  --res_lit_sel_side                      none
% 2.65/1.01  --res_ordering                          kbo
% 2.65/1.01  --res_to_prop_solver                    active
% 2.65/1.01  --res_prop_simpl_new                    false
% 2.65/1.01  --res_prop_simpl_given                  true
% 2.65/1.01  --res_passive_queue_type                priority_queues
% 2.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/1.01  --res_passive_queues_freq               [15;5]
% 2.65/1.01  --res_forward_subs                      full
% 2.65/1.01  --res_backward_subs                     full
% 2.65/1.01  --res_forward_subs_resolution           true
% 2.65/1.01  --res_backward_subs_resolution          true
% 2.65/1.01  --res_orphan_elimination                true
% 2.65/1.01  --res_time_limit                        2.
% 2.65/1.01  --res_out_proof                         true
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Options
% 2.65/1.01  
% 2.65/1.01  --superposition_flag                    true
% 2.65/1.01  --sup_passive_queue_type                priority_queues
% 2.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.65/1.01  --demod_completeness_check              fast
% 2.65/1.01  --demod_use_ground                      true
% 2.65/1.01  --sup_to_prop_solver                    passive
% 2.65/1.01  --sup_prop_simpl_new                    true
% 2.65/1.01  --sup_prop_simpl_given                  true
% 2.65/1.01  --sup_fun_splitting                     false
% 2.65/1.01  --sup_smt_interval                      50000
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Simplification Setup
% 2.65/1.01  
% 2.65/1.01  --sup_indices_passive                   []
% 2.65/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_full_bw                           [BwDemod]
% 2.65/1.01  --sup_immed_triv                        [TrivRules]
% 2.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_immed_bw_main                     []
% 2.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  
% 2.65/1.01  ------ Combination Options
% 2.65/1.01  
% 2.65/1.01  --comb_res_mult                         3
% 2.65/1.01  --comb_sup_mult                         2
% 2.65/1.01  --comb_inst_mult                        10
% 2.65/1.01  
% 2.65/1.01  ------ Debug Options
% 2.65/1.01  
% 2.65/1.01  --dbg_backtrace                         false
% 2.65/1.01  --dbg_dump_prop_clauses                 false
% 2.65/1.01  --dbg_dump_prop_clauses_file            -
% 2.65/1.01  --dbg_out_stat                          false
% 2.65/1.01  ------ Parsing...
% 2.65/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/1.01  ------ Proving...
% 2.65/1.01  ------ Problem Properties 
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  clauses                                 11
% 2.65/1.01  conjectures                             2
% 2.65/1.01  EPR                                     0
% 2.65/1.01  Horn                                    11
% 2.65/1.01  unary                                   5
% 2.65/1.01  binary                                  6
% 2.65/1.01  lits                                    17
% 2.65/1.01  lits eq                                 6
% 2.65/1.01  fd_pure                                 0
% 2.65/1.01  fd_pseudo                               0
% 2.65/1.01  fd_cond                                 0
% 2.65/1.01  fd_pseudo_cond                          0
% 2.65/1.01  AC symbols                              0
% 2.65/1.01  
% 2.65/1.01  ------ Schedule dynamic 5 is on 
% 2.65/1.01  
% 2.65/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  ------ 
% 2.65/1.01  Current options:
% 2.65/1.01  ------ 
% 2.65/1.01  
% 2.65/1.01  ------ Input Options
% 2.65/1.01  
% 2.65/1.01  --out_options                           all
% 2.65/1.01  --tptp_safe_out                         true
% 2.65/1.01  --problem_path                          ""
% 2.65/1.01  --include_path                          ""
% 2.65/1.01  --clausifier                            res/vclausify_rel
% 2.65/1.01  --clausifier_options                    --mode clausify
% 2.65/1.01  --stdin                                 false
% 2.65/1.01  --stats_out                             all
% 2.65/1.01  
% 2.65/1.01  ------ General Options
% 2.65/1.01  
% 2.65/1.01  --fof                                   false
% 2.65/1.01  --time_out_real                         305.
% 2.65/1.01  --time_out_virtual                      -1.
% 2.65/1.01  --symbol_type_check                     false
% 2.65/1.01  --clausify_out                          false
% 2.65/1.01  --sig_cnt_out                           false
% 2.65/1.01  --trig_cnt_out                          false
% 2.65/1.01  --trig_cnt_out_tolerance                1.
% 2.65/1.01  --trig_cnt_out_sk_spl                   false
% 2.65/1.01  --abstr_cl_out                          false
% 2.65/1.01  
% 2.65/1.01  ------ Global Options
% 2.65/1.01  
% 2.65/1.01  --schedule                              default
% 2.65/1.01  --add_important_lit                     false
% 2.65/1.01  --prop_solver_per_cl                    1000
% 2.65/1.01  --min_unsat_core                        false
% 2.65/1.01  --soft_assumptions                      false
% 2.65/1.01  --soft_lemma_size                       3
% 2.65/1.01  --prop_impl_unit_size                   0
% 2.65/1.01  --prop_impl_unit                        []
% 2.65/1.01  --share_sel_clauses                     true
% 2.65/1.01  --reset_solvers                         false
% 2.65/1.01  --bc_imp_inh                            [conj_cone]
% 2.65/1.01  --conj_cone_tolerance                   3.
% 2.65/1.01  --extra_neg_conj                        none
% 2.65/1.01  --large_theory_mode                     true
% 2.65/1.01  --prolific_symb_bound                   200
% 2.65/1.01  --lt_threshold                          2000
% 2.65/1.01  --clause_weak_htbl                      true
% 2.65/1.01  --gc_record_bc_elim                     false
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing Options
% 2.65/1.01  
% 2.65/1.01  --preprocessing_flag                    true
% 2.65/1.01  --time_out_prep_mult                    0.1
% 2.65/1.01  --splitting_mode                        input
% 2.65/1.01  --splitting_grd                         true
% 2.65/1.01  --splitting_cvd                         false
% 2.65/1.01  --splitting_cvd_svl                     false
% 2.65/1.01  --splitting_nvd                         32
% 2.65/1.01  --sub_typing                            true
% 2.65/1.01  --prep_gs_sim                           true
% 2.65/1.01  --prep_unflatten                        true
% 2.65/1.01  --prep_res_sim                          true
% 2.65/1.01  --prep_upred                            true
% 2.65/1.01  --prep_sem_filter                       exhaustive
% 2.65/1.01  --prep_sem_filter_out                   false
% 2.65/1.01  --pred_elim                             true
% 2.65/1.01  --res_sim_input                         true
% 2.65/1.01  --eq_ax_congr_red                       true
% 2.65/1.01  --pure_diseq_elim                       true
% 2.65/1.01  --brand_transform                       false
% 2.65/1.01  --non_eq_to_eq                          false
% 2.65/1.01  --prep_def_merge                        true
% 2.65/1.01  --prep_def_merge_prop_impl              false
% 2.65/1.01  --prep_def_merge_mbd                    true
% 2.65/1.01  --prep_def_merge_tr_red                 false
% 2.65/1.01  --prep_def_merge_tr_cl                  false
% 2.65/1.01  --smt_preprocessing                     true
% 2.65/1.01  --smt_ac_axioms                         fast
% 2.65/1.01  --preprocessed_out                      false
% 2.65/1.01  --preprocessed_stats                    false
% 2.65/1.01  
% 2.65/1.01  ------ Abstraction refinement Options
% 2.65/1.01  
% 2.65/1.01  --abstr_ref                             []
% 2.65/1.01  --abstr_ref_prep                        false
% 2.65/1.01  --abstr_ref_until_sat                   false
% 2.65/1.01  --abstr_ref_sig_restrict                funpre
% 2.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/1.01  --abstr_ref_under                       []
% 2.65/1.01  
% 2.65/1.01  ------ SAT Options
% 2.65/1.01  
% 2.65/1.01  --sat_mode                              false
% 2.65/1.01  --sat_fm_restart_options                ""
% 2.65/1.01  --sat_gr_def                            false
% 2.65/1.01  --sat_epr_types                         true
% 2.65/1.01  --sat_non_cyclic_types                  false
% 2.65/1.01  --sat_finite_models                     false
% 2.65/1.01  --sat_fm_lemmas                         false
% 2.65/1.01  --sat_fm_prep                           false
% 2.65/1.01  --sat_fm_uc_incr                        true
% 2.65/1.01  --sat_out_model                         small
% 2.65/1.01  --sat_out_clauses                       false
% 2.65/1.01  
% 2.65/1.01  ------ QBF Options
% 2.65/1.01  
% 2.65/1.01  --qbf_mode                              false
% 2.65/1.01  --qbf_elim_univ                         false
% 2.65/1.01  --qbf_dom_inst                          none
% 2.65/1.01  --qbf_dom_pre_inst                      false
% 2.65/1.01  --qbf_sk_in                             false
% 2.65/1.01  --qbf_pred_elim                         true
% 2.65/1.01  --qbf_split                             512
% 2.65/1.01  
% 2.65/1.01  ------ BMC1 Options
% 2.65/1.01  
% 2.65/1.01  --bmc1_incremental                      false
% 2.65/1.01  --bmc1_axioms                           reachable_all
% 2.65/1.01  --bmc1_min_bound                        0
% 2.65/1.01  --bmc1_max_bound                        -1
% 2.65/1.01  --bmc1_max_bound_default                -1
% 2.65/1.01  --bmc1_symbol_reachability              true
% 2.65/1.01  --bmc1_property_lemmas                  false
% 2.65/1.01  --bmc1_k_induction                      false
% 2.65/1.01  --bmc1_non_equiv_states                 false
% 2.65/1.01  --bmc1_deadlock                         false
% 2.65/1.01  --bmc1_ucm                              false
% 2.65/1.01  --bmc1_add_unsat_core                   none
% 2.65/1.01  --bmc1_unsat_core_children              false
% 2.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/1.01  --bmc1_out_stat                         full
% 2.65/1.01  --bmc1_ground_init                      false
% 2.65/1.01  --bmc1_pre_inst_next_state              false
% 2.65/1.01  --bmc1_pre_inst_state                   false
% 2.65/1.01  --bmc1_pre_inst_reach_state             false
% 2.65/1.01  --bmc1_out_unsat_core                   false
% 2.65/1.01  --bmc1_aig_witness_out                  false
% 2.65/1.01  --bmc1_verbose                          false
% 2.65/1.01  --bmc1_dump_clauses_tptp                false
% 2.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.65/1.01  --bmc1_dump_file                        -
% 2.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.65/1.01  --bmc1_ucm_extend_mode                  1
% 2.65/1.01  --bmc1_ucm_init_mode                    2
% 2.65/1.01  --bmc1_ucm_cone_mode                    none
% 2.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.65/1.01  --bmc1_ucm_relax_model                  4
% 2.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/1.01  --bmc1_ucm_layered_model                none
% 2.65/1.01  --bmc1_ucm_max_lemma_size               10
% 2.65/1.01  
% 2.65/1.01  ------ AIG Options
% 2.65/1.01  
% 2.65/1.01  --aig_mode                              false
% 2.65/1.01  
% 2.65/1.01  ------ Instantiation Options
% 2.65/1.01  
% 2.65/1.01  --instantiation_flag                    true
% 2.65/1.01  --inst_sos_flag                         false
% 2.65/1.01  --inst_sos_phase                        true
% 2.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel_side                     none
% 2.65/1.01  --inst_solver_per_active                1400
% 2.65/1.01  --inst_solver_calls_frac                1.
% 2.65/1.01  --inst_passive_queue_type               priority_queues
% 2.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/1.01  --inst_passive_queues_freq              [25;2]
% 2.65/1.01  --inst_dismatching                      true
% 2.65/1.01  --inst_eager_unprocessed_to_passive     true
% 2.65/1.01  --inst_prop_sim_given                   true
% 2.65/1.01  --inst_prop_sim_new                     false
% 2.65/1.01  --inst_subs_new                         false
% 2.65/1.01  --inst_eq_res_simp                      false
% 2.65/1.01  --inst_subs_given                       false
% 2.65/1.01  --inst_orphan_elimination               true
% 2.65/1.01  --inst_learning_loop_flag               true
% 2.65/1.01  --inst_learning_start                   3000
% 2.65/1.01  --inst_learning_factor                  2
% 2.65/1.01  --inst_start_prop_sim_after_learn       3
% 2.65/1.01  --inst_sel_renew                        solver
% 2.65/1.01  --inst_lit_activity_flag                true
% 2.65/1.01  --inst_restr_to_given                   false
% 2.65/1.01  --inst_activity_threshold               500
% 2.65/1.01  --inst_out_proof                        true
% 2.65/1.01  
% 2.65/1.01  ------ Resolution Options
% 2.65/1.01  
% 2.65/1.01  --resolution_flag                       false
% 2.65/1.01  --res_lit_sel                           adaptive
% 2.65/1.01  --res_lit_sel_side                      none
% 2.65/1.01  --res_ordering                          kbo
% 2.65/1.01  --res_to_prop_solver                    active
% 2.65/1.01  --res_prop_simpl_new                    false
% 2.65/1.01  --res_prop_simpl_given                  true
% 2.65/1.01  --res_passive_queue_type                priority_queues
% 2.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/1.01  --res_passive_queues_freq               [15;5]
% 2.65/1.01  --res_forward_subs                      full
% 2.65/1.01  --res_backward_subs                     full
% 2.65/1.01  --res_forward_subs_resolution           true
% 2.65/1.01  --res_backward_subs_resolution          true
% 2.65/1.01  --res_orphan_elimination                true
% 2.65/1.01  --res_time_limit                        2.
% 2.65/1.01  --res_out_proof                         true
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Options
% 2.65/1.01  
% 2.65/1.01  --superposition_flag                    true
% 2.65/1.01  --sup_passive_queue_type                priority_queues
% 2.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.65/1.01  --demod_completeness_check              fast
% 2.65/1.01  --demod_use_ground                      true
% 2.65/1.01  --sup_to_prop_solver                    passive
% 2.65/1.01  --sup_prop_simpl_new                    true
% 2.65/1.01  --sup_prop_simpl_given                  true
% 2.65/1.01  --sup_fun_splitting                     false
% 2.65/1.01  --sup_smt_interval                      50000
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Simplification Setup
% 2.65/1.01  
% 2.65/1.01  --sup_indices_passive                   []
% 2.65/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_full_bw                           [BwDemod]
% 2.65/1.01  --sup_immed_triv                        [TrivRules]
% 2.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_immed_bw_main                     []
% 2.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  
% 2.65/1.01  ------ Combination Options
% 2.65/1.01  
% 2.65/1.01  --comb_res_mult                         3
% 2.65/1.01  --comb_sup_mult                         2
% 2.65/1.01  --comb_inst_mult                        10
% 2.65/1.01  
% 2.65/1.01  ------ Debug Options
% 2.65/1.01  
% 2.65/1.01  --dbg_backtrace                         false
% 2.65/1.01  --dbg_dump_prop_clauses                 false
% 2.65/1.01  --dbg_dump_prop_clauses_file            -
% 2.65/1.01  --dbg_out_stat                          false
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  ------ Proving...
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  % SZS status Theorem for theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  fof(f18,conjecture,(
% 2.65/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f19,negated_conjecture,(
% 2.65/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 2.65/1.01    inference(negated_conjecture,[],[f18])).
% 2.65/1.01  
% 2.65/1.01  fof(f29,plain,(
% 2.65/1.01    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.65/1.01    inference(ennf_transformation,[],[f19])).
% 2.65/1.01  
% 2.65/1.01  fof(f30,plain,(
% 2.65/1.01    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.65/1.01    inference(flattening,[],[f29])).
% 2.65/1.01  
% 2.65/1.01  fof(f33,plain,(
% 2.65/1.01    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.65/1.01    introduced(choice_axiom,[])).
% 2.65/1.01  
% 2.65/1.01  fof(f32,plain,(
% 2.65/1.01    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.65/1.01    introduced(choice_axiom,[])).
% 2.65/1.01  
% 2.65/1.01  fof(f34,plain,(
% 2.65/1.01    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33,f32])).
% 2.65/1.01  
% 2.65/1.01  fof(f54,plain,(
% 2.65/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.65/1.01    inference(cnf_transformation,[],[f34])).
% 2.65/1.01  
% 2.65/1.01  fof(f11,axiom,(
% 2.65/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f21,plain,(
% 2.65/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.65/1.01    inference(ennf_transformation,[],[f11])).
% 2.65/1.01  
% 2.65/1.01  fof(f45,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.65/1.01    inference(cnf_transformation,[],[f21])).
% 2.65/1.01  
% 2.65/1.01  fof(f2,axiom,(
% 2.65/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f36,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.65/1.01    inference(cnf_transformation,[],[f2])).
% 2.65/1.01  
% 2.65/1.01  fof(f12,axiom,(
% 2.65/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f46,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.65/1.01    inference(cnf_transformation,[],[f12])).
% 2.65/1.01  
% 2.65/1.01  fof(f5,axiom,(
% 2.65/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f39,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f5])).
% 2.65/1.01  
% 2.65/1.01  fof(f6,axiom,(
% 2.65/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f40,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f6])).
% 2.65/1.01  
% 2.65/1.01  fof(f7,axiom,(
% 2.65/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f41,plain,(
% 2.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f7])).
% 2.65/1.01  
% 2.65/1.01  fof(f8,axiom,(
% 2.65/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f42,plain,(
% 2.65/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f8])).
% 2.65/1.01  
% 2.65/1.01  fof(f9,axiom,(
% 2.65/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f43,plain,(
% 2.65/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f9])).
% 2.65/1.01  
% 2.65/1.01  fof(f10,axiom,(
% 2.65/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f44,plain,(
% 2.65/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f10])).
% 2.65/1.01  
% 2.65/1.01  fof(f57,plain,(
% 2.65/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f43,f44])).
% 2.65/1.01  
% 2.65/1.01  fof(f58,plain,(
% 2.65/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f42,f57])).
% 2.65/1.01  
% 2.65/1.01  fof(f59,plain,(
% 2.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f41,f58])).
% 2.65/1.01  
% 2.65/1.01  fof(f60,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f40,f59])).
% 2.65/1.01  
% 2.65/1.01  fof(f61,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f39,f60])).
% 2.65/1.01  
% 2.65/1.01  fof(f62,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.65/1.01    inference(definition_unfolding,[],[f46,f61])).
% 2.65/1.01  
% 2.65/1.01  fof(f63,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.65/1.01    inference(definition_unfolding,[],[f36,f62])).
% 2.65/1.01  
% 2.65/1.01  fof(f65,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.65/1.01    inference(definition_unfolding,[],[f45,f63])).
% 2.65/1.01  
% 2.65/1.01  fof(f17,axiom,(
% 2.65/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f28,plain,(
% 2.65/1.01    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/1.01    inference(ennf_transformation,[],[f17])).
% 2.65/1.01  
% 2.65/1.01  fof(f52,plain,(
% 2.65/1.01    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f28])).
% 2.65/1.01  
% 2.65/1.01  fof(f53,plain,(
% 2.65/1.01    l1_pre_topc(sK0)),
% 2.65/1.01    inference(cnf_transformation,[],[f34])).
% 2.65/1.01  
% 2.65/1.01  fof(f3,axiom,(
% 2.65/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f20,plain,(
% 2.65/1.01    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.65/1.01    inference(ennf_transformation,[],[f3])).
% 2.65/1.01  
% 2.65/1.01  fof(f37,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f20])).
% 2.65/1.01  
% 2.65/1.01  fof(f64,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f37,f63])).
% 2.65/1.01  
% 2.65/1.01  fof(f1,axiom,(
% 2.65/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f35,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f1])).
% 2.65/1.01  
% 2.65/1.01  fof(f4,axiom,(
% 2.65/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f38,plain,(
% 2.65/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.65/1.01    inference(cnf_transformation,[],[f4])).
% 2.65/1.01  
% 2.65/1.01  fof(f15,axiom,(
% 2.65/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f25,plain,(
% 2.65/1.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.65/1.01    inference(ennf_transformation,[],[f15])).
% 2.65/1.01  
% 2.65/1.01  fof(f26,plain,(
% 2.65/1.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.65/1.01    inference(flattening,[],[f25])).
% 2.65/1.01  
% 2.65/1.01  fof(f50,plain,(
% 2.65/1.01    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f26])).
% 2.65/1.01  
% 2.65/1.01  fof(f13,axiom,(
% 2.65/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f22,plain,(
% 2.65/1.01    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.65/1.01    inference(ennf_transformation,[],[f13])).
% 2.65/1.01  
% 2.65/1.01  fof(f23,plain,(
% 2.65/1.01    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.65/1.01    inference(flattening,[],[f22])).
% 2.65/1.01  
% 2.65/1.01  fof(f47,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f23])).
% 2.65/1.01  
% 2.65/1.01  fof(f14,axiom,(
% 2.65/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f24,plain,(
% 2.65/1.01    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/1.01    inference(ennf_transformation,[],[f14])).
% 2.65/1.01  
% 2.65/1.01  fof(f31,plain,(
% 2.65/1.01    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/1.01    inference(nnf_transformation,[],[f24])).
% 2.65/1.01  
% 2.65/1.01  fof(f48,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f31])).
% 2.65/1.01  
% 2.65/1.01  fof(f55,plain,(
% 2.65/1.01    v5_tops_1(sK1,sK0)),
% 2.65/1.01    inference(cnf_transformation,[],[f34])).
% 2.65/1.01  
% 2.65/1.01  fof(f16,axiom,(
% 2.65/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f27,plain,(
% 2.65/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/1.01    inference(ennf_transformation,[],[f16])).
% 2.65/1.01  
% 2.65/1.01  fof(f51,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f27])).
% 2.65/1.01  
% 2.65/1.01  fof(f56,plain,(
% 2.65/1.01    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 2.65/1.01    inference(cnf_transformation,[],[f34])).
% 2.65/1.01  
% 2.65/1.01  cnf(c_12,negated_conjecture,
% 2.65/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_617,plain,
% 2.65/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_3,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.65/1.01      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.65/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_619,plain,
% 2.65/1.01      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.65/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1437,plain,
% 2.65/1.01      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_617,c_619]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_9,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.65/1.01      | ~ l1_pre_topc(X1) ),
% 2.65/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_13,negated_conjecture,
% 2.65/1.01      ( l1_pre_topc(sK0) ),
% 2.65/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_215,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.65/1.01      | sK0 != X1 ),
% 2.65/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_216,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/1.01      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.65/1.01      inference(unflattening,[status(thm)],[c_215]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_616,plain,
% 2.65/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/1.01      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_715,plain,
% 2.65/1.01      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_617,c_616]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1,plain,
% 2.65/1.01      ( ~ r1_tarski(X0,X1)
% 2.65/1.01      | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ),
% 2.65/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_621,plain,
% 2.65/1.01      ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
% 2.65/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1107,plain,
% 2.65/1.01      ( k2_xboole_0(k1_tops_1(sK0,sK1),k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_tops_1(sK0,sK1))))) = sK1 ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_715,c_621]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_0,plain,
% 2.65/1.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.65/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_2,plain,
% 2.65/1.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 2.65/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_620,plain,
% 2.65/1.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_984,plain,
% 2.65/1.01      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_0,c_620]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1173,plain,
% 2.65/1.01      ( r1_tarski(k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_tops_1(sK0,sK1)))),sK1) = iProver_top ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_1107,c_984]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1514,plain,
% 2.65/1.01      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1) = iProver_top ),
% 2.65/1.01      inference(demodulation,[status(thm)],[c_1437,c_1173]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_7,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | ~ l1_pre_topc(X1) ),
% 2.65/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_239,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | sK0 != X1 ),
% 2.65/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_240,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/1.01      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/1.01      inference(unflattening,[status(thm)],[c_239]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_614,plain,
% 2.65/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/1.01      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_4,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | ~ l1_pre_topc(X1)
% 2.65/1.01      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 2.65/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_251,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 2.65/1.01      | sK0 != X1 ),
% 2.65/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_252,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/1.01      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 2.65/1.01      inference(unflattening,[status(thm)],[c_251]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_613,plain,
% 2.65/1.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 2.65/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_821,plain,
% 2.65/1.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 2.65/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_614,c_613]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1245,plain,
% 2.65/1.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_617,c_821]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_6,plain,
% 2.65/1.01      ( ~ v5_tops_1(X0,X1)
% 2.65/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | ~ l1_pre_topc(X1)
% 2.65/1.01      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 2.65/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_11,negated_conjecture,
% 2.65/1.01      ( v5_tops_1(sK1,sK0) ),
% 2.65/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_206,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | ~ l1_pre_topc(X1)
% 2.65/1.01      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 2.65/1.01      | sK1 != X0
% 2.65/1.01      | sK0 != X1 ),
% 2.65/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_207,plain,
% 2.65/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/1.01      | ~ l1_pre_topc(sK0)
% 2.65/1.01      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 2.65/1.01      inference(unflattening,[status(thm)],[c_206]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_209,plain,
% 2.65/1.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 2.65/1.01      inference(global_propositional_subsumption,
% 2.65/1.01                [status(thm)],
% 2.65/1.01                [c_207,c_13,c_12]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1252,plain,
% 2.65/1.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.65/1.01      inference(light_normalisation,[status(thm)],[c_1245,c_209]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_8,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | ~ l1_pre_topc(X1)
% 2.65/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.65/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_227,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.65/1.01      | sK0 != X1 ),
% 2.65/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_228,plain,
% 2.65/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/1.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.65/1.01      inference(unflattening,[status(thm)],[c_227]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_615,plain,
% 2.65/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.65/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_916,plain,
% 2.65/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.65/1.01      inference(superposition,[status(thm)],[c_617,c_615]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1258,plain,
% 2.65/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.65/1.01      inference(demodulation,[status(thm)],[c_1252,c_916]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_1520,plain,
% 2.65/1.01      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.65/1.01      inference(light_normalisation,[status(thm)],[c_1514,c_1258]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_10,negated_conjecture,
% 2.65/1.01      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 2.65/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_618,plain,
% 2.65/1.01      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 2.65/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(c_630,plain,
% 2.65/1.01      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.65/1.01      inference(light_normalisation,[status(thm)],[c_618,c_209]) ).
% 2.65/1.01  
% 2.65/1.01  cnf(contradiction,plain,
% 2.65/1.01      ( $false ),
% 2.65/1.01      inference(minisat,[status(thm)],[c_1520,c_630]) ).
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  ------                               Statistics
% 2.65/1.01  
% 2.65/1.01  ------ General
% 2.65/1.01  
% 2.65/1.01  abstr_ref_over_cycles:                  0
% 2.65/1.01  abstr_ref_under_cycles:                 0
% 2.65/1.01  gc_basic_clause_elim:                   0
% 2.65/1.01  forced_gc_time:                         0
% 2.65/1.01  parsing_time:                           0.012
% 2.65/1.01  unif_index_cands_time:                  0.
% 2.65/1.01  unif_index_add_time:                    0.
% 2.65/1.01  orderings_time:                         0.
% 2.65/1.01  out_proof_time:                         0.01
% 2.65/1.01  total_time:                             0.122
% 2.65/1.01  num_of_symbols:                         47
% 2.65/1.01  num_of_terms:                           1659
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing
% 2.65/1.01  
% 2.65/1.01  num_of_splits:                          0
% 2.65/1.01  num_of_split_atoms:                     0
% 2.65/1.01  num_of_reused_defs:                     0
% 2.65/1.01  num_eq_ax_congr_red:                    30
% 2.65/1.01  num_of_sem_filtered_clauses:            1
% 2.65/1.01  num_of_subtypes:                        0
% 2.65/1.01  monotx_restored_types:                  0
% 2.65/1.01  sat_num_of_epr_types:                   0
% 2.65/1.01  sat_num_of_non_cyclic_types:            0
% 2.65/1.01  sat_guarded_non_collapsed_types:        0
% 2.65/1.01  num_pure_diseq_elim:                    0
% 2.65/1.01  simp_replaced_by:                       0
% 2.65/1.01  res_preprocessed:                       74
% 2.65/1.01  prep_upred:                             0
% 2.65/1.01  prep_unflattend:                        24
% 2.65/1.01  smt_new_axioms:                         0
% 2.65/1.01  pred_elim_cands:                        2
% 2.65/1.01  pred_elim:                              2
% 2.65/1.01  pred_elim_cl:                           3
% 2.65/1.01  pred_elim_cycles:                       5
% 2.65/1.01  merged_defs:                            0
% 2.65/1.01  merged_defs_ncl:                        0
% 2.65/1.01  bin_hyper_res:                          0
% 2.65/1.01  prep_cycles:                            4
% 2.65/1.01  pred_elim_time:                         0.006
% 2.65/1.01  splitting_time:                         0.
% 2.65/1.01  sem_filter_time:                        0.
% 2.65/1.01  monotx_time:                            0.001
% 2.65/1.01  subtype_inf_time:                       0.
% 2.65/1.01  
% 2.65/1.01  ------ Problem properties
% 2.65/1.01  
% 2.65/1.01  clauses:                                11
% 2.65/1.01  conjectures:                            2
% 2.65/1.01  epr:                                    0
% 2.65/1.01  horn:                                   11
% 2.65/1.01  ground:                                 3
% 2.65/1.01  unary:                                  5
% 2.65/1.01  binary:                                 6
% 2.65/1.01  lits:                                   17
% 2.65/1.01  lits_eq:                                6
% 2.65/1.01  fd_pure:                                0
% 2.65/1.01  fd_pseudo:                              0
% 2.65/1.01  fd_cond:                                0
% 2.65/1.01  fd_pseudo_cond:                         0
% 2.65/1.01  ac_symbols:                             0
% 2.65/1.01  
% 2.65/1.01  ------ Propositional Solver
% 2.65/1.01  
% 2.65/1.01  prop_solver_calls:                      26
% 2.65/1.01  prop_fast_solver_calls:                 369
% 2.65/1.01  smt_solver_calls:                       0
% 2.65/1.01  smt_fast_solver_calls:                  0
% 2.65/1.01  prop_num_of_clauses:                    564
% 2.65/1.01  prop_preprocess_simplified:             2331
% 2.65/1.01  prop_fo_subsumed:                       2
% 2.65/1.01  prop_solver_time:                       0.
% 2.65/1.01  smt_solver_time:                        0.
% 2.65/1.01  smt_fast_solver_time:                   0.
% 2.65/1.01  prop_fast_solver_time:                  0.
% 2.65/1.01  prop_unsat_core_time:                   0.
% 2.65/1.01  
% 2.65/1.01  ------ QBF
% 2.65/1.01  
% 2.65/1.01  qbf_q_res:                              0
% 2.65/1.01  qbf_num_tautologies:                    0
% 2.65/1.01  qbf_prep_cycles:                        0
% 2.65/1.01  
% 2.65/1.01  ------ BMC1
% 2.65/1.01  
% 2.65/1.01  bmc1_current_bound:                     -1
% 2.65/1.01  bmc1_last_solved_bound:                 -1
% 2.65/1.01  bmc1_unsat_core_size:                   -1
% 2.65/1.01  bmc1_unsat_core_parents_size:           -1
% 2.65/1.01  bmc1_merge_next_fun:                    0
% 2.65/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.65/1.01  
% 2.65/1.01  ------ Instantiation
% 2.65/1.01  
% 2.65/1.01  inst_num_of_clauses:                    190
% 2.65/1.01  inst_num_in_passive:                    61
% 2.65/1.01  inst_num_in_active:                     113
% 2.65/1.01  inst_num_in_unprocessed:                16
% 2.65/1.01  inst_num_of_loops:                      120
% 2.65/1.01  inst_num_of_learning_restarts:          0
% 2.65/1.01  inst_num_moves_active_passive:          3
% 2.65/1.01  inst_lit_activity:                      0
% 2.65/1.01  inst_lit_activity_moves:                0
% 2.65/1.01  inst_num_tautologies:                   0
% 2.65/1.01  inst_num_prop_implied:                  0
% 2.65/1.01  inst_num_existing_simplified:           0
% 2.65/1.01  inst_num_eq_res_simplified:             0
% 2.65/1.01  inst_num_child_elim:                    0
% 2.65/1.01  inst_num_of_dismatching_blockings:      17
% 2.65/1.01  inst_num_of_non_proper_insts:           149
% 2.65/1.01  inst_num_of_duplicates:                 0
% 2.65/1.01  inst_inst_num_from_inst_to_res:         0
% 2.65/1.01  inst_dismatching_checking_time:         0.
% 2.65/1.01  
% 2.65/1.01  ------ Resolution
% 2.65/1.01  
% 2.65/1.01  res_num_of_clauses:                     0
% 2.65/1.01  res_num_in_passive:                     0
% 2.65/1.01  res_num_in_active:                      0
% 2.65/1.01  res_num_of_loops:                       78
% 2.65/1.01  res_forward_subset_subsumed:            8
% 2.65/1.01  res_backward_subset_subsumed:           0
% 2.65/1.01  res_forward_subsumed:                   0
% 2.65/1.01  res_backward_subsumed:                  0
% 2.65/1.01  res_forward_subsumption_resolution:     0
% 2.65/1.01  res_backward_subsumption_resolution:    0
% 2.65/1.01  res_clause_to_clause_subsumption:       54
% 2.65/1.01  res_orphan_elimination:                 0
% 2.65/1.01  res_tautology_del:                      14
% 2.65/1.01  res_num_eq_res_simplified:              0
% 2.65/1.01  res_num_sel_changes:                    0
% 2.65/1.01  res_moves_from_active_to_pass:          0
% 2.65/1.01  
% 2.65/1.01  ------ Superposition
% 2.65/1.01  
% 2.65/1.01  sup_time_total:                         0.
% 2.65/1.01  sup_time_generating:                    0.
% 2.65/1.01  sup_time_sim_full:                      0.
% 2.65/1.01  sup_time_sim_immed:                     0.
% 2.65/1.01  
% 2.65/1.01  sup_num_of_clauses:                     29
% 2.65/1.01  sup_num_in_active:                      19
% 2.65/1.01  sup_num_in_passive:                     10
% 2.65/1.01  sup_num_of_loops:                       23
% 2.65/1.01  sup_fw_superposition:                   17
% 2.65/1.01  sup_bw_superposition:                   6
% 2.65/1.01  sup_immediate_simplified:               3
% 2.65/1.01  sup_given_eliminated:                   0
% 2.65/1.01  comparisons_done:                       0
% 2.65/1.01  comparisons_avoided:                    0
% 2.65/1.01  
% 2.65/1.01  ------ Simplifications
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  sim_fw_subset_subsumed:                 0
% 2.65/1.01  sim_bw_subset_subsumed:                 0
% 2.65/1.01  sim_fw_subsumed:                        0
% 2.65/1.01  sim_bw_subsumed:                        0
% 2.65/1.01  sim_fw_subsumption_res:                 0
% 2.65/1.01  sim_bw_subsumption_res:                 0
% 2.65/1.01  sim_tautology_del:                      0
% 2.65/1.01  sim_eq_tautology_del:                   0
% 2.65/1.01  sim_eq_res_simp:                        0
% 2.65/1.01  sim_fw_demodulated:                     0
% 2.65/1.01  sim_bw_demodulated:                     4
% 2.65/1.01  sim_light_normalised:                   4
% 2.65/1.01  sim_joinable_taut:                      0
% 2.65/1.01  sim_joinable_simp:                      0
% 2.65/1.01  sim_ac_normalised:                      0
% 2.65/1.01  sim_smt_subsumption:                    0
% 2.65/1.01  
%------------------------------------------------------------------------------
