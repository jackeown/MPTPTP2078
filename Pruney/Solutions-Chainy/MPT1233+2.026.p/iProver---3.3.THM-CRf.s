%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:41 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 418 expanded)
%              Number of clauses        :   80 ( 156 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   22
%              Number of atoms          :  346 ( 962 expanded)
%              Number of equality atoms :  144 ( 329 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f43,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f44,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f46])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f81])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f82])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f24,axiom,(
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

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1271,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1271,c_4])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1801,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1268])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1274,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_320,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_321,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_368,plain,
    ( v1_xboole_0(k1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_321])).

cnf(c_369,plain,
    ( v1_xboole_0(k1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_1266,plain,
    ( v1_xboole_0(k1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1272,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2413,plain,
    ( k1_struct_0(sK0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1272])).

cnf(c_2901,plain,
    ( k1_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1274,c_2413])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_363,plain,
    ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_321])).

cnf(c_364,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_382,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_321])).

cnf(c_383,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1289,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_364,c_383])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X0)
    | r1_tarski(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_159,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(k3_subset_1(X1,X0),X2)
    | r1_tarski(k3_subset_1(X1,X2),X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_160])).

cnf(c_696,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_697,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_724,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(k3_subset_1(X1,X0),X2)
    | r1_tarski(k3_subset_1(X1,X2),X0) ),
    inference(bin_hyper_res,[status(thm)],[c_195,c_697])).

cnf(c_1263,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_1537,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1263])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1273,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2582,plain,
    ( k1_setfam_1(k6_enumset1(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k1_struct_0(sK0))) = k3_subset_1(u1_struct_0(sK0),X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_1273])).

cnf(c_3341,plain,
    ( k1_setfam_1(k6_enumset1(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2901,c_2582])).

cnf(c_2,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3398,plain,
    ( k3_subset_1(u1_struct_0(sK0),X0) = k1_xboole_0
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3341,c_2])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1392,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1394,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1550,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1551,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_3481,plain,
    ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | k3_subset_1(u1_struct_0(sK0),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3398,c_1394,c_1551])).

cnf(c_3482,plain,
    ( k3_subset_1(u1_struct_0(sK0),X0) = k1_xboole_0
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3481])).

cnf(c_3496,plain,
    ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_3482])).

cnf(c_3500,plain,
    ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3496,c_1801])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_1267,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1691,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1285,c_1267])).

cnf(c_4851,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_3500,c_1691])).

cnf(c_1270,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_291,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_292,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_20])).

cnf(c_297,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_339,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_340,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0)
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(resolution,[status(thm)],[c_297,c_340])).

cnf(c_1264,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1679,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1270,c_1264])).

cnf(c_1384,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1899,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1679,c_0,c_1384,c_1392])).

cnf(c_3348,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2901,c_1289])).

cnf(c_4853,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4851,c_1899,c_3348])).

cnf(c_19,negated_conjecture,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1292,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_19,c_383])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4853,c_1292])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.41/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/0.98  
% 2.41/0.98  ------  iProver source info
% 2.41/0.98  
% 2.41/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.41/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/0.98  git: non_committed_changes: false
% 2.41/0.98  git: last_make_outside_of_git: false
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options
% 2.41/0.98  
% 2.41/0.98  --out_options                           all
% 2.41/0.98  --tptp_safe_out                         true
% 2.41/0.98  --problem_path                          ""
% 2.41/0.98  --include_path                          ""
% 2.41/0.98  --clausifier                            res/vclausify_rel
% 2.41/0.98  --clausifier_options                    --mode clausify
% 2.41/0.98  --stdin                                 false
% 2.41/0.98  --stats_out                             all
% 2.41/0.98  
% 2.41/0.98  ------ General Options
% 2.41/0.98  
% 2.41/0.98  --fof                                   false
% 2.41/0.98  --time_out_real                         305.
% 2.41/0.98  --time_out_virtual                      -1.
% 2.41/0.98  --symbol_type_check                     false
% 2.41/0.98  --clausify_out                          false
% 2.41/0.98  --sig_cnt_out                           false
% 2.41/0.98  --trig_cnt_out                          false
% 2.41/0.98  --trig_cnt_out_tolerance                1.
% 2.41/0.98  --trig_cnt_out_sk_spl                   false
% 2.41/0.98  --abstr_cl_out                          false
% 2.41/0.98  
% 2.41/0.98  ------ Global Options
% 2.41/0.98  
% 2.41/0.98  --schedule                              default
% 2.41/0.98  --add_important_lit                     false
% 2.41/0.98  --prop_solver_per_cl                    1000
% 2.41/0.98  --min_unsat_core                        false
% 2.41/0.98  --soft_assumptions                      false
% 2.41/0.98  --soft_lemma_size                       3
% 2.41/0.98  --prop_impl_unit_size                   0
% 2.41/0.98  --prop_impl_unit                        []
% 2.41/0.98  --share_sel_clauses                     true
% 2.41/0.98  --reset_solvers                         false
% 2.41/0.98  --bc_imp_inh                            [conj_cone]
% 2.41/0.98  --conj_cone_tolerance                   3.
% 2.41/0.98  --extra_neg_conj                        none
% 2.41/0.98  --large_theory_mode                     true
% 2.41/0.98  --prolific_symb_bound                   200
% 2.41/0.98  --lt_threshold                          2000
% 2.41/0.98  --clause_weak_htbl                      true
% 2.41/0.98  --gc_record_bc_elim                     false
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing Options
% 2.41/0.98  
% 2.41/0.98  --preprocessing_flag                    true
% 2.41/0.98  --time_out_prep_mult                    0.1
% 2.41/0.98  --splitting_mode                        input
% 2.41/0.98  --splitting_grd                         true
% 2.41/0.98  --splitting_cvd                         false
% 2.41/0.98  --splitting_cvd_svl                     false
% 2.41/0.98  --splitting_nvd                         32
% 2.41/0.98  --sub_typing                            true
% 2.41/0.98  --prep_gs_sim                           true
% 2.41/0.98  --prep_unflatten                        true
% 2.41/0.98  --prep_res_sim                          true
% 2.41/0.98  --prep_upred                            true
% 2.41/0.98  --prep_sem_filter                       exhaustive
% 2.41/0.98  --prep_sem_filter_out                   false
% 2.41/0.98  --pred_elim                             true
% 2.41/0.98  --res_sim_input                         true
% 2.41/0.98  --eq_ax_congr_red                       true
% 2.41/0.98  --pure_diseq_elim                       true
% 2.41/0.98  --brand_transform                       false
% 2.41/0.98  --non_eq_to_eq                          false
% 2.41/0.98  --prep_def_merge                        true
% 2.41/0.98  --prep_def_merge_prop_impl              false
% 2.41/0.98  --prep_def_merge_mbd                    true
% 2.41/0.98  --prep_def_merge_tr_red                 false
% 2.41/0.98  --prep_def_merge_tr_cl                  false
% 2.41/0.98  --smt_preprocessing                     true
% 2.41/0.98  --smt_ac_axioms                         fast
% 2.41/0.98  --preprocessed_out                      false
% 2.41/0.98  --preprocessed_stats                    false
% 2.41/0.98  
% 2.41/0.98  ------ Abstraction refinement Options
% 2.41/0.98  
% 2.41/0.98  --abstr_ref                             []
% 2.41/0.98  --abstr_ref_prep                        false
% 2.41/0.98  --abstr_ref_until_sat                   false
% 2.41/0.98  --abstr_ref_sig_restrict                funpre
% 2.41/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.98  --abstr_ref_under                       []
% 2.41/0.98  
% 2.41/0.98  ------ SAT Options
% 2.41/0.98  
% 2.41/0.98  --sat_mode                              false
% 2.41/0.98  --sat_fm_restart_options                ""
% 2.41/0.98  --sat_gr_def                            false
% 2.41/0.98  --sat_epr_types                         true
% 2.41/0.98  --sat_non_cyclic_types                  false
% 2.41/0.98  --sat_finite_models                     false
% 2.41/0.98  --sat_fm_lemmas                         false
% 2.41/0.98  --sat_fm_prep                           false
% 2.41/0.98  --sat_fm_uc_incr                        true
% 2.41/0.98  --sat_out_model                         small
% 2.41/0.98  --sat_out_clauses                       false
% 2.41/0.98  
% 2.41/0.98  ------ QBF Options
% 2.41/0.98  
% 2.41/0.98  --qbf_mode                              false
% 2.41/0.98  --qbf_elim_univ                         false
% 2.41/0.98  --qbf_dom_inst                          none
% 2.41/0.98  --qbf_dom_pre_inst                      false
% 2.41/0.98  --qbf_sk_in                             false
% 2.41/0.98  --qbf_pred_elim                         true
% 2.41/0.98  --qbf_split                             512
% 2.41/0.98  
% 2.41/0.98  ------ BMC1 Options
% 2.41/0.98  
% 2.41/0.98  --bmc1_incremental                      false
% 2.41/0.98  --bmc1_axioms                           reachable_all
% 2.41/0.98  --bmc1_min_bound                        0
% 2.41/0.98  --bmc1_max_bound                        -1
% 2.41/0.98  --bmc1_max_bound_default                -1
% 2.41/0.98  --bmc1_symbol_reachability              true
% 2.41/0.98  --bmc1_property_lemmas                  false
% 2.41/0.98  --bmc1_k_induction                      false
% 2.41/0.98  --bmc1_non_equiv_states                 false
% 2.41/0.98  --bmc1_deadlock                         false
% 2.41/0.98  --bmc1_ucm                              false
% 2.41/0.98  --bmc1_add_unsat_core                   none
% 2.41/0.99  --bmc1_unsat_core_children              false
% 2.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.99  --bmc1_out_stat                         full
% 2.41/0.99  --bmc1_ground_init                      false
% 2.41/0.99  --bmc1_pre_inst_next_state              false
% 2.41/0.99  --bmc1_pre_inst_state                   false
% 2.41/0.99  --bmc1_pre_inst_reach_state             false
% 2.41/0.99  --bmc1_out_unsat_core                   false
% 2.41/0.99  --bmc1_aig_witness_out                  false
% 2.41/0.99  --bmc1_verbose                          false
% 2.41/0.99  --bmc1_dump_clauses_tptp                false
% 2.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.99  --bmc1_dump_file                        -
% 2.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.99  --bmc1_ucm_extend_mode                  1
% 2.41/0.99  --bmc1_ucm_init_mode                    2
% 2.41/0.99  --bmc1_ucm_cone_mode                    none
% 2.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.99  --bmc1_ucm_relax_model                  4
% 2.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.99  --bmc1_ucm_layered_model                none
% 2.41/0.99  --bmc1_ucm_max_lemma_size               10
% 2.41/0.99  
% 2.41/0.99  ------ AIG Options
% 2.41/0.99  
% 2.41/0.99  --aig_mode                              false
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation Options
% 2.41/0.99  
% 2.41/0.99  --instantiation_flag                    true
% 2.41/0.99  --inst_sos_flag                         false
% 2.41/0.99  --inst_sos_phase                        true
% 2.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel_side                     num_symb
% 2.41/0.99  --inst_solver_per_active                1400
% 2.41/0.99  --inst_solver_calls_frac                1.
% 2.41/0.99  --inst_passive_queue_type               priority_queues
% 2.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.99  --inst_passive_queues_freq              [25;2]
% 2.41/0.99  --inst_dismatching                      true
% 2.41/0.99  --inst_eager_unprocessed_to_passive     true
% 2.41/0.99  --inst_prop_sim_given                   true
% 2.41/0.99  --inst_prop_sim_new                     false
% 2.41/0.99  --inst_subs_new                         false
% 2.41/0.99  --inst_eq_res_simp                      false
% 2.41/0.99  --inst_subs_given                       false
% 2.41/0.99  --inst_orphan_elimination               true
% 2.41/0.99  --inst_learning_loop_flag               true
% 2.41/0.99  --inst_learning_start                   3000
% 2.41/0.99  --inst_learning_factor                  2
% 2.41/0.99  --inst_start_prop_sim_after_learn       3
% 2.41/0.99  --inst_sel_renew                        solver
% 2.41/0.99  --inst_lit_activity_flag                true
% 2.41/0.99  --inst_restr_to_given                   false
% 2.41/0.99  --inst_activity_threshold               500
% 2.41/0.99  --inst_out_proof                        true
% 2.41/0.99  
% 2.41/0.99  ------ Resolution Options
% 2.41/0.99  
% 2.41/0.99  --resolution_flag                       true
% 2.41/0.99  --res_lit_sel                           adaptive
% 2.41/0.99  --res_lit_sel_side                      none
% 2.41/0.99  --res_ordering                          kbo
% 2.41/0.99  --res_to_prop_solver                    active
% 2.41/0.99  --res_prop_simpl_new                    false
% 2.41/0.99  --res_prop_simpl_given                  true
% 2.41/0.99  --res_passive_queue_type                priority_queues
% 2.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.99  --res_passive_queues_freq               [15;5]
% 2.41/0.99  --res_forward_subs                      full
% 2.41/0.99  --res_backward_subs                     full
% 2.41/0.99  --res_forward_subs_resolution           true
% 2.41/0.99  --res_backward_subs_resolution          true
% 2.41/0.99  --res_orphan_elimination                true
% 2.41/0.99  --res_time_limit                        2.
% 2.41/0.99  --res_out_proof                         true
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Options
% 2.41/0.99  
% 2.41/0.99  --superposition_flag                    true
% 2.41/0.99  --sup_passive_queue_type                priority_queues
% 2.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.99  --demod_completeness_check              fast
% 2.41/0.99  --demod_use_ground                      true
% 2.41/0.99  --sup_to_prop_solver                    passive
% 2.41/0.99  --sup_prop_simpl_new                    true
% 2.41/0.99  --sup_prop_simpl_given                  true
% 2.41/0.99  --sup_fun_splitting                     false
% 2.41/0.99  --sup_smt_interval                      50000
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Simplification Setup
% 2.41/0.99  
% 2.41/0.99  --sup_indices_passive                   []
% 2.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_full_bw                           [BwDemod]
% 2.41/0.99  --sup_immed_triv                        [TrivRules]
% 2.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_immed_bw_main                     []
% 2.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  
% 2.41/0.99  ------ Combination Options
% 2.41/0.99  
% 2.41/0.99  --comb_res_mult                         3
% 2.41/0.99  --comb_sup_mult                         2
% 2.41/0.99  --comb_inst_mult                        10
% 2.41/0.99  
% 2.41/0.99  ------ Debug Options
% 2.41/0.99  
% 2.41/0.99  --dbg_backtrace                         false
% 2.41/0.99  --dbg_dump_prop_clauses                 false
% 2.41/0.99  --dbg_dump_prop_clauses_file            -
% 2.41/0.99  --dbg_out_stat                          false
% 2.41/0.99  ------ Parsing...
% 2.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/0.99  ------ Proving...
% 2.41/0.99  ------ Problem Properties 
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  clauses                                 17
% 2.41/0.99  conjectures                             1
% 2.41/0.99  EPR                                     2
% 2.41/0.99  Horn                                    17
% 2.41/0.99  unary                                   10
% 2.41/0.99  binary                                  4
% 2.41/0.99  lits                                    28
% 2.41/0.99  lits eq                                 9
% 2.41/0.99  fd_pure                                 0
% 2.41/0.99  fd_pseudo                               0
% 2.41/0.99  fd_cond                                 0
% 2.41/0.99  fd_pseudo_cond                          1
% 2.41/0.99  AC symbols                              0
% 2.41/0.99  
% 2.41/0.99  ------ Schedule dynamic 5 is on 
% 2.41/0.99  
% 2.41/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  ------ 
% 2.41/0.99  Current options:
% 2.41/0.99  ------ 
% 2.41/0.99  
% 2.41/0.99  ------ Input Options
% 2.41/0.99  
% 2.41/0.99  --out_options                           all
% 2.41/0.99  --tptp_safe_out                         true
% 2.41/0.99  --problem_path                          ""
% 2.41/0.99  --include_path                          ""
% 2.41/0.99  --clausifier                            res/vclausify_rel
% 2.41/0.99  --clausifier_options                    --mode clausify
% 2.41/0.99  --stdin                                 false
% 2.41/0.99  --stats_out                             all
% 2.41/0.99  
% 2.41/0.99  ------ General Options
% 2.41/0.99  
% 2.41/0.99  --fof                                   false
% 2.41/0.99  --time_out_real                         305.
% 2.41/0.99  --time_out_virtual                      -1.
% 2.41/0.99  --symbol_type_check                     false
% 2.41/0.99  --clausify_out                          false
% 2.41/0.99  --sig_cnt_out                           false
% 2.41/0.99  --trig_cnt_out                          false
% 2.41/0.99  --trig_cnt_out_tolerance                1.
% 2.41/0.99  --trig_cnt_out_sk_spl                   false
% 2.41/0.99  --abstr_cl_out                          false
% 2.41/0.99  
% 2.41/0.99  ------ Global Options
% 2.41/0.99  
% 2.41/0.99  --schedule                              default
% 2.41/0.99  --add_important_lit                     false
% 2.41/0.99  --prop_solver_per_cl                    1000
% 2.41/0.99  --min_unsat_core                        false
% 2.41/0.99  --soft_assumptions                      false
% 2.41/0.99  --soft_lemma_size                       3
% 2.41/0.99  --prop_impl_unit_size                   0
% 2.41/0.99  --prop_impl_unit                        []
% 2.41/0.99  --share_sel_clauses                     true
% 2.41/0.99  --reset_solvers                         false
% 2.41/0.99  --bc_imp_inh                            [conj_cone]
% 2.41/0.99  --conj_cone_tolerance                   3.
% 2.41/0.99  --extra_neg_conj                        none
% 2.41/0.99  --large_theory_mode                     true
% 2.41/0.99  --prolific_symb_bound                   200
% 2.41/0.99  --lt_threshold                          2000
% 2.41/0.99  --clause_weak_htbl                      true
% 2.41/0.99  --gc_record_bc_elim                     false
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing Options
% 2.41/0.99  
% 2.41/0.99  --preprocessing_flag                    true
% 2.41/0.99  --time_out_prep_mult                    0.1
% 2.41/0.99  --splitting_mode                        input
% 2.41/0.99  --splitting_grd                         true
% 2.41/0.99  --splitting_cvd                         false
% 2.41/0.99  --splitting_cvd_svl                     false
% 2.41/0.99  --splitting_nvd                         32
% 2.41/0.99  --sub_typing                            true
% 2.41/0.99  --prep_gs_sim                           true
% 2.41/0.99  --prep_unflatten                        true
% 2.41/0.99  --prep_res_sim                          true
% 2.41/0.99  --prep_upred                            true
% 2.41/0.99  --prep_sem_filter                       exhaustive
% 2.41/0.99  --prep_sem_filter_out                   false
% 2.41/0.99  --pred_elim                             true
% 2.41/0.99  --res_sim_input                         true
% 2.41/0.99  --eq_ax_congr_red                       true
% 2.41/0.99  --pure_diseq_elim                       true
% 2.41/0.99  --brand_transform                       false
% 2.41/0.99  --non_eq_to_eq                          false
% 2.41/0.99  --prep_def_merge                        true
% 2.41/0.99  --prep_def_merge_prop_impl              false
% 2.41/0.99  --prep_def_merge_mbd                    true
% 2.41/0.99  --prep_def_merge_tr_red                 false
% 2.41/0.99  --prep_def_merge_tr_cl                  false
% 2.41/0.99  --smt_preprocessing                     true
% 2.41/0.99  --smt_ac_axioms                         fast
% 2.41/0.99  --preprocessed_out                      false
% 2.41/0.99  --preprocessed_stats                    false
% 2.41/0.99  
% 2.41/0.99  ------ Abstraction refinement Options
% 2.41/0.99  
% 2.41/0.99  --abstr_ref                             []
% 2.41/0.99  --abstr_ref_prep                        false
% 2.41/0.99  --abstr_ref_until_sat                   false
% 2.41/0.99  --abstr_ref_sig_restrict                funpre
% 2.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.99  --abstr_ref_under                       []
% 2.41/0.99  
% 2.41/0.99  ------ SAT Options
% 2.41/0.99  
% 2.41/0.99  --sat_mode                              false
% 2.41/0.99  --sat_fm_restart_options                ""
% 2.41/0.99  --sat_gr_def                            false
% 2.41/0.99  --sat_epr_types                         true
% 2.41/0.99  --sat_non_cyclic_types                  false
% 2.41/0.99  --sat_finite_models                     false
% 2.41/0.99  --sat_fm_lemmas                         false
% 2.41/0.99  --sat_fm_prep                           false
% 2.41/0.99  --sat_fm_uc_incr                        true
% 2.41/0.99  --sat_out_model                         small
% 2.41/0.99  --sat_out_clauses                       false
% 2.41/0.99  
% 2.41/0.99  ------ QBF Options
% 2.41/0.99  
% 2.41/0.99  --qbf_mode                              false
% 2.41/0.99  --qbf_elim_univ                         false
% 2.41/0.99  --qbf_dom_inst                          none
% 2.41/0.99  --qbf_dom_pre_inst                      false
% 2.41/0.99  --qbf_sk_in                             false
% 2.41/0.99  --qbf_pred_elim                         true
% 2.41/0.99  --qbf_split                             512
% 2.41/0.99  
% 2.41/0.99  ------ BMC1 Options
% 2.41/0.99  
% 2.41/0.99  --bmc1_incremental                      false
% 2.41/0.99  --bmc1_axioms                           reachable_all
% 2.41/0.99  --bmc1_min_bound                        0
% 2.41/0.99  --bmc1_max_bound                        -1
% 2.41/0.99  --bmc1_max_bound_default                -1
% 2.41/0.99  --bmc1_symbol_reachability              true
% 2.41/0.99  --bmc1_property_lemmas                  false
% 2.41/0.99  --bmc1_k_induction                      false
% 2.41/0.99  --bmc1_non_equiv_states                 false
% 2.41/0.99  --bmc1_deadlock                         false
% 2.41/0.99  --bmc1_ucm                              false
% 2.41/0.99  --bmc1_add_unsat_core                   none
% 2.41/0.99  --bmc1_unsat_core_children              false
% 2.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.99  --bmc1_out_stat                         full
% 2.41/0.99  --bmc1_ground_init                      false
% 2.41/0.99  --bmc1_pre_inst_next_state              false
% 2.41/0.99  --bmc1_pre_inst_state                   false
% 2.41/0.99  --bmc1_pre_inst_reach_state             false
% 2.41/0.99  --bmc1_out_unsat_core                   false
% 2.41/0.99  --bmc1_aig_witness_out                  false
% 2.41/0.99  --bmc1_verbose                          false
% 2.41/0.99  --bmc1_dump_clauses_tptp                false
% 2.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.99  --bmc1_dump_file                        -
% 2.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.99  --bmc1_ucm_extend_mode                  1
% 2.41/0.99  --bmc1_ucm_init_mode                    2
% 2.41/0.99  --bmc1_ucm_cone_mode                    none
% 2.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.99  --bmc1_ucm_relax_model                  4
% 2.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.99  --bmc1_ucm_layered_model                none
% 2.41/0.99  --bmc1_ucm_max_lemma_size               10
% 2.41/0.99  
% 2.41/0.99  ------ AIG Options
% 2.41/0.99  
% 2.41/0.99  --aig_mode                              false
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation Options
% 2.41/0.99  
% 2.41/0.99  --instantiation_flag                    true
% 2.41/0.99  --inst_sos_flag                         false
% 2.41/0.99  --inst_sos_phase                        true
% 2.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.99  --inst_lit_sel_side                     none
% 2.41/0.99  --inst_solver_per_active                1400
% 2.41/0.99  --inst_solver_calls_frac                1.
% 2.41/0.99  --inst_passive_queue_type               priority_queues
% 2.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.99  --inst_passive_queues_freq              [25;2]
% 2.41/0.99  --inst_dismatching                      true
% 2.41/0.99  --inst_eager_unprocessed_to_passive     true
% 2.41/0.99  --inst_prop_sim_given                   true
% 2.41/0.99  --inst_prop_sim_new                     false
% 2.41/0.99  --inst_subs_new                         false
% 2.41/0.99  --inst_eq_res_simp                      false
% 2.41/0.99  --inst_subs_given                       false
% 2.41/0.99  --inst_orphan_elimination               true
% 2.41/0.99  --inst_learning_loop_flag               true
% 2.41/0.99  --inst_learning_start                   3000
% 2.41/0.99  --inst_learning_factor                  2
% 2.41/0.99  --inst_start_prop_sim_after_learn       3
% 2.41/0.99  --inst_sel_renew                        solver
% 2.41/0.99  --inst_lit_activity_flag                true
% 2.41/0.99  --inst_restr_to_given                   false
% 2.41/0.99  --inst_activity_threshold               500
% 2.41/0.99  --inst_out_proof                        true
% 2.41/0.99  
% 2.41/0.99  ------ Resolution Options
% 2.41/0.99  
% 2.41/0.99  --resolution_flag                       false
% 2.41/0.99  --res_lit_sel                           adaptive
% 2.41/0.99  --res_lit_sel_side                      none
% 2.41/0.99  --res_ordering                          kbo
% 2.41/0.99  --res_to_prop_solver                    active
% 2.41/0.99  --res_prop_simpl_new                    false
% 2.41/0.99  --res_prop_simpl_given                  true
% 2.41/0.99  --res_passive_queue_type                priority_queues
% 2.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.99  --res_passive_queues_freq               [15;5]
% 2.41/0.99  --res_forward_subs                      full
% 2.41/0.99  --res_backward_subs                     full
% 2.41/0.99  --res_forward_subs_resolution           true
% 2.41/0.99  --res_backward_subs_resolution          true
% 2.41/0.99  --res_orphan_elimination                true
% 2.41/0.99  --res_time_limit                        2.
% 2.41/0.99  --res_out_proof                         true
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Options
% 2.41/0.99  
% 2.41/0.99  --superposition_flag                    true
% 2.41/0.99  --sup_passive_queue_type                priority_queues
% 2.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.99  --demod_completeness_check              fast
% 2.41/0.99  --demod_use_ground                      true
% 2.41/0.99  --sup_to_prop_solver                    passive
% 2.41/0.99  --sup_prop_simpl_new                    true
% 2.41/0.99  --sup_prop_simpl_given                  true
% 2.41/0.99  --sup_fun_splitting                     false
% 2.41/0.99  --sup_smt_interval                      50000
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Simplification Setup
% 2.41/0.99  
% 2.41/0.99  --sup_indices_passive                   []
% 2.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_full_bw                           [BwDemod]
% 2.41/0.99  --sup_immed_triv                        [TrivRules]
% 2.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_immed_bw_main                     []
% 2.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  
% 2.41/0.99  ------ Combination Options
% 2.41/0.99  
% 2.41/0.99  --comb_res_mult                         3
% 2.41/0.99  --comb_sup_mult                         2
% 2.41/0.99  --comb_inst_mult                        10
% 2.41/0.99  
% 2.41/0.99  ------ Debug Options
% 2.41/0.99  
% 2.41/0.99  --dbg_backtrace                         false
% 2.41/0.99  --dbg_dump_prop_clauses                 false
% 2.41/0.99  --dbg_dump_prop_clauses_file            -
% 2.41/0.99  --dbg_out_stat                          false
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  ------ Proving...
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  % SZS status Theorem for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  fof(f12,axiom,(
% 2.41/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f59,plain,(
% 2.41/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f12])).
% 2.41/0.99  
% 2.41/0.99  fof(f11,axiom,(
% 2.41/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f58,plain,(
% 2.41/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.41/0.99    inference(cnf_transformation,[],[f11])).
% 2.41/0.99  
% 2.41/0.99  fof(f16,axiom,(
% 2.41/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f45,plain,(
% 2.41/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.41/0.99    inference(nnf_transformation,[],[f16])).
% 2.41/0.99  
% 2.41/0.99  fof(f63,plain,(
% 2.41/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f45])).
% 2.41/0.99  
% 2.41/0.99  fof(f1,axiom,(
% 2.41/0.99    v1_xboole_0(k1_xboole_0)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f48,plain,(
% 2.41/0.99    v1_xboole_0(k1_xboole_0)),
% 2.41/0.99    inference(cnf_transformation,[],[f1])).
% 2.41/0.99  
% 2.41/0.99  fof(f22,axiom,(
% 2.41/0.99    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f38,plain,(
% 2.41/0.99    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f22])).
% 2.41/0.99  
% 2.41/0.99  fof(f69,plain,(
% 2.41/0.99    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f38])).
% 2.41/0.99  
% 2.41/0.99  fof(f21,axiom,(
% 2.41/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f37,plain,(
% 2.41/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f21])).
% 2.41/0.99  
% 2.41/0.99  fof(f68,plain,(
% 2.41/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f37])).
% 2.41/0.99  
% 2.41/0.99  fof(f26,conjecture,(
% 2.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f27,negated_conjecture,(
% 2.41/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 2.41/0.99    inference(negated_conjecture,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f43,plain,(
% 2.41/0.99    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.41/0.99    inference(ennf_transformation,[],[f27])).
% 2.41/0.99  
% 2.41/0.99  fof(f44,plain,(
% 2.41/0.99    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.41/0.99    inference(flattening,[],[f43])).
% 2.41/0.99  
% 2.41/0.99  fof(f46,plain,(
% 2.41/0.99    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f47,plain,(
% 2.41/0.99    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f46])).
% 2.41/0.99  
% 2.41/0.99  fof(f75,plain,(
% 2.41/0.99    l1_pre_topc(sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f47])).
% 2.41/0.99  
% 2.41/0.99  fof(f4,axiom,(
% 2.41/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f30,plain,(
% 2.41/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f4])).
% 2.41/0.99  
% 2.41/0.99  fof(f51,plain,(
% 2.41/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f30])).
% 2.41/0.99  
% 2.41/0.99  fof(f23,axiom,(
% 2.41/0.99    ! [X0] : (l1_struct_0(X0) => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f39,plain,(
% 2.41/0.99    ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f23])).
% 2.41/0.99  
% 2.41/0.99  fof(f70,plain,(
% 2.41/0.99    ( ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f39])).
% 2.41/0.99  
% 2.41/0.99  fof(f19,axiom,(
% 2.41/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f35,plain,(
% 2.41/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f19])).
% 2.41/0.99  
% 2.41/0.99  fof(f66,plain,(
% 2.41/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f35])).
% 2.41/0.99  
% 2.41/0.99  fof(f13,axiom,(
% 2.41/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f31,plain,(
% 2.41/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.41/0.99    inference(ennf_transformation,[],[f13])).
% 2.41/0.99  
% 2.41/0.99  fof(f32,plain,(
% 2.41/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.41/0.99    inference(flattening,[],[f31])).
% 2.41/0.99  
% 2.41/0.99  fof(f60,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f32])).
% 2.41/0.99  
% 2.41/0.99  fof(f64,plain,(
% 2.41/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f45])).
% 2.41/0.99  
% 2.41/0.99  fof(f2,axiom,(
% 2.41/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f29,plain,(
% 2.41/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.41/0.99    inference(ennf_transformation,[],[f2])).
% 2.41/0.99  
% 2.41/0.99  fof(f49,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f29])).
% 2.41/0.99  
% 2.41/0.99  fof(f15,axiom,(
% 2.41/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f62,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f15])).
% 2.41/0.99  
% 2.41/0.99  fof(f5,axiom,(
% 2.41/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f52,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f5])).
% 2.41/0.99  
% 2.41/0.99  fof(f6,axiom,(
% 2.41/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f53,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f6])).
% 2.41/0.99  
% 2.41/0.99  fof(f7,axiom,(
% 2.41/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f54,plain,(
% 2.41/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f7])).
% 2.41/0.99  
% 2.41/0.99  fof(f8,axiom,(
% 2.41/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f55,plain,(
% 2.41/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f8])).
% 2.41/0.99  
% 2.41/0.99  fof(f9,axiom,(
% 2.41/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f56,plain,(
% 2.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f9])).
% 2.41/0.99  
% 2.41/0.99  fof(f10,axiom,(
% 2.41/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f57,plain,(
% 2.41/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f10])).
% 2.41/0.99  
% 2.41/0.99  fof(f77,plain,(
% 2.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f56,f57])).
% 2.41/0.99  
% 2.41/0.99  fof(f78,plain,(
% 2.41/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f55,f77])).
% 2.41/0.99  
% 2.41/0.99  fof(f79,plain,(
% 2.41/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f54,f78])).
% 2.41/0.99  
% 2.41/0.99  fof(f80,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f53,f79])).
% 2.41/0.99  
% 2.41/0.99  fof(f81,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f52,f80])).
% 2.41/0.99  
% 2.41/0.99  fof(f82,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.41/0.99    inference(definition_unfolding,[],[f62,f81])).
% 2.41/0.99  
% 2.41/0.99  fof(f83,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f49,f82])).
% 2.41/0.99  
% 2.41/0.99  fof(f3,axiom,(
% 2.41/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f50,plain,(
% 2.41/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f3])).
% 2.41/0.99  
% 2.41/0.99  fof(f84,plain,(
% 2.41/0.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 2.41/0.99    inference(definition_unfolding,[],[f50,f82])).
% 2.41/0.99  
% 2.41/0.99  fof(f14,axiom,(
% 2.41/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f61,plain,(
% 2.41/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f14])).
% 2.41/0.99  
% 2.41/0.99  fof(f25,axiom,(
% 2.41/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f42,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f25])).
% 2.41/0.99  
% 2.41/0.99  fof(f73,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f42])).
% 2.41/0.99  
% 2.41/0.99  fof(f18,axiom,(
% 2.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f33,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.41/0.99    inference(ennf_transformation,[],[f18])).
% 2.41/0.99  
% 2.41/0.99  fof(f34,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.41/0.99    inference(flattening,[],[f33])).
% 2.41/0.99  
% 2.41/0.99  fof(f65,plain,(
% 2.41/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f34])).
% 2.41/0.99  
% 2.41/0.99  fof(f74,plain,(
% 2.41/0.99    v2_pre_topc(sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f47])).
% 2.41/0.99  
% 2.41/0.99  fof(f24,axiom,(
% 2.41/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f40,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f24])).
% 2.41/0.99  
% 2.41/0.99  fof(f41,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(flattening,[],[f40])).
% 2.41/0.99  
% 2.41/0.99  fof(f71,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f41])).
% 2.41/0.99  
% 2.41/0.99  fof(f76,plain,(
% 2.41/0.99    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 2.41/0.99    inference(cnf_transformation,[],[f47])).
% 2.41/0.99  
% 2.41/0.99  cnf(c_5,plain,
% 2.41/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.41/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1271,plain,
% 2.41/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_4,plain,
% 2.41/0.99      ( k2_subset_1(X0) = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1285,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_1271,c_4]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_9,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1268,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.41/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1801,plain,
% 2.41/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1285,c_1268]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_0,plain,
% 2.41/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1274,plain,
% 2.41/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_14,plain,
% 2.41/0.99      ( ~ l1_struct_0(X0) | v1_xboole_0(k1_struct_0(X0)) ),
% 2.41/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_13,plain,
% 2.41/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_20,negated_conjecture,
% 2.41/0.99      ( l1_pre_topc(sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_320,plain,
% 2.41/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_321,plain,
% 2.41/0.99      ( l1_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_368,plain,
% 2.41/0.99      ( v1_xboole_0(k1_struct_0(X0)) | sK0 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_321]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_369,plain,
% 2.41/0.99      ( v1_xboole_0(k1_struct_0(sK0)) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1266,plain,
% 2.41/0.99      ( v1_xboole_0(k1_struct_0(sK0)) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3,plain,
% 2.41/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.41/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1272,plain,
% 2.41/0.99      ( X0 = X1
% 2.41/0.99      | v1_xboole_0(X0) != iProver_top
% 2.41/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2413,plain,
% 2.41/0.99      ( k1_struct_0(sK0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1266,c_1272]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2901,plain,
% 2.41/0.99      ( k1_struct_0(sK0) = k1_xboole_0 ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1274,c_2413]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_15,plain,
% 2.41/0.99      ( ~ l1_struct_0(X0)
% 2.41/0.99      | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_363,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
% 2.41/0.99      | sK0 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_321]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_364,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_363]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_11,plain,
% 2.41/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_382,plain,
% 2.41/0.99      ( k2_struct_0(X0) = u1_struct_0(X0) | sK0 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_321]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_383,plain,
% 2.41/0.99      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_382]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1289,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_364,c_383]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_6,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.41/0.99      | ~ r1_tarski(k3_subset_1(X1,X2),X0)
% 2.41/0.99      | r1_tarski(k3_subset_1(X1,X0),X2) ),
% 2.41/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_8,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_159,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.41/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_160,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_159]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_195,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/0.99      | ~ r1_tarski(X2,X1)
% 2.41/0.99      | ~ r1_tarski(k3_subset_1(X1,X0),X2)
% 2.41/0.99      | r1_tarski(k3_subset_1(X1,X2),X0) ),
% 2.41/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_160]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_696,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.41/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_697,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_696]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_724,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | ~ r1_tarski(X2,X1)
% 2.41/0.99      | ~ r1_tarski(k3_subset_1(X1,X0),X2)
% 2.41/0.99      | r1_tarski(k3_subset_1(X1,X2),X0) ),
% 2.41/0.99      inference(bin_hyper_res,[status(thm)],[c_195,c_697]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1263,plain,
% 2.41/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.41/0.99      | r1_tarski(X2,X1) != iProver_top
% 2.41/0.99      | r1_tarski(k3_subset_1(X1,X0),X2) != iProver_top
% 2.41/0.99      | r1_tarski(k3_subset_1(X1,X2),X0) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1537,plain,
% 2.41/0.99      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k1_struct_0(sK0)) = iProver_top
% 2.41/0.99      | r1_tarski(k1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1289,c_1263]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1273,plain,
% 2.41/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 2.41/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2582,plain,
% 2.41/0.99      ( k1_setfam_1(k6_enumset1(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k1_struct_0(sK0))) = k3_subset_1(u1_struct_0(sK0),X0)
% 2.41/0.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(k1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1537,c_1273]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3341,plain,
% 2.41/0.99      ( k1_setfam_1(k6_enumset1(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 2.41/0.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.41/0.99      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_2901,c_2582]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2,plain,
% 2.41/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3398,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),X0) = k1_xboole_0
% 2.41/0.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.41/0.99      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_3341,c_2]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_7,plain,
% 2.41/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.41/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1392,plain,
% 2.41/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1394,plain,
% 2.41/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1459,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1550,plain,
% 2.41/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_1459]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1551,plain,
% 2.41/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.41/0.99      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3481,plain,
% 2.41/0.99      ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 2.41/0.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | k3_subset_1(u1_struct_0(sK0),X0) = k1_xboole_0 ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_3398,c_1394,c_1551]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3482,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),X0) = k1_xboole_0
% 2.41/0.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.41/0.99      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_3481]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3496,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0
% 2.41/0.99      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1801,c_3482]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3500,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0 ),
% 2.41/0.99      inference(forward_subsumption_resolution,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_3496,c_1801]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_18,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_327,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 2.41/0.99      | sK0 != X1 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_328,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_327]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1267,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 2.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1691,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1285,c_1267]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_4851,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_3500,c_1691]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1270,plain,
% 2.41/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_10,plain,
% 2.41/0.99      ( v4_pre_topc(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ v2_pre_topc(X1)
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | ~ v1_xboole_0(X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_21,negated_conjecture,
% 2.41/0.99      ( v2_pre_topc(sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_291,plain,
% 2.41/0.99      ( v4_pre_topc(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | ~ v1_xboole_0(X0)
% 2.41/0.99      | sK0 != X1 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_292,plain,
% 2.41/0.99      ( v4_pre_topc(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ l1_pre_topc(sK0)
% 2.41/0.99      | ~ v1_xboole_0(X0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_296,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | v4_pre_topc(X0,sK0)
% 2.41/0.99      | ~ v1_xboole_0(X0) ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_292,c_20]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_297,plain,
% 2.41/0.99      ( v4_pre_topc(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ v1_xboole_0(X0) ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_296]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_17,plain,
% 2.41/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.41/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_339,plain,
% 2.41/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | k2_pre_topc(X1,X0) = X0
% 2.41/0.99      | sK0 != X1 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_340,plain,
% 2.41/0.99      ( ~ v4_pre_topc(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,X0) = X0 ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_393,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ v1_xboole_0(X0)
% 2.41/0.99      | k2_pre_topc(sK0,X0) = X0 ),
% 2.41/0.99      inference(resolution,[status(thm)],[c_297,c_340]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1264,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,X0) = X0
% 2.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.41/0.99      | v1_xboole_0(X0) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1679,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
% 2.41/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1270,c_1264]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1384,plain,
% 2.41/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.41/0.99      | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_393]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1899,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_1679,c_0,c_1384,c_1392]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3348,plain,
% 2.41/0.99      ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = u1_struct_0(sK0) ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_2901,c_1289]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_4853,plain,
% 2.41/0.99      ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_4851,c_1899,c_3348]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_19,negated_conjecture,
% 2.41/0.99      ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
% 2.41/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1292,plain,
% 2.41/0.99      ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_19,c_383]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(contradiction,plain,
% 2.41/0.99      ( $false ),
% 2.41/0.99      inference(minisat,[status(thm)],[c_4853,c_1292]) ).
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  ------                               Statistics
% 2.41/0.99  
% 2.41/0.99  ------ General
% 2.41/0.99  
% 2.41/0.99  abstr_ref_over_cycles:                  0
% 2.41/0.99  abstr_ref_under_cycles:                 0
% 2.41/0.99  gc_basic_clause_elim:                   0
% 2.41/0.99  forced_gc_time:                         0
% 2.41/0.99  parsing_time:                           0.011
% 2.41/0.99  unif_index_cands_time:                  0.
% 2.41/0.99  unif_index_add_time:                    0.
% 2.41/0.99  orderings_time:                         0.
% 2.41/0.99  out_proof_time:                         0.008
% 2.41/0.99  total_time:                             0.159
% 2.41/0.99  num_of_symbols:                         50
% 2.41/0.99  num_of_terms:                           3394
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing
% 2.41/0.99  
% 2.41/0.99  num_of_splits:                          0
% 2.41/0.99  num_of_split_atoms:                     0
% 2.41/0.99  num_of_reused_defs:                     0
% 2.41/0.99  num_eq_ax_congr_red:                    33
% 2.41/0.99  num_of_sem_filtered_clauses:            1
% 2.41/0.99  num_of_subtypes:                        0
% 2.41/0.99  monotx_restored_types:                  0
% 2.41/0.99  sat_num_of_epr_types:                   0
% 2.41/0.99  sat_num_of_non_cyclic_types:            0
% 2.41/0.99  sat_guarded_non_collapsed_types:        0
% 2.41/0.99  num_pure_diseq_elim:                    0
% 2.41/0.99  simp_replaced_by:                       0
% 2.41/0.99  res_preprocessed:                       102
% 2.41/0.99  prep_upred:                             0
% 2.41/0.99  prep_unflattend:                        34
% 2.41/0.99  smt_new_axioms:                         0
% 2.41/0.99  pred_elim_cands:                        3
% 2.41/0.99  pred_elim:                              4
% 2.41/0.99  pred_elim_cl:                           5
% 2.41/0.99  pred_elim_cycles:                       6
% 2.41/0.99  merged_defs:                            8
% 2.41/0.99  merged_defs_ncl:                        0
% 2.41/0.99  bin_hyper_res:                          10
% 2.41/0.99  prep_cycles:                            4
% 2.41/0.99  pred_elim_time:                         0.008
% 2.41/0.99  splitting_time:                         0.
% 2.41/0.99  sem_filter_time:                        0.
% 2.41/0.99  monotx_time:                            0.
% 2.41/0.99  subtype_inf_time:                       0.
% 2.41/0.99  
% 2.41/0.99  ------ Problem properties
% 2.41/0.99  
% 2.41/0.99  clauses:                                17
% 2.41/0.99  conjectures:                            1
% 2.41/0.99  epr:                                    2
% 2.41/0.99  horn:                                   17
% 2.41/0.99  ground:                                 6
% 2.41/0.99  unary:                                  10
% 2.41/0.99  binary:                                 4
% 2.41/0.99  lits:                                   28
% 2.41/0.99  lits_eq:                                9
% 2.41/0.99  fd_pure:                                0
% 2.41/0.99  fd_pseudo:                              0
% 2.41/0.99  fd_cond:                                0
% 2.41/0.99  fd_pseudo_cond:                         1
% 2.41/0.99  ac_symbols:                             0
% 2.41/0.99  
% 2.41/0.99  ------ Propositional Solver
% 2.41/0.99  
% 2.41/0.99  prop_solver_calls:                      27
% 2.41/0.99  prop_fast_solver_calls:                 665
% 2.41/0.99  smt_solver_calls:                       0
% 2.41/0.99  smt_fast_solver_calls:                  0
% 2.41/0.99  prop_num_of_clauses:                    1831
% 2.41/0.99  prop_preprocess_simplified:             5872
% 2.41/0.99  prop_fo_subsumed:                       10
% 2.41/0.99  prop_solver_time:                       0.
% 2.41/0.99  smt_solver_time:                        0.
% 2.41/0.99  smt_fast_solver_time:                   0.
% 2.41/0.99  prop_fast_solver_time:                  0.
% 2.41/0.99  prop_unsat_core_time:                   0.
% 2.41/0.99  
% 2.41/0.99  ------ QBF
% 2.41/0.99  
% 2.41/0.99  qbf_q_res:                              0
% 2.41/0.99  qbf_num_tautologies:                    0
% 2.41/0.99  qbf_prep_cycles:                        0
% 2.41/0.99  
% 2.41/0.99  ------ BMC1
% 2.41/0.99  
% 2.41/0.99  bmc1_current_bound:                     -1
% 2.41/0.99  bmc1_last_solved_bound:                 -1
% 2.41/0.99  bmc1_unsat_core_size:                   -1
% 2.41/0.99  bmc1_unsat_core_parents_size:           -1
% 2.41/0.99  bmc1_merge_next_fun:                    0
% 2.41/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation
% 2.41/0.99  
% 2.41/0.99  inst_num_of_clauses:                    610
% 2.41/0.99  inst_num_in_passive:                    294
% 2.41/0.99  inst_num_in_active:                     275
% 2.41/0.99  inst_num_in_unprocessed:                41
% 2.41/0.99  inst_num_of_loops:                      280
% 2.41/0.99  inst_num_of_learning_restarts:          0
% 2.41/0.99  inst_num_moves_active_passive:          3
% 2.41/0.99  inst_lit_activity:                      0
% 2.41/0.99  inst_lit_activity_moves:                0
% 2.41/0.99  inst_num_tautologies:                   0
% 2.41/0.99  inst_num_prop_implied:                  0
% 2.41/0.99  inst_num_existing_simplified:           0
% 2.41/0.99  inst_num_eq_res_simplified:             0
% 2.41/0.99  inst_num_child_elim:                    0
% 2.41/0.99  inst_num_of_dismatching_blockings:      129
% 2.41/0.99  inst_num_of_non_proper_insts:           571
% 2.41/0.99  inst_num_of_duplicates:                 0
% 2.41/0.99  inst_inst_num_from_inst_to_res:         0
% 2.41/0.99  inst_dismatching_checking_time:         0.
% 2.41/0.99  
% 2.41/0.99  ------ Resolution
% 2.41/0.99  
% 2.41/0.99  res_num_of_clauses:                     0
% 2.41/0.99  res_num_in_passive:                     0
% 2.41/0.99  res_num_in_active:                      0
% 2.41/0.99  res_num_of_loops:                       106
% 2.41/0.99  res_forward_subset_subsumed:            78
% 2.41/0.99  res_backward_subset_subsumed:           0
% 2.41/0.99  res_forward_subsumed:                   0
% 2.41/0.99  res_backward_subsumed:                  0
% 2.41/0.99  res_forward_subsumption_resolution:     0
% 2.41/0.99  res_backward_subsumption_resolution:    0
% 2.41/0.99  res_clause_to_clause_subsumption:       215
% 2.41/0.99  res_orphan_elimination:                 0
% 2.41/0.99  res_tautology_del:                      84
% 2.41/0.99  res_num_eq_res_simplified:              0
% 2.41/0.99  res_num_sel_changes:                    0
% 2.41/0.99  res_moves_from_active_to_pass:          0
% 2.41/0.99  
% 2.41/0.99  ------ Superposition
% 2.41/0.99  
% 2.41/0.99  sup_time_total:                         0.
% 2.41/0.99  sup_time_generating:                    0.
% 2.41/0.99  sup_time_sim_full:                      0.
% 2.41/0.99  sup_time_sim_immed:                     0.
% 2.41/0.99  
% 2.41/0.99  sup_num_of_clauses:                     39
% 2.41/0.99  sup_num_in_active:                      33
% 2.41/0.99  sup_num_in_passive:                     6
% 2.41/0.99  sup_num_of_loops:                       55
% 2.41/0.99  sup_fw_superposition:                   31
% 2.41/0.99  sup_bw_superposition:                   26
% 2.41/0.99  sup_immediate_simplified:               18
% 2.41/0.99  sup_given_eliminated:                   1
% 2.41/0.99  comparisons_done:                       0
% 2.41/0.99  comparisons_avoided:                    0
% 2.41/0.99  
% 2.41/0.99  ------ Simplifications
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  sim_fw_subset_subsumed:                 0
% 2.41/0.99  sim_bw_subset_subsumed:                 2
% 2.41/0.99  sim_fw_subsumed:                        1
% 2.41/0.99  sim_bw_subsumed:                        0
% 2.41/0.99  sim_fw_subsumption_res:                 1
% 2.41/0.99  sim_bw_subsumption_res:                 0
% 2.41/0.99  sim_tautology_del:                      14
% 2.41/0.99  sim_eq_tautology_del:                   3
% 2.41/0.99  sim_eq_res_simp:                        0
% 2.41/0.99  sim_fw_demodulated:                     4
% 2.41/0.99  sim_bw_demodulated:                     22
% 2.41/0.99  sim_light_normalised:                   27
% 2.41/0.99  sim_joinable_taut:                      0
% 2.41/0.99  sim_joinable_simp:                      0
% 2.41/0.99  sim_ac_normalised:                      0
% 2.41/0.99  sim_smt_subsumption:                    0
% 2.41/0.99  
%------------------------------------------------------------------------------
