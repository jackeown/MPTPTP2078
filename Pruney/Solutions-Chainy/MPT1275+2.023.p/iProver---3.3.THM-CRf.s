%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:26 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_718)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f84])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f86])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f87])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK1) != sK1
          | ~ v3_tops_1(sK1,X0) )
        & ( k2_tops_1(X0,sK1) = sK1
          | v3_tops_1(sK1,X0) )
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X0] : k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_485,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_486,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(X1,sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1591,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(equality_resolution,[status(thm)],[c_486])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_461,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_462,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_subset_1(X1) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_437,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
    | k1_subset_1(X1) = X0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_438,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0)
    | k1_subset_1(X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_448,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | k1_subset_1(X1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_438,c_3])).

cnf(c_1673,plain,
    ( k1_subset_1(X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_448])).

cnf(c_4,plain,
    ( k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2032,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1673,c_4])).

cnf(c_2459,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_462,c_2032])).

cnf(c_2463,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2459])).

cnf(c_2565,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_1591,c_2463])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_376,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_377,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_379,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_849,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_21,c_379])).

cnf(c_1452,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_378,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_380,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_16,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_172,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_326,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_172])).

cnf(c_327,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_329,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_22,c_21])).

cnf(c_841,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_22,c_21,c_327])).

cnf(c_1457,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_72,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_76,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_331,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_14,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_361,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_362,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_616,plain,
    ( v2_tops_1(X0,sK0)
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_362])).

cnf(c_617,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_17,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_288,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_289,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_291,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_22,c_21])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_170,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_314,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(resolution,[status(thm)],[c_291,c_170])).

cnf(c_683,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(resolution,[status(thm)],[c_617,c_314])).

cnf(c_1061,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1608,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1610,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_1814,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1457,c_23,c_24,c_72,c_76,c_328,c_683,c_1610])).

cnf(c_2211,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_72,c_76,c_683,c_718,c_1610])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_591,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_407])).

cnf(c_592,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_303,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_305,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_22,c_21])).

cnf(c_1486,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_592,c_305])).

cnf(c_2214,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2211,c_1486])).

cnf(c_2786,plain,
    ( k2_tops_1(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2565,c_2214])).

cnf(c_315,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2786,c_1814,c_315])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.02/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/1.01  
% 2.02/1.01  ------  iProver source info
% 2.02/1.01  
% 2.02/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.02/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/1.01  git: non_committed_changes: false
% 2.02/1.01  git: last_make_outside_of_git: false
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     num_symb
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       true
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    true
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  ------ Parsing...
% 2.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/1.01  ------ Proving...
% 2.02/1.01  ------ Problem Properties 
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  clauses                                 22
% 2.02/1.01  conjectures                             0
% 2.02/1.01  EPR                                     3
% 2.02/1.01  Horn                                    21
% 2.02/1.01  unary                                   5
% 2.02/1.01  binary                                  15
% 2.02/1.01  lits                                    41
% 2.02/1.01  lits eq                                 26
% 2.02/1.01  fd_pure                                 0
% 2.02/1.01  fd_pseudo                               0
% 2.02/1.01  fd_cond                                 0
% 2.02/1.01  fd_pseudo_cond                          1
% 2.02/1.01  AC symbols                              0
% 2.02/1.01  
% 2.02/1.01  ------ Schedule dynamic 5 is on 
% 2.02/1.01  
% 2.02/1.01  ------ no conjectures: strip conj schedule 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  Current options:
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     none
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       false
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    true
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ Proving...
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  % SZS status Theorem for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  fof(f12,axiom,(
% 2.02/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f29,plain,(
% 2.02/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f12])).
% 2.02/1.01  
% 2.02/1.01  fof(f65,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f29])).
% 2.02/1.01  
% 2.02/1.01  fof(f2,axiom,(
% 2.02/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f55,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f2])).
% 2.02/1.01  
% 2.02/1.01  fof(f16,axiom,(
% 2.02/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f70,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f16])).
% 2.02/1.01  
% 2.02/1.01  fof(f4,axiom,(
% 2.02/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f57,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f4])).
% 2.02/1.01  
% 2.02/1.01  fof(f5,axiom,(
% 2.02/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f58,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f5])).
% 2.02/1.01  
% 2.02/1.01  fof(f6,axiom,(
% 2.02/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f59,plain,(
% 2.02/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f6])).
% 2.02/1.01  
% 2.02/1.01  fof(f7,axiom,(
% 2.02/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f60,plain,(
% 2.02/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f7])).
% 2.02/1.01  
% 2.02/1.01  fof(f8,axiom,(
% 2.02/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f61,plain,(
% 2.02/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f8])).
% 2.02/1.01  
% 2.02/1.01  fof(f9,axiom,(
% 2.02/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f62,plain,(
% 2.02/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f9])).
% 2.02/1.01  
% 2.02/1.01  fof(f84,plain,(
% 2.02/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.02/1.01    inference(definition_unfolding,[],[f61,f62])).
% 2.02/1.01  
% 2.02/1.01  fof(f85,plain,(
% 2.02/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.02/1.01    inference(definition_unfolding,[],[f60,f84])).
% 2.02/1.01  
% 2.02/1.01  fof(f86,plain,(
% 2.02/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.02/1.01    inference(definition_unfolding,[],[f59,f85])).
% 2.02/1.01  
% 2.02/1.01  fof(f87,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.02/1.01    inference(definition_unfolding,[],[f58,f86])).
% 2.02/1.01  
% 2.02/1.01  fof(f88,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.02/1.01    inference(definition_unfolding,[],[f57,f87])).
% 2.02/1.01  
% 2.02/1.01  fof(f89,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.02/1.01    inference(definition_unfolding,[],[f70,f88])).
% 2.02/1.01  
% 2.02/1.01  fof(f90,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.02/1.01    inference(definition_unfolding,[],[f55,f89])).
% 2.02/1.01  
% 2.02/1.01  fof(f93,plain,(
% 2.02/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.02/1.01    inference(definition_unfolding,[],[f65,f90])).
% 2.02/1.01  
% 2.02/1.01  fof(f24,conjecture,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f25,negated_conjecture,(
% 2.02/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.02/1.01    inference(negated_conjecture,[],[f24])).
% 2.02/1.01  
% 2.02/1.01  fof(f40,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f25])).
% 2.02/1.01  
% 2.02/1.01  fof(f41,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.02/1.01    inference(flattening,[],[f40])).
% 2.02/1.01  
% 2.02/1.01  fof(f47,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f41])).
% 2.02/1.01  
% 2.02/1.01  fof(f48,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.02/1.01    inference(flattening,[],[f47])).
% 2.02/1.01  
% 2.02/1.01  fof(f50,plain,(
% 2.02/1.01    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f49,plain,(
% 2.02/1.01    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.02/1.01    introduced(choice_axiom,[])).
% 2.02/1.01  
% 2.02/1.01  fof(f51,plain,(
% 2.02/1.01    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 2.02/1.01  
% 2.02/1.01  fof(f80,plain,(
% 2.02/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.02/1.01    inference(cnf_transformation,[],[f51])).
% 2.02/1.01  
% 2.02/1.01  fof(f11,axiom,(
% 2.02/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f28,plain,(
% 2.02/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f11])).
% 2.02/1.01  
% 2.02/1.01  fof(f64,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f28])).
% 2.02/1.01  
% 2.02/1.01  fof(f92,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.02/1.01    inference(definition_unfolding,[],[f64,f90])).
% 2.02/1.01  
% 2.02/1.01  fof(f15,axiom,(
% 2.02/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f69,plain,(
% 2.02/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f15])).
% 2.02/1.01  
% 2.02/1.01  fof(f14,axiom,(
% 2.02/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f30,plain,(
% 2.02/1.01    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/1.01    inference(ennf_transformation,[],[f14])).
% 2.02/1.01  
% 2.02/1.01  fof(f44,plain,(
% 2.02/1.01    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/1.01    inference(nnf_transformation,[],[f30])).
% 2.02/1.01  
% 2.02/1.01  fof(f67,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f44])).
% 2.02/1.01  
% 2.02/1.01  fof(f3,axiom,(
% 2.02/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f56,plain,(
% 2.02/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f3])).
% 2.02/1.01  
% 2.02/1.01  fof(f10,axiom,(
% 2.02/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f63,plain,(
% 2.02/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.02/1.01    inference(cnf_transformation,[],[f10])).
% 2.02/1.01  
% 2.02/1.01  fof(f13,axiom,(
% 2.02/1.01    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f66,plain,(
% 2.02/1.01    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.02/1.01    inference(cnf_transformation,[],[f13])).
% 2.02/1.01  
% 2.02/1.01  fof(f91,plain,(
% 2.02/1.01    ( ! [X0] : (k3_subset_1(X0,k1_subset_1(X0)) = X0) )),
% 2.02/1.01    inference(definition_unfolding,[],[f63,f66])).
% 2.02/1.01  
% 2.02/1.01  fof(f20,axiom,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f34,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f20])).
% 2.02/1.01  
% 2.02/1.01  fof(f45,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f34])).
% 2.02/1.01  
% 2.02/1.01  fof(f73,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f45])).
% 2.02/1.01  
% 2.02/1.01  fof(f79,plain,(
% 2.02/1.01    l1_pre_topc(sK0)),
% 2.02/1.01    inference(cnf_transformation,[],[f51])).
% 2.02/1.01  
% 2.02/1.01  fof(f22,axiom,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f36,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f22])).
% 2.02/1.01  
% 2.02/1.01  fof(f37,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(flattening,[],[f36])).
% 2.02/1.01  
% 2.02/1.01  fof(f77,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f37])).
% 2.02/1.01  
% 2.02/1.01  fof(f82,plain,(
% 2.02/1.01    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 2.02/1.01    inference(cnf_transformation,[],[f51])).
% 2.02/1.01  
% 2.02/1.01  fof(f1,axiom,(
% 2.02/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f42,plain,(
% 2.02/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/1.01    inference(nnf_transformation,[],[f1])).
% 2.02/1.01  
% 2.02/1.01  fof(f43,plain,(
% 2.02/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/1.01    inference(flattening,[],[f42])).
% 2.02/1.01  
% 2.02/1.01  fof(f52,plain,(
% 2.02/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f95,plain,(
% 2.02/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/1.01    inference(equality_resolution,[],[f52])).
% 2.02/1.01  
% 2.02/1.01  fof(f54,plain,(
% 2.02/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f43])).
% 2.02/1.01  
% 2.02/1.01  fof(f21,axiom,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f35,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f21])).
% 2.02/1.01  
% 2.02/1.01  fof(f46,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(nnf_transformation,[],[f35])).
% 2.02/1.01  
% 2.02/1.01  fof(f76,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f46])).
% 2.02/1.01  
% 2.02/1.01  fof(f23,axiom,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f38,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f23])).
% 2.02/1.01  
% 2.02/1.01  fof(f39,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(flattening,[],[f38])).
% 2.02/1.01  
% 2.02/1.01  fof(f78,plain,(
% 2.02/1.01    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f39])).
% 2.02/1.01  
% 2.02/1.01  fof(f81,plain,(
% 2.02/1.01    v4_pre_topc(sK1,sK0)),
% 2.02/1.01    inference(cnf_transformation,[],[f51])).
% 2.02/1.01  
% 2.02/1.01  fof(f83,plain,(
% 2.02/1.01    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 2.02/1.01    inference(cnf_transformation,[],[f51])).
% 2.02/1.01  
% 2.02/1.01  fof(f19,axiom,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f33,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f19])).
% 2.02/1.01  
% 2.02/1.01  fof(f72,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f33])).
% 2.02/1.01  
% 2.02/1.01  fof(f18,axiom,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.02/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.02/1.01  
% 2.02/1.01  fof(f26,plain,(
% 2.02/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 2.02/1.01    inference(pure_predicate_removal,[],[f18])).
% 2.02/1.01  
% 2.02/1.01  fof(f31,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(ennf_transformation,[],[f26])).
% 2.02/1.01  
% 2.02/1.01  fof(f32,plain,(
% 2.02/1.01    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.01    inference(flattening,[],[f31])).
% 2.02/1.01  
% 2.02/1.01  fof(f71,plain,(
% 2.02/1.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.01    inference(cnf_transformation,[],[f32])).
% 2.02/1.01  
% 2.02/1.01  cnf(c_6,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.02/1.01      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.02/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_21,negated_conjecture,
% 2.02/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.02/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_485,plain,
% 2.02/1.01      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.02/1.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X2)
% 2.02/1.01      | sK1 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_486,plain,
% 2.02/1.01      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(X1,sK1,X0)
% 2.02/1.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_485]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1591,plain,
% 2.02/1.01      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.02/1.01      inference(equality_resolution,[status(thm)],[c_486]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_5,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.02/1.01      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_9,plain,
% 2.02/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.02/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_461,plain,
% 2.02/1.01      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 2.02/1.01      | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
% 2.02/1.01      | k1_xboole_0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_462,plain,
% 2.02/1.01      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)
% 2.02/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_461]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_8,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.02/1.01      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 2.02/1.01      | k1_subset_1(X1) = X0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_437,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 2.02/1.01      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1)
% 2.02/1.01      | k1_subset_1(X1) = X0
% 2.02/1.01      | k1_xboole_0 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_438,plain,
% 2.02/1.01      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
% 2.02/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0)
% 2.02/1.01      | k1_subset_1(X0) = k1_xboole_0 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_437]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_3,plain,
% 2.02/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_448,plain,
% 2.02/1.01      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 2.02/1.01      | k1_subset_1(X1) = k1_xboole_0 ),
% 2.02/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_438,c_3]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1673,plain,
% 2.02/1.01      ( k1_subset_1(X0) = k1_xboole_0 ),
% 2.02/1.01      inference(equality_resolution,[status(thm)],[c_448]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_4,plain,
% 2.02/1.01      ( k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2032,plain,
% 2.02/1.01      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.02/1.01      inference(demodulation,[status(thm)],[c_1673,c_4]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2459,plain,
% 2.02/1.01      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0
% 2.02/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 2.02/1.01      inference(light_normalisation,[status(thm)],[c_462,c_2032]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2463,plain,
% 2.02/1.01      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 2.02/1.01      inference(equality_resolution,[status(thm)],[c_2459]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2565,plain,
% 2.02/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
% 2.02/1.01      inference(superposition,[status(thm)],[c_1591,c_2463]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_13,plain,
% 2.02/1.01      ( ~ v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1)
% 2.02/1.01      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_22,negated_conjecture,
% 2.02/1.01      ( l1_pre_topc(sK0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_376,plain,
% 2.02/1.01      ( ~ v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.02/1.01      | sK0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_377,plain,
% 2.02/1.01      ( ~ v2_tops_1(X0,sK0)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_376]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_379,plain,
% 2.02/1.01      ( ~ v2_tops_1(sK1,sK0)
% 2.02/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_377]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_849,plain,
% 2.02/1.01      ( ~ v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.02/1.01      inference(prop_impl,[status(thm)],[c_21,c_379]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1452,plain,
% 2.02/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.02/1.01      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_24,plain,
% 2.02/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_378,plain,
% 2.02/1.01      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.02/1.01      | v2_tops_1(X0,sK0) != iProver_top
% 2.02/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_380,plain,
% 2.02/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.02/1.01      | v2_tops_1(sK1,sK0) != iProver_top
% 2.02/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_378]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_16,plain,
% 2.02/1.01      ( ~ v3_tops_1(X0,X1)
% 2.02/1.01      | v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_19,negated_conjecture,
% 2.02/1.01      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_172,plain,
% 2.02/1.01      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_326,plain,
% 2.02/1.01      ( v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1)
% 2.02/1.01      | k2_tops_1(sK0,sK1) = sK1
% 2.02/1.01      | sK1 != X0
% 2.02/1.01      | sK0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_172]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_327,plain,
% 2.02/1.01      ( v2_tops_1(sK1,sK0)
% 2.02/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | ~ l1_pre_topc(sK0)
% 2.02/1.01      | k2_tops_1(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_326]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_329,plain,
% 2.02/1.01      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_327,c_22,c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_841,plain,
% 2.02/1.01      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(prop_impl,[status(thm)],[c_22,c_21,c_327]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1457,plain,
% 2.02/1.01      ( k2_tops_1(sK0,sK1) = sK1 | v2_tops_1(sK1,sK0) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2,plain,
% 2.02/1.01      ( r1_tarski(X0,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_72,plain,
% 2.02/1.01      ( r1_tarski(sK1,sK1) ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_0,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.02/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_76,plain,
% 2.02/1.01      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_331,plain,
% 2.02/1.01      ( k2_tops_1(sK0,sK1) = sK1 | v2_tops_1(sK1,sK0) = iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_14,plain,
% 2.02/1.01      ( v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.02/1.01      | ~ l1_pre_topc(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_361,plain,
% 2.02/1.01      ( v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.02/1.01      | sK0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_362,plain,
% 2.02/1.01      ( v2_tops_1(X0,sK0)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_616,plain,
% 2.02/1.01      ( v2_tops_1(X0,sK0)
% 2.02/1.01      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 2.02/1.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.02/1.01      | sK1 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_362]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_617,plain,
% 2.02/1.01      ( v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_616]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_17,plain,
% 2.02/1.01      ( v3_tops_1(X0,X1)
% 2.02/1.01      | ~ v2_tops_1(X0,X1)
% 2.02/1.01      | ~ v4_pre_topc(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1) ),
% 2.02/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_20,negated_conjecture,
% 2.02/1.01      ( v4_pre_topc(sK1,sK0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_288,plain,
% 2.02/1.01      ( v3_tops_1(X0,X1)
% 2.02/1.01      | ~ v2_tops_1(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1)
% 2.02/1.01      | sK1 != X0
% 2.02/1.01      | sK0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_289,plain,
% 2.02/1.01      ( v3_tops_1(sK1,sK0)
% 2.02/1.01      | ~ v2_tops_1(sK1,sK0)
% 2.02/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | ~ l1_pre_topc(sK0) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_288]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_291,plain,
% 2.02/1.01      ( v3_tops_1(sK1,sK0) | ~ v2_tops_1(sK1,sK0) ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_289,c_22,c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_18,negated_conjecture,
% 2.02/1.01      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.02/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_170,plain,
% 2.02/1.01      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.02/1.01      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_314,plain,
% 2.02/1.01      ( ~ v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.02/1.01      inference(resolution,[status(thm)],[c_291,c_170]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_683,plain,
% 2.02/1.01      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.02/1.01      inference(resolution,[status(thm)],[c_617,c_314]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1061,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.02/1.01      theory(equality) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1608,plain,
% 2.02/1.01      ( ~ r1_tarski(X0,X1)
% 2.02/1.01      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.02/1.01      | k2_tops_1(sK0,sK1) != X1
% 2.02/1.01      | sK1 != X0 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1061]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1610,plain,
% 2.02/1.01      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.02/1.01      | ~ r1_tarski(sK1,sK1)
% 2.02/1.01      | k2_tops_1(sK0,sK1) != sK1
% 2.02/1.01      | sK1 != sK1 ),
% 2.02/1.01      inference(instantiation,[status(thm)],[c_1608]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1814,plain,
% 2.02/1.01      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_1457,c_23,c_24,c_72,c_76,c_328,c_683,c_1610]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2211,plain,
% 2.02/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_1452,c_72,c_76,c_683,c_718,c_1610]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_11,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1)
% 2.02/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.02/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_406,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.02/1.01      | sK0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_407,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_406]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_591,plain,
% 2.02/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.02/1.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.02/1.01      | sK1 != X0 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_407]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_592,plain,
% 2.02/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_591]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_10,plain,
% 2.02/1.01      ( ~ v4_pre_topc(X0,X1)
% 2.02/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1)
% 2.02/1.01      | k2_pre_topc(X1,X0) = X0 ),
% 2.02/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_302,plain,
% 2.02/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.01      | ~ l1_pre_topc(X1)
% 2.02/1.01      | k2_pre_topc(X1,X0) = X0
% 2.02/1.01      | sK1 != X0
% 2.02/1.01      | sK0 != X1 ),
% 2.02/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_303,plain,
% 2.02/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.01      | ~ l1_pre_topc(sK0)
% 2.02/1.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(unflattening,[status(thm)],[c_302]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_305,plain,
% 2.02/1.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(global_propositional_subsumption,
% 2.02/1.01                [status(thm)],
% 2.02/1.01                [c_303,c_22,c_21]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_1486,plain,
% 2.02/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.02/1.01      inference(light_normalisation,[status(thm)],[c_592,c_305]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2214,plain,
% 2.02/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.02/1.01      inference(demodulation,[status(thm)],[c_2211,c_1486]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_2786,plain,
% 2.02/1.01      ( k2_tops_1(sK0,sK1) = sK1 ),
% 2.02/1.01      inference(demodulation,[status(thm)],[c_2565,c_2214]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(c_315,plain,
% 2.02/1.01      ( k2_tops_1(sK0,sK1) != sK1 | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.02/1.01      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.02/1.01  
% 2.02/1.01  cnf(contradiction,plain,
% 2.02/1.01      ( $false ),
% 2.02/1.01      inference(minisat,[status(thm)],[c_2786,c_1814,c_315]) ).
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  ------                               Statistics
% 2.02/1.01  
% 2.02/1.01  ------ General
% 2.02/1.01  
% 2.02/1.01  abstr_ref_over_cycles:                  0
% 2.02/1.01  abstr_ref_under_cycles:                 0
% 2.02/1.01  gc_basic_clause_elim:                   0
% 2.02/1.01  forced_gc_time:                         0
% 2.02/1.01  parsing_time:                           0.022
% 2.02/1.01  unif_index_cands_time:                  0.
% 2.02/1.01  unif_index_add_time:                    0.
% 2.02/1.01  orderings_time:                         0.
% 2.02/1.01  out_proof_time:                         0.008
% 2.02/1.01  total_time:                             0.181
% 2.02/1.01  num_of_symbols:                         51
% 2.02/1.01  num_of_terms:                           1833
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing
% 2.02/1.01  
% 2.02/1.01  num_of_splits:                          0
% 2.02/1.01  num_of_split_atoms:                     0
% 2.02/1.01  num_of_reused_defs:                     0
% 2.02/1.01  num_eq_ax_congr_red:                    21
% 2.02/1.01  num_of_sem_filtered_clauses:            1
% 2.02/1.01  num_of_subtypes:                        0
% 2.02/1.01  monotx_restored_types:                  0
% 2.02/1.01  sat_num_of_epr_types:                   0
% 2.02/1.01  sat_num_of_non_cyclic_types:            0
% 2.02/1.01  sat_guarded_non_collapsed_types:        0
% 2.02/1.01  num_pure_diseq_elim:                    0
% 2.02/1.01  simp_replaced_by:                       0
% 2.02/1.01  res_preprocessed:                       117
% 2.02/1.01  prep_upred:                             0
% 2.02/1.01  prep_unflattend:                        29
% 2.02/1.01  smt_new_axioms:                         0
% 2.02/1.01  pred_elim_cands:                        2
% 2.02/1.01  pred_elim:                              4
% 2.02/1.01  pred_elim_cl:                           0
% 2.02/1.01  pred_elim_cycles:                       6
% 2.02/1.01  merged_defs:                            20
% 2.02/1.01  merged_defs_ncl:                        0
% 2.02/1.01  bin_hyper_res:                          20
% 2.02/1.01  prep_cycles:                            4
% 2.02/1.01  pred_elim_time:                         0.027
% 2.02/1.01  splitting_time:                         0.
% 2.02/1.01  sem_filter_time:                        0.
% 2.02/1.01  monotx_time:                            0.
% 2.02/1.01  subtype_inf_time:                       0.
% 2.02/1.01  
% 2.02/1.01  ------ Problem properties
% 2.02/1.01  
% 2.02/1.01  clauses:                                22
% 2.02/1.01  conjectures:                            0
% 2.02/1.01  epr:                                    3
% 2.02/1.01  horn:                                   21
% 2.02/1.01  ground:                                 8
% 2.02/1.01  unary:                                  5
% 2.02/1.01  binary:                                 15
% 2.02/1.01  lits:                                   41
% 2.02/1.01  lits_eq:                                26
% 2.02/1.01  fd_pure:                                0
% 2.02/1.01  fd_pseudo:                              0
% 2.02/1.01  fd_cond:                                0
% 2.02/1.01  fd_pseudo_cond:                         1
% 2.02/1.01  ac_symbols:                             0
% 2.02/1.01  
% 2.02/1.01  ------ Propositional Solver
% 2.02/1.01  
% 2.02/1.01  prop_solver_calls:                      27
% 2.02/1.01  prop_fast_solver_calls:                 737
% 2.02/1.01  smt_solver_calls:                       0
% 2.02/1.01  smt_fast_solver_calls:                  0
% 2.02/1.01  prop_num_of_clauses:                    848
% 2.02/1.01  prop_preprocess_simplified:             3518
% 2.02/1.01  prop_fo_subsumed:                       16
% 2.02/1.01  prop_solver_time:                       0.
% 2.02/1.01  smt_solver_time:                        0.
% 2.02/1.01  smt_fast_solver_time:                   0.
% 2.02/1.01  prop_fast_solver_time:                  0.
% 2.02/1.01  prop_unsat_core_time:                   0.
% 2.02/1.01  
% 2.02/1.01  ------ QBF
% 2.02/1.01  
% 2.02/1.01  qbf_q_res:                              0
% 2.02/1.01  qbf_num_tautologies:                    0
% 2.02/1.01  qbf_prep_cycles:                        0
% 2.02/1.01  
% 2.02/1.01  ------ BMC1
% 2.02/1.01  
% 2.02/1.01  bmc1_current_bound:                     -1
% 2.02/1.01  bmc1_last_solved_bound:                 -1
% 2.02/1.01  bmc1_unsat_core_size:                   -1
% 2.02/1.01  bmc1_unsat_core_parents_size:           -1
% 2.02/1.01  bmc1_merge_next_fun:                    0
% 2.02/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation
% 2.02/1.01  
% 2.02/1.01  inst_num_of_clauses:                    292
% 2.02/1.01  inst_num_in_passive:                    70
% 2.02/1.01  inst_num_in_active:                     170
% 2.02/1.01  inst_num_in_unprocessed:                52
% 2.02/1.01  inst_num_of_loops:                      180
% 2.02/1.01  inst_num_of_learning_restarts:          0
% 2.02/1.01  inst_num_moves_active_passive:          6
% 2.02/1.01  inst_lit_activity:                      0
% 2.02/1.01  inst_lit_activity_moves:                0
% 2.02/1.01  inst_num_tautologies:                   0
% 2.02/1.01  inst_num_prop_implied:                  0
% 2.02/1.01  inst_num_existing_simplified:           0
% 2.02/1.01  inst_num_eq_res_simplified:             0
% 2.02/1.01  inst_num_child_elim:                    0
% 2.02/1.01  inst_num_of_dismatching_blockings:      24
% 2.02/1.01  inst_num_of_non_proper_insts:           276
% 2.02/1.01  inst_num_of_duplicates:                 0
% 2.02/1.01  inst_inst_num_from_inst_to_res:         0
% 2.02/1.01  inst_dismatching_checking_time:         0.
% 2.02/1.01  
% 2.02/1.01  ------ Resolution
% 2.02/1.01  
% 2.02/1.01  res_num_of_clauses:                     0
% 2.02/1.01  res_num_in_passive:                     0
% 2.02/1.01  res_num_in_active:                      0
% 2.02/1.01  res_num_of_loops:                       121
% 2.02/1.01  res_forward_subset_subsumed:            45
% 2.02/1.01  res_backward_subset_subsumed:           2
% 2.02/1.01  res_forward_subsumed:                   2
% 2.02/1.01  res_backward_subsumed:                  1
% 2.02/1.01  res_forward_subsumption_resolution:     3
% 2.02/1.01  res_backward_subsumption_resolution:    1
% 2.02/1.01  res_clause_to_clause_subsumption:       100
% 2.02/1.01  res_orphan_elimination:                 0
% 2.02/1.01  res_tautology_del:                      64
% 2.02/1.01  res_num_eq_res_simplified:              0
% 2.02/1.01  res_num_sel_changes:                    0
% 2.02/1.01  res_moves_from_active_to_pass:          0
% 2.02/1.01  
% 2.02/1.01  ------ Superposition
% 2.02/1.01  
% 2.02/1.01  sup_time_total:                         0.
% 2.02/1.01  sup_time_generating:                    0.
% 2.02/1.01  sup_time_sim_full:                      0.
% 2.02/1.01  sup_time_sim_immed:                     0.
% 2.02/1.01  
% 2.02/1.01  sup_num_of_clauses:                     30
% 2.02/1.01  sup_num_in_active:                      24
% 2.02/1.01  sup_num_in_passive:                     6
% 2.02/1.01  sup_num_of_loops:                       34
% 2.02/1.01  sup_fw_superposition:                   9
% 2.02/1.01  sup_bw_superposition:                   4
% 2.02/1.01  sup_immediate_simplified:               3
% 2.02/1.01  sup_given_eliminated:                   0
% 2.02/1.01  comparisons_done:                       0
% 2.02/1.01  comparisons_avoided:                    0
% 2.02/1.01  
% 2.02/1.01  ------ Simplifications
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  sim_fw_subset_subsumed:                 0
% 2.02/1.01  sim_bw_subset_subsumed:                 5
% 2.02/1.01  sim_fw_subsumed:                        2
% 2.02/1.01  sim_bw_subsumed:                        0
% 2.02/1.01  sim_fw_subsumption_res:                 0
% 2.02/1.01  sim_bw_subsumption_res:                 0
% 2.02/1.01  sim_tautology_del:                      0
% 2.02/1.01  sim_eq_tautology_del:                   4
% 2.02/1.01  sim_eq_res_simp:                        0
% 2.02/1.01  sim_fw_demodulated:                     1
% 2.02/1.01  sim_bw_demodulated:                     8
% 2.02/1.01  sim_light_normalised:                   3
% 2.02/1.01  sim_joinable_taut:                      0
% 2.02/1.01  sim_joinable_simp:                      0
% 2.02/1.01  sim_ac_normalised:                      0
% 2.02/1.01  sim_smt_subsumption:                    0
% 2.02/1.01  
%------------------------------------------------------------------------------
