%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:30 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 858 expanded)
%              Number of clauses        :  115 ( 250 expanded)
%              Number of leaves         :   28 ( 192 expanded)
%              Depth                    :   21
%              Number of atoms          :  538 (3944 expanded)
%              Number of equality atoms :  218 (1095 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f88])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f90])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f91])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f92])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f93])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f94])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f94])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1789,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1790,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2317,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_1790])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_201])).

cnf(c_1784,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_4039,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_2317,c_1784])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1794,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_201])).

cnf(c_1787,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_3270,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1794,c_1787])).

cnf(c_4157,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4039,c_3270])).

cnf(c_16,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_418,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_419,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_15,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_433,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_434,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_419,c_434])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_952,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_23,c_512])).

cnf(c_1777,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_511,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_513,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_14,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_448,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_449,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_17,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_403,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_404,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_449,c_404])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_950,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_23,c_498])).

cnf(c_1776,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_54,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_18,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_204,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_383,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_204])).

cnf(c_384,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_386,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_24,c_23])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_tops_1(sK0,X0))
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_404])).

cnf(c_537,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_23])).

cnf(c_541,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1299,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1324,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1793,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1793,c_1])).

cnf(c_1892,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_1301,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1936,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_tops_1(sK0,X2))
    | X2 != X0
    | k2_tops_1(sK0,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_1937,plain,
    ( X0 != X1
    | k2_tops_1(sK0,X0) != X2
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_1939,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_2015,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_56,c_541,c_1324,c_1892,c_1939])).

cnf(c_2508,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1777,c_26,c_56,c_513,c_541,c_1324,c_1892,c_1939])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_1782,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_1933,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1789,c_1782])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_362,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_24,c_23])).

cnf(c_1934,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1933,c_362])).

cnf(c_2511,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2508,c_1934])).

cnf(c_4235,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4157,c_2511])).

cnf(c_19,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_345,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_346,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_348,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_24,c_23])).

cnf(c_20,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_202,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_371,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(resolution,[status(thm)],[c_348,c_202])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_419])).

cnf(c_562,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_564,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_23])).

cnf(c_946,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_23,c_562])).

cnf(c_1778,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_566,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_2605,plain,
    ( k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1778,c_56,c_541,c_566,c_1324,c_1892,c_1939])).

cnf(c_4239,plain,
    ( k3_subset_1(sK1,k1_xboole_0) != sK1 ),
    inference(demodulation,[status(thm)],[c_4235,c_2605])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_242,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_201])).

cnf(c_1786,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_3137,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_1790])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_243,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_201])).

cnf(c_1785,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_2955,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1794,c_1785])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X0),X0)
    | k2_subset_1(X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_245,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X1,X0),X0)
    | k2_subset_1(X1) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_201])).

cnf(c_1783,plain,
    ( k2_subset_1(X0) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_1843,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1783,c_1])).

cnf(c_3066,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0
    | r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2955,c_1843])).

cnf(c_3904,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0
    | r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3066,c_1794])).

cnf(c_3908,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3137,c_3904])).

cnf(c_3917,plain,
    ( k3_subset_1(sK1,k1_xboole_0) = sK1
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3908])).

cnf(c_85,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_87,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4239,c_3917,c_87])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.19/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.98  
% 3.19/0.98  ------  iProver source info
% 3.19/0.98  
% 3.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.98  git: non_committed_changes: false
% 3.19/0.98  git: last_make_outside_of_git: false
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    --mode clausify
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         false
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     num_symb
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       true
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     false
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   []
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_full_bw                           [BwDemod]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  ------ Parsing...
% 3.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.98  ------ Proving...
% 3.19/0.98  ------ Problem Properties 
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  clauses                                 21
% 3.19/0.98  conjectures                             1
% 3.19/0.98  EPR                                     1
% 3.19/0.98  Horn                                    20
% 3.19/0.98  unary                                   7
% 3.19/0.98  binary                                  11
% 3.19/0.98  lits                                    38
% 3.19/0.98  lits eq                                 13
% 3.19/0.98  fd_pure                                 0
% 3.19/0.98  fd_pseudo                               0
% 3.19/0.98  fd_cond                                 0
% 3.19/0.98  fd_pseudo_cond                          1
% 3.19/0.98  AC symbols                              0
% 3.19/0.98  
% 3.19/0.98  ------ Schedule dynamic 5 is on 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  Current options:
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    --mode clausify
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         false
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     none
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       false
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     false
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   []
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_full_bw                           [BwDemod]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ Proving...
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  % SZS status Theorem for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  fof(f26,conjecture,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f27,negated_conjecture,(
% 3.19/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.19/0.98    inference(negated_conjecture,[],[f26])).
% 3.19/0.98  
% 3.19/0.98  fof(f44,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f27])).
% 3.19/0.98  
% 3.19/0.98  fof(f45,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f44])).
% 3.19/0.98  
% 3.19/0.98  fof(f50,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f45])).
% 3.19/0.98  
% 3.19/0.98  fof(f51,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f50])).
% 3.19/0.98  
% 3.19/0.98  fof(f53,plain,(
% 3.19/0.98    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f52,plain,(
% 3.19/0.98    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f54,plain,(
% 3.19/0.98    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).
% 3.19/0.98  
% 3.19/0.98  fof(f84,plain,(
% 3.19/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.19/0.98    inference(cnf_transformation,[],[f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f18,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f47,plain,(
% 3.19/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.19/0.98    inference(nnf_transformation,[],[f18])).
% 3.19/0.98  
% 3.19/0.98  fof(f73,plain,(
% 3.19/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f47])).
% 3.19/0.98  
% 3.19/0.98  fof(f14,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f33,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f14])).
% 3.19/0.98  
% 3.19/0.98  fof(f68,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f33])).
% 3.19/0.98  
% 3.19/0.98  fof(f1,axiom,(
% 3.19/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f55,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f1])).
% 3.19/0.98  
% 3.19/0.98  fof(f17,axiom,(
% 3.19/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f72,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f17])).
% 3.19/0.98  
% 3.19/0.98  fof(f3,axiom,(
% 3.19/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f57,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f3])).
% 3.19/0.98  
% 3.19/0.98  fof(f4,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f58,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f4])).
% 3.19/0.98  
% 3.19/0.98  fof(f5,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f59,plain,(
% 3.19/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f5])).
% 3.19/0.98  
% 3.19/0.98  fof(f6,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f60,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f6])).
% 3.19/0.98  
% 3.19/0.98  fof(f7,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f61,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f7])).
% 3.19/0.98  
% 3.19/0.98  fof(f8,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f62,plain,(
% 3.19/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f8])).
% 3.19/0.98  
% 3.19/0.98  fof(f88,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f61,f62])).
% 3.19/0.98  
% 3.19/0.98  fof(f89,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f60,f88])).
% 3.19/0.98  
% 3.19/0.98  fof(f90,plain,(
% 3.19/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f59,f89])).
% 3.19/0.98  
% 3.19/0.98  fof(f91,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f58,f90])).
% 3.19/0.98  
% 3.19/0.98  fof(f92,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f57,f91])).
% 3.19/0.98  
% 3.19/0.98  fof(f93,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.19/0.98    inference(definition_unfolding,[],[f72,f92])).
% 3.19/0.98  
% 3.19/0.98  fof(f94,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.19/0.98    inference(definition_unfolding,[],[f55,f93])).
% 3.19/0.98  
% 3.19/0.98  fof(f96,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(definition_unfolding,[],[f68,f94])).
% 3.19/0.98  
% 3.19/0.98  fof(f74,plain,(
% 3.19/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f47])).
% 3.19/0.98  
% 3.19/0.98  fof(f2,axiom,(
% 3.19/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f56,plain,(
% 3.19/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f2])).
% 3.19/0.98  
% 3.19/0.98  fof(f10,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f30,plain,(
% 3.19/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f10])).
% 3.19/0.98  
% 3.19/0.98  fof(f64,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f30])).
% 3.19/0.98  
% 3.19/0.98  fof(f95,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(definition_unfolding,[],[f64,f94])).
% 3.19/0.98  
% 3.19/0.98  fof(f23,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f39,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f23])).
% 3.19/0.98  
% 3.19/0.98  fof(f49,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f39])).
% 3.19/0.98  
% 3.19/0.98  fof(f80,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f83,plain,(
% 3.19/0.98    l1_pre_topc(sK0)),
% 3.19/0.98    inference(cnf_transformation,[],[f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f22,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f38,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f22])).
% 3.19/0.98  
% 3.19/0.98  fof(f48,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(nnf_transformation,[],[f38])).
% 3.19/0.98  
% 3.19/0.98  fof(f77,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f48])).
% 3.19/0.98  
% 3.19/0.98  fof(f78,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f48])).
% 3.19/0.98  
% 3.19/0.98  fof(f79,plain,(
% 3.19/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f24,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f40,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f24])).
% 3.19/0.98  
% 3.19/0.98  fof(f41,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f40])).
% 3.19/0.98  
% 3.19/0.98  fof(f81,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f41])).
% 3.19/0.98  
% 3.19/0.98  fof(f86,plain,(
% 3.19/0.98    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 3.19/0.98    inference(cnf_transformation,[],[f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f11,axiom,(
% 3.19/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f65,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f11])).
% 3.19/0.98  
% 3.19/0.98  fof(f9,axiom,(
% 3.19/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f63,plain,(
% 3.19/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.19/0.98    inference(cnf_transformation,[],[f9])).
% 3.19/0.98  
% 3.19/0.98  fof(f21,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f37,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f21])).
% 3.19/0.98  
% 3.19/0.98  fof(f76,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f37])).
% 3.19/0.98  
% 3.19/0.98  fof(f20,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f28,plain,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.19/0.98    inference(pure_predicate_removal,[],[f20])).
% 3.19/0.98  
% 3.19/0.98  fof(f35,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f28])).
% 3.19/0.98  
% 3.19/0.98  fof(f36,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f35])).
% 3.19/0.98  
% 3.19/0.98  fof(f75,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f36])).
% 3.19/0.98  
% 3.19/0.98  fof(f85,plain,(
% 3.19/0.98    v4_pre_topc(sK1,sK0)),
% 3.19/0.98    inference(cnf_transformation,[],[f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f25,axiom,(
% 3.19/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f42,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f25])).
% 3.19/0.98  
% 3.19/0.98  fof(f43,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.19/0.98    inference(flattening,[],[f42])).
% 3.19/0.98  
% 3.19/0.98  fof(f82,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f43])).
% 3.19/0.98  
% 3.19/0.98  fof(f87,plain,(
% 3.19/0.98    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 3.19/0.98    inference(cnf_transformation,[],[f54])).
% 3.19/0.98  
% 3.19/0.98  fof(f12,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f31,plain,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f12])).
% 3.19/0.98  
% 3.19/0.98  fof(f66,plain,(
% 3.19/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f31])).
% 3.19/0.98  
% 3.19/0.98  fof(f13,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f32,plain,(
% 3.19/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f13])).
% 3.19/0.98  
% 3.19/0.98  fof(f67,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f32])).
% 3.19/0.98  
% 3.19/0.98  fof(f15,axiom,(
% 3.19/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.19/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f34,plain,(
% 3.19/0.98    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f15])).
% 3.19/0.98  
% 3.19/0.98  fof(f46,plain,(
% 3.19/0.98    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.98    inference(nnf_transformation,[],[f34])).
% 3.19/0.98  
% 3.19/0.98  fof(f69,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f46])).
% 3.19/0.98  
% 3.19/0.98  cnf(c_23,negated_conjecture,
% 3.19/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.19/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1789,plain,
% 3.19/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_11,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1790,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.19/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2317,plain,
% 3.19/0.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_1789,c_1790]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_6,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.19/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_10,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_200,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_201,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.19/0.98      inference(renaming,[status(thm)],[c_200]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_244,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.19/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_201]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1784,plain,
% 3.19/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.19/0.98      | r1_tarski(X0,X2) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4039,plain,
% 3.19/0.98      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_2317,c_1784]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_0,plain,
% 3.19/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1794,plain,
% 3.19/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_241,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 3.19/0.98      inference(bin_hyper_res,[status(thm)],[c_2,c_201]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1787,plain,
% 3.19/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 3.19/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3270,plain,
% 3.19/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_1794,c_1787]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4157,plain,
% 3.19/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0) ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_4039,c_3270]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_16,plain,
% 3.19/0.98      ( v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_24,negated_conjecture,
% 3.19/0.98      ( l1_pre_topc(sK0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_418,plain,
% 3.19/0.98      ( v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_419,plain,
% 3.19/0.98      ( v2_tops_1(X0,sK0)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_418]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_15,plain,
% 3.19/0.98      ( ~ v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_433,plain,
% 3.19/0.98      ( ~ v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_434,plain,
% 3.19/0.98      ( ~ v2_tops_1(X0,sK0)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_433]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_510,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 3.19/0.98      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_419,c_434]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_512,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.19/0.98      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_510]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_952,plain,
% 3.19/0.98      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.19/0.98      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_23,c_512]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1777,plain,
% 3.19/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_26,plain,
% 3.19/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_511,plain,
% 3.19/0.98      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 3.19/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_513,plain,
% 3.19/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.19/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_511]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_14,plain,
% 3.19/0.98      ( v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_448,plain,
% 3.19/0.98      ( v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_449,plain,
% 3.19/0.98      ( v2_tops_1(X0,sK0)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_17,plain,
% 3.19/0.98      ( ~ v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(X1,X0))
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_403,plain,
% 3.19/0.98      ( ~ v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(X1,X0))
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_404,plain,
% 3.19/0.98      ( ~ v2_tops_1(X0,sK0)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_403]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_496,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(sK0,X0))
% 3.19/0.98      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_449,c_404]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_498,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.19/0.98      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_496]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_950,plain,
% 3.19/0.98      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.19/0.98      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_23,c_498]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1776,plain,
% 3.19/0.98      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_54,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.19/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_56,plain,
% 3.19/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top
% 3.19/0.98      | r1_tarski(sK1,sK1) = iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_54]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_18,plain,
% 3.19/0.98      ( ~ v3_tops_1(X0,X1)
% 3.19/0.98      | v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_21,negated_conjecture,
% 3.19/0.98      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_204,plain,
% 3.19/0.98      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_21]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_383,plain,
% 3.19/0.98      ( v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_tops_1(sK0,sK1) = sK1
% 3.19/0.98      | sK1 != X0
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_204]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_384,plain,
% 3.19/0.98      ( v2_tops_1(sK1,sK0)
% 3.19/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ l1_pre_topc(sK0)
% 3.19/0.98      | k2_tops_1(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_383]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_386,plain,
% 3.19/0.98      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_384,c_24,c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_536,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(sK0,X0))
% 3.19/0.98      | k2_tops_1(sK0,sK1) = sK1
% 3.19/0.98      | sK1 != X0
% 3.19/0.98      | sK0 != sK0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_386,c_404]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_537,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.19/0.98      | k2_tops_1(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_536]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_539,plain,
% 3.19/0.98      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_537,c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_541,plain,
% 3.19/0.98      ( k2_tops_1(sK0,sK1) = sK1
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1299,plain,( X0 = X0 ),theory(equality) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1324,plain,
% 3.19/0.98      ( sK1 = sK1 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_1299]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3,plain,
% 3.19/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1793,plain,
% 3.19/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1,plain,
% 3.19/0.98      ( k2_subset_1(X0) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1805,plain,
% 3.19/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.98      inference(light_normalisation,[status(thm)],[c_1793,c_1]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1892,plain,
% 3.19/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_1805]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1301,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.19/0.98      theory(equality) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1936,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | r1_tarski(X2,k2_tops_1(sK0,X2))
% 3.19/0.98      | X2 != X0
% 3.19/0.98      | k2_tops_1(sK0,X2) != X1 ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_1301]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1937,plain,
% 3.19/0.98      ( X0 != X1
% 3.19/0.98      | k2_tops_1(sK0,X0) != X2
% 3.19/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.19/0.98      | r1_tarski(X0,k2_tops_1(sK0,X0)) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1939,plain,
% 3.19/0.98      ( k2_tops_1(sK0,sK1) != sK1
% 3.19/0.98      | sK1 != sK1
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 3.19/0.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2015,plain,
% 3.19/0.98      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1776,c_56,c_541,c_1324,c_1892,c_1939]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2508,plain,
% 3.19/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1777,c_26,c_56,c_513,c_541,c_1324,c_1892,c_1939]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_13,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_463,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_464,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_463]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1782,plain,
% 3.19/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 3.19/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1933,plain,
% 3.19/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_1789,c_1782]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_12,plain,
% 3.19/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_22,negated_conjecture,
% 3.19/0.98      ( v4_pre_topc(sK1,sK0) ),
% 3.19/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_359,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | k2_pre_topc(X1,X0) = X0
% 3.19/0.98      | sK1 != X0
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_360,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ l1_pre_topc(sK0)
% 3.19/0.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_359]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_362,plain,
% 3.19/0.98      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_360,c_24,c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1934,plain,
% 3.19/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.19/0.98      inference(light_normalisation,[status(thm)],[c_1933,c_362]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2511,plain,
% 3.19/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 3.19/0.98      inference(demodulation,[status(thm)],[c_2508,c_1934]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4235,plain,
% 3.19/0.98      ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
% 3.19/0.98      inference(demodulation,[status(thm)],[c_4157,c_2511]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_19,plain,
% 3.19/0.98      ( v3_tops_1(X0,X1)
% 3.19/0.98      | ~ v2_tops_1(X0,X1)
% 3.19/0.98      | ~ v4_pre_topc(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1) ),
% 3.19/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_345,plain,
% 3.19/0.98      ( v3_tops_1(X0,X1)
% 3.19/0.98      | ~ v2_tops_1(X0,X1)
% 3.19/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.98      | ~ l1_pre_topc(X1)
% 3.19/0.98      | sK1 != X0
% 3.19/0.98      | sK0 != X1 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_346,plain,
% 3.19/0.98      ( v3_tops_1(sK1,sK0)
% 3.19/0.98      | ~ v2_tops_1(sK1,sK0)
% 3.19/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ l1_pre_topc(sK0) ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_345]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_348,plain,
% 3.19/0.98      ( v3_tops_1(sK1,sK0) | ~ v2_tops_1(sK1,sK0) ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_346,c_24,c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_20,negated_conjecture,
% 3.19/0.98      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_202,plain,
% 3.19/0.98      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_20]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_371,plain,
% 3.19/0.98      ( ~ v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(resolution,[status(thm)],[c_348,c_202]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_561,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 3.19/0.98      | k2_tops_1(sK0,sK1) != sK1
% 3.19/0.98      | sK1 != X0
% 3.19/0.98      | sK0 != sK0 ),
% 3.19/0.98      inference(resolution_lifted,[status(thm)],[c_371,c_419]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_562,plain,
% 3.19/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.19/0.98      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.19/0.98      | k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(unflattening,[status(thm)],[c_561]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_564,plain,
% 3.19/0.98      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_562,c_23]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_946,plain,
% 3.19/0.98      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(prop_impl,[status(thm)],[c_23,c_562]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1778,plain,
% 3.19/0.98      ( k2_tops_1(sK0,sK1) != sK1
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_566,plain,
% 3.19/0.98      ( k2_tops_1(sK0,sK1) != sK1
% 3.19/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2605,plain,
% 3.19/0.98      ( k2_tops_1(sK0,sK1) != sK1 ),
% 3.19/0.98      inference(global_propositional_subsumption,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_1778,c_56,c_541,c_566,c_1324,c_1892,c_1939]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4239,plain,
% 3.19/0.98      ( k3_subset_1(sK1,k1_xboole_0) != sK1 ),
% 3.19/0.98      inference(demodulation,[status(thm)],[c_4235,c_2605]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_4,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.19/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_242,plain,
% 3.19/0.98      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 3.19/0.98      | ~ r1_tarski(X1,X0) ),
% 3.19/0.98      inference(bin_hyper_res,[status(thm)],[c_4,c_201]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1786,plain,
% 3.19/0.98      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 3.19/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3137,plain,
% 3.19/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.19/0.98      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_1786,c_1790]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_5,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_243,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.19/0.98      inference(bin_hyper_res,[status(thm)],[c_5,c_201]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1785,plain,
% 3.19/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.19/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_2955,plain,
% 3.19/0.98      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_1794,c_1785]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_8,plain,
% 3.19/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.98      | ~ r1_tarski(k3_subset_1(X1,X0),X0)
% 3.19/0.98      | k2_subset_1(X1) = X0 ),
% 3.19/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_245,plain,
% 3.19/0.98      ( ~ r1_tarski(X0,X1)
% 3.19/0.98      | ~ r1_tarski(k3_subset_1(X1,X0),X0)
% 3.19/0.98      | k2_subset_1(X1) = X0 ),
% 3.19/0.98      inference(bin_hyper_res,[status(thm)],[c_8,c_201]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1783,plain,
% 3.19/0.98      ( k2_subset_1(X0) = X1
% 3.19/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.19/0.98      | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_1843,plain,
% 3.19/0.98      ( X0 = X1
% 3.19/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.19/0.98      | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top ),
% 3.19/0.98      inference(demodulation,[status(thm)],[c_1783,c_1]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3066,plain,
% 3.19/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0
% 3.19/0.98      | r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) != iProver_top
% 3.19/0.98      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_2955,c_1843]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3904,plain,
% 3.19/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0
% 3.19/0.98      | r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) != iProver_top ),
% 3.19/0.98      inference(forward_subsumption_resolution,
% 3.19/0.98                [status(thm)],
% 3.19/0.98                [c_3066,c_1794]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3908,plain,
% 3.19/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0
% 3.19/0.98      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.19/0.98      inference(superposition,[status(thm)],[c_3137,c_3904]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_3917,plain,
% 3.19/0.98      ( k3_subset_1(sK1,k1_xboole_0) = sK1
% 3.19/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_3908]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_85,plain,
% 3.19/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.19/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(c_87,plain,
% 3.19/0.98      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.19/0.98      inference(instantiation,[status(thm)],[c_85]) ).
% 3.19/0.98  
% 3.19/0.98  cnf(contradiction,plain,
% 3.19/0.98      ( $false ),
% 3.19/0.98      inference(minisat,[status(thm)],[c_4239,c_3917,c_87]) ).
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  ------                               Statistics
% 3.19/0.98  
% 3.19/0.98  ------ General
% 3.19/0.98  
% 3.19/0.98  abstr_ref_over_cycles:                  0
% 3.19/0.98  abstr_ref_under_cycles:                 0
% 3.19/0.98  gc_basic_clause_elim:                   0
% 3.19/0.98  forced_gc_time:                         0
% 3.19/0.98  parsing_time:                           0.01
% 3.19/0.98  unif_index_cands_time:                  0.
% 3.19/0.98  unif_index_add_time:                    0.
% 3.19/0.98  orderings_time:                         0.
% 3.19/0.98  out_proof_time:                         0.01
% 3.19/0.98  total_time:                             0.149
% 3.19/0.98  num_of_symbols:                         51
% 3.19/0.98  num_of_terms:                           3411
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing
% 3.19/0.98  
% 3.19/0.98  num_of_splits:                          0
% 3.19/0.98  num_of_split_atoms:                     0
% 3.19/0.98  num_of_reused_defs:                     0
% 3.19/0.98  num_eq_ax_congr_red:                    39
% 3.19/0.98  num_of_sem_filtered_clauses:            1
% 3.19/0.98  num_of_subtypes:                        0
% 3.19/0.98  monotx_restored_types:                  0
% 3.19/0.98  sat_num_of_epr_types:                   0
% 3.19/0.98  sat_num_of_non_cyclic_types:            0
% 3.19/0.98  sat_guarded_non_collapsed_types:        0
% 3.19/0.98  num_pure_diseq_elim:                    0
% 3.19/0.98  simp_replaced_by:                       0
% 3.19/0.98  res_preprocessed:                       115
% 3.19/0.98  prep_upred:                             0
% 3.19/0.98  prep_unflattend:                        55
% 3.19/0.98  smt_new_axioms:                         0
% 3.19/0.98  pred_elim_cands:                        2
% 3.19/0.98  pred_elim:                              4
% 3.19/0.98  pred_elim_cl:                           4
% 3.19/0.98  pred_elim_cycles:                       6
% 3.19/0.98  merged_defs:                            22
% 3.19/0.98  merged_defs_ncl:                        0
% 3.19/0.98  bin_hyper_res:                          27
% 3.19/0.98  prep_cycles:                            4
% 3.19/0.98  pred_elim_time:                         0.014
% 3.19/0.98  splitting_time:                         0.
% 3.19/0.98  sem_filter_time:                        0.
% 3.19/0.98  monotx_time:                            0.
% 3.19/0.98  subtype_inf_time:                       0.
% 3.19/0.98  
% 3.19/0.98  ------ Problem properties
% 3.19/0.98  
% 3.19/0.98  clauses:                                21
% 3.19/0.98  conjectures:                            1
% 3.19/0.98  epr:                                    1
% 3.19/0.98  horn:                                   20
% 3.19/0.98  ground:                                 6
% 3.19/0.98  unary:                                  7
% 3.19/0.98  binary:                                 11
% 3.19/0.98  lits:                                   38
% 3.19/0.98  lits_eq:                                13
% 3.19/0.98  fd_pure:                                0
% 3.19/0.98  fd_pseudo:                              0
% 3.19/0.98  fd_cond:                                0
% 3.19/0.98  fd_pseudo_cond:                         1
% 3.19/0.98  ac_symbols:                             0
% 3.19/0.98  
% 3.19/0.98  ------ Propositional Solver
% 3.19/0.98  
% 3.19/0.98  prop_solver_calls:                      29
% 3.19/0.98  prop_fast_solver_calls:                 749
% 3.19/0.98  smt_solver_calls:                       0
% 3.19/0.98  smt_fast_solver_calls:                  0
% 3.19/0.98  prop_num_of_clauses:                    1268
% 3.19/0.98  prop_preprocess_simplified:             4412
% 3.19/0.98  prop_fo_subsumed:                       20
% 3.19/0.98  prop_solver_time:                       0.
% 3.19/0.98  smt_solver_time:                        0.
% 3.19/0.98  smt_fast_solver_time:                   0.
% 3.19/0.98  prop_fast_solver_time:                  0.
% 3.19/0.98  prop_unsat_core_time:                   0.
% 3.19/0.98  
% 3.19/0.98  ------ QBF
% 3.19/0.98  
% 3.19/0.98  qbf_q_res:                              0
% 3.19/0.98  qbf_num_tautologies:                    0
% 3.19/0.98  qbf_prep_cycles:                        0
% 3.19/0.98  
% 3.19/0.98  ------ BMC1
% 3.19/0.98  
% 3.19/0.98  bmc1_current_bound:                     -1
% 3.19/0.98  bmc1_last_solved_bound:                 -1
% 3.19/0.98  bmc1_unsat_core_size:                   -1
% 3.19/0.98  bmc1_unsat_core_parents_size:           -1
% 3.19/0.98  bmc1_merge_next_fun:                    0
% 3.19/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation
% 3.19/0.98  
% 3.19/0.98  inst_num_of_clauses:                    405
% 3.19/0.98  inst_num_in_passive:                    43
% 3.19/0.98  inst_num_in_active:                     246
% 3.19/0.98  inst_num_in_unprocessed:                116
% 3.19/0.98  inst_num_of_loops:                      270
% 3.19/0.98  inst_num_of_learning_restarts:          0
% 3.19/0.98  inst_num_moves_active_passive:          18
% 3.19/0.98  inst_lit_activity:                      0
% 3.19/0.98  inst_lit_activity_moves:                0
% 3.19/0.98  inst_num_tautologies:                   0
% 3.19/0.98  inst_num_prop_implied:                  0
% 3.19/0.98  inst_num_existing_simplified:           0
% 3.19/0.98  inst_num_eq_res_simplified:             0
% 3.19/0.98  inst_num_child_elim:                    0
% 3.19/0.98  inst_num_of_dismatching_blockings:      90
% 3.19/0.98  inst_num_of_non_proper_insts:           503
% 3.19/0.98  inst_num_of_duplicates:                 0
% 3.19/0.98  inst_inst_num_from_inst_to_res:         0
% 3.19/0.98  inst_dismatching_checking_time:         0.
% 3.19/0.98  
% 3.19/0.98  ------ Resolution
% 3.19/0.98  
% 3.19/0.98  res_num_of_clauses:                     0
% 3.19/0.98  res_num_in_passive:                     0
% 3.19/0.98  res_num_in_active:                      0
% 3.19/0.98  res_num_of_loops:                       119
% 3.19/0.98  res_forward_subset_subsumed:            42
% 3.19/0.98  res_backward_subset_subsumed:           2
% 3.19/0.98  res_forward_subsumed:                   2
% 3.19/0.98  res_backward_subsumed:                  0
% 3.19/0.98  res_forward_subsumption_resolution:     1
% 3.19/0.98  res_backward_subsumption_resolution:    0
% 3.19/0.98  res_clause_to_clause_subsumption:       296
% 3.19/0.98  res_orphan_elimination:                 0
% 3.19/0.98  res_tautology_del:                      106
% 3.19/0.98  res_num_eq_res_simplified:              0
% 3.19/0.98  res_num_sel_changes:                    0
% 3.19/0.98  res_moves_from_active_to_pass:          0
% 3.19/0.98  
% 3.19/0.98  ------ Superposition
% 3.19/0.98  
% 3.19/0.98  sup_time_total:                         0.
% 3.19/0.98  sup_time_generating:                    0.
% 3.19/0.98  sup_time_sim_full:                      0.
% 3.19/0.98  sup_time_sim_immed:                     0.
% 3.19/0.98  
% 3.19/0.98  sup_num_of_clauses:                     67
% 3.19/0.98  sup_num_in_active:                      45
% 3.19/0.98  sup_num_in_passive:                     22
% 3.19/0.98  sup_num_of_loops:                       53
% 3.19/0.98  sup_fw_superposition:                   54
% 3.19/0.98  sup_bw_superposition:                   28
% 3.19/0.98  sup_immediate_simplified:               20
% 3.19/0.98  sup_given_eliminated:                   1
% 3.19/0.98  comparisons_done:                       0
% 3.19/0.98  comparisons_avoided:                    0
% 3.19/0.98  
% 3.19/0.98  ------ Simplifications
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  sim_fw_subset_subsumed:                 9
% 3.19/0.98  sim_bw_subset_subsumed:                 0
% 3.19/0.98  sim_fw_subsumed:                        3
% 3.19/0.98  sim_bw_subsumed:                        0
% 3.19/0.98  sim_fw_subsumption_res:                 1
% 3.19/0.98  sim_bw_subsumption_res:                 0
% 3.19/0.98  sim_tautology_del:                      2
% 3.19/0.98  sim_eq_tautology_del:                   7
% 3.19/0.98  sim_eq_res_simp:                        0
% 3.19/0.98  sim_fw_demodulated:                     3
% 3.19/0.98  sim_bw_demodulated:                     9
% 3.19/0.98  sim_light_normalised:                   7
% 3.19/0.98  sim_joinable_taut:                      0
% 3.19/0.98  sim_joinable_simp:                      0
% 3.19/0.98  sim_ac_normalised:                      0
% 3.19/0.98  sim_smt_subsumption:                    0
% 3.19/0.98  
%------------------------------------------------------------------------------
