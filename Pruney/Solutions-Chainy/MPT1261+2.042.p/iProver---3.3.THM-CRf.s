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
% DateTime   : Thu Dec  3 12:14:30 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  148 (1380 expanded)
%              Number of clauses        :   66 ( 292 expanded)
%              Number of leaves         :   24 ( 342 expanded)
%              Depth                    :   21
%              Number of atoms          :  339 (5143 expanded)
%              Number of equality atoms :  167 (1812 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f77])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f81])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f82])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f49,f79,f79])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f82])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_657,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_657,c_2])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_654,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2380,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_667,c_654])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_644,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2379,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_644,c_654])).

cnf(c_3853,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_2380,c_2379])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_645,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_651,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2401,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_651])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3091,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2401,c_20])).

cnf(c_3092,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3091])).

cnf(c_3097,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_645,c_3092])).

cnf(c_4331,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3853,c_3097])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6041,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4331,c_656])).

cnf(c_9423,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6041,c_667])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9425,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9423,c_653])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_658,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9451,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_9425,c_658])).

cnf(c_1,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_648,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2174,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_648])).

cnf(c_896,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3330,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_17,c_16,c_896])).

cnf(c_3334,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_656])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_836,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_837,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_4688,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3334,c_20,c_21,c_837])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_655,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4699,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_655])).

cnf(c_11733,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_644,c_4699])).

cnf(c_11769,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_1,c_11733])).

cnf(c_2910,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_655])).

cnf(c_4700,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4688,c_2910])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_647,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1169,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_647])).

cnf(c_889,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1719,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_17,c_16,c_889])).

cnf(c_4702,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4700,c_1719])).

cnf(c_11771,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11769,c_4702])).

cnf(c_12058,plain,
    ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11771,c_11733])).

cnf(c_23056,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_9451,c_12058])).

cnf(c_23067,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_23056,c_3330])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10881,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23067,c_23056,c_10881,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:54:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.81/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.48  
% 7.81/1.48  ------  iProver source info
% 7.81/1.48  
% 7.81/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.48  git: non_committed_changes: false
% 7.81/1.48  git: last_make_outside_of_git: false
% 7.81/1.48  
% 7.81/1.48  ------ 
% 7.81/1.48  ------ Parsing...
% 7.81/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.48  
% 7.81/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.48  ------ Proving...
% 7.81/1.48  ------ Problem Properties 
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  clauses                                 19
% 7.81/1.48  conjectures                             5
% 7.81/1.48  EPR                                     2
% 7.81/1.48  Horn                                    18
% 7.81/1.48  unary                                   6
% 7.81/1.48  binary                                  6
% 7.81/1.48  lits                                    43
% 7.81/1.48  lits eq                                 11
% 7.81/1.48  fd_pure                                 0
% 7.81/1.48  fd_pseudo                               0
% 7.81/1.48  fd_cond                                 0
% 7.81/1.48  fd_pseudo_cond                          0
% 7.81/1.48  AC symbols                              0
% 7.81/1.48  
% 7.81/1.48  ------ Input Options Time Limit: Unbounded
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ 
% 7.81/1.48  Current options:
% 7.81/1.48  ------ 
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  ------ Proving...
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  % SZS status Theorem for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  fof(f12,axiom,(
% 7.81/1.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f58,plain,(
% 7.81/1.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f12])).
% 7.81/1.48  
% 7.81/1.48  fof(f11,axiom,(
% 7.81/1.48    ! [X0] : k2_subset_1(X0) = X0),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f57,plain,(
% 7.81/1.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.81/1.48    inference(cnf_transformation,[],[f11])).
% 7.81/1.48  
% 7.81/1.48  fof(f15,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f30,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f15])).
% 7.81/1.48  
% 7.81/1.48  fof(f61,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f30])).
% 7.81/1.48  
% 7.81/1.48  fof(f1,axiom,(
% 7.81/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f47,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f1])).
% 7.81/1.48  
% 7.81/1.48  fof(f16,axiom,(
% 7.81/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f62,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f16])).
% 7.81/1.48  
% 7.81/1.48  fof(f4,axiom,(
% 7.81/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f50,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f4])).
% 7.81/1.48  
% 7.81/1.48  fof(f5,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f51,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f5])).
% 7.81/1.48  
% 7.81/1.48  fof(f6,axiom,(
% 7.81/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f52,plain,(
% 7.81/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f6])).
% 7.81/1.48  
% 7.81/1.48  fof(f7,axiom,(
% 7.81/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f53,plain,(
% 7.81/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f7])).
% 7.81/1.48  
% 7.81/1.48  fof(f8,axiom,(
% 7.81/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f54,plain,(
% 7.81/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f8])).
% 7.81/1.48  
% 7.81/1.48  fof(f9,axiom,(
% 7.81/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f55,plain,(
% 7.81/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f9])).
% 7.81/1.48  
% 7.81/1.48  fof(f75,plain,(
% 7.81/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f54,f55])).
% 7.81/1.48  
% 7.81/1.48  fof(f76,plain,(
% 7.81/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f53,f75])).
% 7.81/1.48  
% 7.81/1.48  fof(f77,plain,(
% 7.81/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f52,f76])).
% 7.81/1.48  
% 7.81/1.48  fof(f78,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f51,f77])).
% 7.81/1.48  
% 7.81/1.48  fof(f79,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f50,f78])).
% 7.81/1.48  
% 7.81/1.48  fof(f80,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.81/1.48    inference(definition_unfolding,[],[f62,f79])).
% 7.81/1.48  
% 7.81/1.48  fof(f81,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.81/1.48    inference(definition_unfolding,[],[f47,f80])).
% 7.81/1.48  
% 7.81/1.48  fof(f86,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.48    inference(definition_unfolding,[],[f61,f81])).
% 7.81/1.48  
% 7.81/1.48  fof(f23,conjecture,(
% 7.81/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f24,negated_conjecture,(
% 7.81/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.81/1.48    inference(negated_conjecture,[],[f23])).
% 7.81/1.48  
% 7.81/1.48  fof(f40,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f24])).
% 7.81/1.48  
% 7.81/1.48  fof(f41,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f40])).
% 7.81/1.48  
% 7.81/1.48  fof(f42,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.48    inference(nnf_transformation,[],[f41])).
% 7.81/1.48  
% 7.81/1.48  fof(f43,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f42])).
% 7.81/1.48  
% 7.81/1.48  fof(f45,plain,(
% 7.81/1.48    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f44,plain,(
% 7.81/1.48    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.81/1.48    introduced(choice_axiom,[])).
% 7.81/1.48  
% 7.81/1.48  fof(f46,plain,(
% 7.81/1.48    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.81/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 7.81/1.48  
% 7.81/1.48  fof(f72,plain,(
% 7.81/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.81/1.48    inference(cnf_transformation,[],[f46])).
% 7.81/1.48  
% 7.81/1.48  fof(f73,plain,(
% 7.81/1.48    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.81/1.48    inference(cnf_transformation,[],[f46])).
% 7.81/1.48  
% 7.81/1.48  fof(f18,axiom,(
% 7.81/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f32,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f18])).
% 7.81/1.48  
% 7.81/1.48  fof(f33,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f32])).
% 7.81/1.48  
% 7.81/1.48  fof(f64,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f33])).
% 7.81/1.48  
% 7.81/1.48  fof(f71,plain,(
% 7.81/1.48    l1_pre_topc(sK0)),
% 7.81/1.48    inference(cnf_transformation,[],[f46])).
% 7.81/1.48  
% 7.81/1.48  fof(f13,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f27,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f13])).
% 7.81/1.48  
% 7.81/1.48  fof(f59,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f27])).
% 7.81/1.48  
% 7.81/1.48  fof(f17,axiom,(
% 7.81/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f25,plain,(
% 7.81/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 7.81/1.48    inference(unused_predicate_definition_removal,[],[f17])).
% 7.81/1.48  
% 7.81/1.48  fof(f31,plain,(
% 7.81/1.48    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.81/1.48    inference(ennf_transformation,[],[f25])).
% 7.81/1.48  
% 7.81/1.48  fof(f63,plain,(
% 7.81/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f31])).
% 7.81/1.48  
% 7.81/1.48  fof(f2,axiom,(
% 7.81/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f26,plain,(
% 7.81/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.81/1.48    inference(ennf_transformation,[],[f2])).
% 7.81/1.48  
% 7.81/1.48  fof(f48,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f26])).
% 7.81/1.48  
% 7.81/1.48  fof(f10,axiom,(
% 7.81/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f56,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f10])).
% 7.81/1.48  
% 7.81/1.48  fof(f82,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.81/1.48    inference(definition_unfolding,[],[f56,f79])).
% 7.81/1.48  
% 7.81/1.48  fof(f83,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f48,f82])).
% 7.81/1.48  
% 7.81/1.48  fof(f3,axiom,(
% 7.81/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f49,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f3])).
% 7.81/1.48  
% 7.81/1.48  fof(f84,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 7.81/1.48    inference(definition_unfolding,[],[f49,f79,f79])).
% 7.81/1.48  
% 7.81/1.48  fof(f21,axiom,(
% 7.81/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f38,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f21])).
% 7.81/1.48  
% 7.81/1.48  fof(f68,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f38])).
% 7.81/1.48  
% 7.81/1.48  fof(f19,axiom,(
% 7.81/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f34,plain,(
% 7.81/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.81/1.48    inference(ennf_transformation,[],[f19])).
% 7.81/1.48  
% 7.81/1.48  fof(f35,plain,(
% 7.81/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.81/1.48    inference(flattening,[],[f34])).
% 7.81/1.48  
% 7.81/1.48  fof(f66,plain,(
% 7.81/1.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f35])).
% 7.81/1.48  
% 7.81/1.48  fof(f14,axiom,(
% 7.81/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f28,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.81/1.48    inference(ennf_transformation,[],[f14])).
% 7.81/1.48  
% 7.81/1.48  fof(f29,plain,(
% 7.81/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.48    inference(flattening,[],[f28])).
% 7.81/1.48  
% 7.81/1.48  fof(f60,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.48    inference(cnf_transformation,[],[f29])).
% 7.81/1.48  
% 7.81/1.48  fof(f85,plain,(
% 7.81/1.48    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.48    inference(definition_unfolding,[],[f60,f82])).
% 7.81/1.48  
% 7.81/1.48  fof(f22,axiom,(
% 7.81/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.81/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.48  
% 7.81/1.48  fof(f39,plain,(
% 7.81/1.48    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.81/1.48    inference(ennf_transformation,[],[f22])).
% 7.81/1.48  
% 7.81/1.48  fof(f69,plain,(
% 7.81/1.48    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f39])).
% 7.81/1.48  
% 7.81/1.48  fof(f65,plain,(
% 7.81/1.48    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.81/1.48    inference(cnf_transformation,[],[f33])).
% 7.81/1.48  
% 7.81/1.48  fof(f74,plain,(
% 7.81/1.48    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.81/1.48    inference(cnf_transformation,[],[f46])).
% 7.81/1.48  
% 7.81/1.48  fof(f70,plain,(
% 7.81/1.48    v2_pre_topc(sK0)),
% 7.81/1.48    inference(cnf_transformation,[],[f46])).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3,plain,
% 7.81/1.48      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.81/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_657,plain,
% 7.81/1.48      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2,plain,
% 7.81/1.48      ( k2_subset_1(X0) = X0 ),
% 7.81/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_667,plain,
% 7.81/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_657,c_2]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.48      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.81/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_654,plain,
% 7.81/1.48      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2380,plain,
% 7.81/1.48      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_667,c_654]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_16,negated_conjecture,
% 7.81/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.81/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_644,plain,
% 7.81/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2379,plain,
% 7.81/1.48      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_644,c_654]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3853,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_2380,c_2379]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_15,negated_conjecture,
% 7.81/1.48      ( v4_pre_topc(sK1,sK0)
% 7.81/1.48      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_645,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.48      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9,plain,
% 7.81/1.48      ( ~ v4_pre_topc(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | k2_pre_topc(X1,X0) = X0 ),
% 7.81/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_651,plain,
% 7.81/1.48      ( k2_pre_topc(X0,X1) = X1
% 7.81/1.48      | v4_pre_topc(X1,X0) != iProver_top
% 7.81/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.81/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2401,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.48      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_644,c_651]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_17,negated_conjecture,
% 7.81/1.48      ( l1_pre_topc(sK0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_20,plain,
% 7.81/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3091,plain,
% 7.81/1.48      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.81/1.48      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_2401,c_20]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3092,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.48      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.81/1.48      inference(renaming,[status(thm)],[c_3091]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3097,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.48      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_645,c_3092]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4331,plain,
% 7.81/1.48      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.48      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_3853,c_3097]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.48      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.81/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_656,plain,
% 7.81/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.81/1.48      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_6041,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.48      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top
% 7.81/1.48      | m1_subset_1(sK1,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4331,c_656]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9423,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.48      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.48      inference(forward_subsumption_resolution,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_6041,c_667]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_7,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_653,plain,
% 7.81/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.81/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9425,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.48      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_9423,c_653]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_0,plain,
% 7.81/1.48      ( ~ r1_tarski(X0,X1)
% 7.81/1.48      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 7.81/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_658,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 7.81/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_9451,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1
% 7.81/1.48      | k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = sK1 ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_9425,c_658]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1,plain,
% 7.81/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_12,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_648,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.81/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.81/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2174,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_644,c_648]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_896,plain,
% 7.81/1.48      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3330,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_2174,c_17,c_16,c_896]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_3334,plain,
% 7.81/1.48      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.81/1.48      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_3330,c_656]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_21,plain,
% 7.81/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_10,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.48      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.48      | ~ l1_pre_topc(X1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_836,plain,
% 7.81/1.48      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.48      | ~ l1_pre_topc(sK0) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_837,plain,
% 7.81/1.48      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.81/1.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4688,plain,
% 7.81/1.48      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_3334,c_20,c_21,c_837]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_5,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.81/1.48      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 7.81/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_655,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.81/1.48      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4699,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4688,c_655]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_11733,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_644,c_4699]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_11769,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_1,c_11733]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_2910,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 7.81/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_644,c_655]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4700,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_4688,c_2910]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_13,plain,
% 7.81/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_647,plain,
% 7.81/1.48      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.81/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.81/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.81/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1169,plain,
% 7.81/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.81/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.81/1.48      inference(superposition,[status(thm)],[c_644,c_647]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_889,plain,
% 7.81/1.48      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_1719,plain,
% 7.81/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.48      inference(global_propositional_subsumption,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_1169,c_17,c_16,c_889]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_4702,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_4700,c_1719]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_11771,plain,
% 7.81/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.48      inference(light_normalisation,[status(thm)],[c_11769,c_4702]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_12058,plain,
% 7.81/1.48      ( k3_tarski(k6_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_11771,c_11733]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_23056,plain,
% 7.81/1.48      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_9451,c_12058]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_23067,plain,
% 7.81/1.48      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.81/1.48      inference(demodulation,[status(thm)],[c_23056,c_3330]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_8,plain,
% 7.81/1.48      ( v4_pre_topc(X0,X1)
% 7.81/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.81/1.48      | ~ l1_pre_topc(X1)
% 7.81/1.48      | ~ v2_pre_topc(X1)
% 7.81/1.48      | k2_pre_topc(X1,X0) != X0 ),
% 7.81/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_10881,plain,
% 7.81/1.48      ( v4_pre_topc(sK1,sK0)
% 7.81/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.81/1.48      | ~ l1_pre_topc(sK0)
% 7.81/1.48      | ~ v2_pre_topc(sK0)
% 7.81/1.48      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.81/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_14,negated_conjecture,
% 7.81/1.48      ( ~ v4_pre_topc(sK1,sK0)
% 7.81/1.48      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.81/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(c_18,negated_conjecture,
% 7.81/1.48      ( v2_pre_topc(sK0) ),
% 7.81/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.81/1.48  
% 7.81/1.48  cnf(contradiction,plain,
% 7.81/1.48      ( $false ),
% 7.81/1.48      inference(minisat,
% 7.81/1.48                [status(thm)],
% 7.81/1.48                [c_23067,c_23056,c_10881,c_14,c_16,c_17,c_18]) ).
% 7.81/1.48  
% 7.81/1.48  
% 7.81/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.48  
% 7.81/1.48  ------                               Statistics
% 7.81/1.48  
% 7.81/1.48  ------ Selected
% 7.81/1.48  
% 7.81/1.48  total_time:                             0.759
% 7.81/1.48  
%------------------------------------------------------------------------------
