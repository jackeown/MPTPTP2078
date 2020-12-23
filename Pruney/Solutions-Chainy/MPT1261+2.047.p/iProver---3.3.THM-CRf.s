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
% DateTime   : Thu Dec  3 12:14:31 EST 2020

% Result     : Theorem 35.45s
% Output     : CNFRefutation 35.45s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 724 expanded)
%              Number of clauses        :   94 ( 237 expanded)
%              Number of leaves         :   23 ( 160 expanded)
%              Depth                    :   21
%              Number of atoms          :  388 (2507 expanded)
%              Number of equality atoms :  190 ( 854 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) != k2_tops_1(X0,sK2)
          | ~ v4_pre_topc(sK2,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) = k2_tops_1(X0,sK2)
          | v4_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
          ( ( k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) != k2_tops_1(sK1,X1)
            | ~ v4_pre_topc(X1,sK1) )
          & ( k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) = k2_tops_1(sK1,X1)
            | v4_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
      | ~ v4_pre_topc(sK2,sK1) )
    & ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
      | v4_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f53,f55,f54])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f64])).

fof(f91,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f70,f64])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f71,f64,f64])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1056,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1066,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3757,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1066])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1062,plain,
    ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21679,plain,
    ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1062])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_22013,plain,
    ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21679,c_33,c_32,c_1396])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1063,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22020,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_22013,c_1063])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1333,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1334,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_22382,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22020,c_36,c_37,c_1334])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_208])).

cnf(c_1050,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_127508,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,sK2)) = k2_xboole_0(X0,k2_tops_1(sK1,sK2))
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22382,c_1050])).

cnf(c_131005,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3757,c_127508])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1061,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26759,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1061])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_26957,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26759,c_33,c_32,c_1432])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_269,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_208])).

cnf(c_1049,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_4019,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_3757,c_1049])).

cnf(c_31,negated_conjecture,
    ( v4_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1057,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4298,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4019,c_1057])).

cnf(c_28,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1060,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2591,plain,
    ( v4_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1060])).

cnf(c_2911,plain,
    ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_36])).

cnf(c_2912,plain,
    ( v4_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2911])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1070,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3609,plain,
    ( k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_1070])).

cnf(c_4852,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) = k2_tops_1(sK1,sK2)
    | k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_4298,c_3609])).

cnf(c_11,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1068,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4856,plain,
    ( k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
    | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4852,c_1068])).

cnf(c_5968,plain,
    ( k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4856,c_1070])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5978,plain,
    ( k2_xboole_0(sK2,k5_xboole_0(k2_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))) = k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_5968,c_12])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2655,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2677,plain,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2655,c_7])).

cnf(c_5990,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(k2_tops_1(sK1,sK2),k1_xboole_0)) = k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_5978,c_2677])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1069,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3606,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1069,c_1070])).

cnf(c_14,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1531,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_14,c_20])).

cnf(c_1909,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1531,c_20])).

cnf(c_32181,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3606,c_1909])).

cnf(c_38925,plain,
    ( k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5990,c_8,c_32181])).

cnf(c_131034,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_131005,c_26957,c_38925])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1059,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26722,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1059])).

cnf(c_2164,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1068])).

cnf(c_2274,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2164,c_1049])).

cnf(c_7301,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_2274,c_4019])).

cnf(c_26730,plain,
    ( k7_subset_1(sK2,sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26722,c_7301])).

cnf(c_27051,plain,
    ( k7_subset_1(sK2,sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26730,c_36])).

cnf(c_7295,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2274,c_0])).

cnf(c_27065,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) = k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_27051,c_7295])).

cnf(c_27110,plain,
    ( k7_subset_1(sK2,sK2,k1_tops_1(sK1,sK2)) = k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_27065,c_2274])).

cnf(c_30,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK1)
    | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1058,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4299,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) != k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4019,c_1058])).

cnf(c_7305,plain,
    ( k7_subset_1(sK2,sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2274,c_4299])).

cnf(c_32334,plain,
    ( k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27110,c_7305])).

cnf(c_5977,plain,
    ( k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_5968,c_1909])).

cnf(c_23,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1429,plain,
    ( v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1430,plain,
    ( k2_pre_topc(sK1,sK2) != sK2
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_131034,c_32334,c_5977,c_1430,c_37,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.45/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.45/5.00  
% 35.45/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.45/5.00  
% 35.45/5.00  ------  iProver source info
% 35.45/5.00  
% 35.45/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.45/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.45/5.00  git: non_committed_changes: false
% 35.45/5.00  git: last_make_outside_of_git: false
% 35.45/5.00  
% 35.45/5.00  ------ 
% 35.45/5.00  ------ Parsing...
% 35.45/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.45/5.00  
% 35.45/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.45/5.00  
% 35.45/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.45/5.00  
% 35.45/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.45/5.00  ------ Proving...
% 35.45/5.00  ------ Problem Properties 
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  clauses                                 35
% 35.45/5.00  conjectures                             5
% 35.45/5.00  EPR                                     3
% 35.45/5.00  Horn                                    30
% 35.45/5.00  unary                                   12
% 35.45/5.00  binary                                  11
% 35.45/5.00  lits                                    75
% 35.45/5.00  lits eq                                 22
% 35.45/5.00  fd_pure                                 0
% 35.45/5.00  fd_pseudo                               0
% 35.45/5.00  fd_cond                                 0
% 35.45/5.00  fd_pseudo_cond                          3
% 35.45/5.00  AC symbols                              0
% 35.45/5.00  
% 35.45/5.00  ------ Input Options Time Limit: Unbounded
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  ------ 
% 35.45/5.00  Current options:
% 35.45/5.00  ------ 
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  ------ Proving...
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  % SZS status Theorem for theBenchmark.p
% 35.45/5.00  
% 35.45/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.45/5.00  
% 35.45/5.00  fof(f25,conjecture,(
% 35.45/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f26,negated_conjecture,(
% 35.45/5.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 35.45/5.00    inference(negated_conjecture,[],[f25])).
% 35.45/5.00  
% 35.45/5.00  fof(f44,plain,(
% 35.45/5.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 35.45/5.00    inference(ennf_transformation,[],[f26])).
% 35.45/5.00  
% 35.45/5.00  fof(f45,plain,(
% 35.45/5.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.45/5.00    inference(flattening,[],[f44])).
% 35.45/5.00  
% 35.45/5.00  fof(f52,plain,(
% 35.45/5.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.45/5.00    inference(nnf_transformation,[],[f45])).
% 35.45/5.00  
% 35.45/5.00  fof(f53,plain,(
% 35.45/5.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.45/5.00    inference(flattening,[],[f52])).
% 35.45/5.00  
% 35.45/5.00  fof(f55,plain,(
% 35.45/5.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) != k2_tops_1(X0,sK2) | ~v4_pre_topc(sK2,X0)) & (k7_subset_1(u1_struct_0(X0),sK2,k1_tops_1(X0,sK2)) = k2_tops_1(X0,sK2) | v4_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.45/5.00    introduced(choice_axiom,[])).
% 35.45/5.00  
% 35.45/5.00  fof(f54,plain,(
% 35.45/5.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) != k2_tops_1(sK1,X1) | ~v4_pre_topc(X1,sK1)) & (k7_subset_1(u1_struct_0(sK1),X1,k1_tops_1(sK1,X1)) = k2_tops_1(sK1,X1) | v4_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 35.45/5.00    introduced(choice_axiom,[])).
% 35.45/5.00  
% 35.45/5.00  fof(f56,plain,(
% 35.45/5.00    ((k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) | ~v4_pre_topc(sK2,sK1)) & (k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) | v4_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 35.45/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f53,f55,f54])).
% 35.45/5.00  
% 35.45/5.00  fof(f90,plain,(
% 35.45/5.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 35.45/5.00    inference(cnf_transformation,[],[f56])).
% 35.45/5.00  
% 35.45/5.00  fof(f18,axiom,(
% 35.45/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f51,plain,(
% 35.45/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.45/5.00    inference(nnf_transformation,[],[f18])).
% 35.45/5.00  
% 35.45/5.00  fof(f79,plain,(
% 35.45/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.45/5.00    inference(cnf_transformation,[],[f51])).
% 35.45/5.00  
% 35.45/5.00  fof(f21,axiom,(
% 35.45/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f39,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(ennf_transformation,[],[f21])).
% 35.45/5.00  
% 35.45/5.00  fof(f84,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f39])).
% 35.45/5.00  
% 35.45/5.00  fof(f89,plain,(
% 35.45/5.00    l1_pre_topc(sK1)),
% 35.45/5.00    inference(cnf_transformation,[],[f56])).
% 35.45/5.00  
% 35.45/5.00  fof(f20,axiom,(
% 35.45/5.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f37,plain,(
% 35.45/5.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 35.45/5.00    inference(ennf_transformation,[],[f20])).
% 35.45/5.00  
% 35.45/5.00  fof(f38,plain,(
% 35.45/5.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(flattening,[],[f37])).
% 35.45/5.00  
% 35.45/5.00  fof(f83,plain,(
% 35.45/5.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f38])).
% 35.45/5.00  
% 35.45/5.00  fof(f15,axiom,(
% 35.45/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f32,plain,(
% 35.45/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.45/5.00    inference(ennf_transformation,[],[f15])).
% 35.45/5.00  
% 35.45/5.00  fof(f33,plain,(
% 35.45/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.45/5.00    inference(flattening,[],[f32])).
% 35.45/5.00  
% 35.45/5.00  fof(f76,plain,(
% 35.45/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.45/5.00    inference(cnf_transformation,[],[f33])).
% 35.45/5.00  
% 35.45/5.00  fof(f80,plain,(
% 35.45/5.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f51])).
% 35.45/5.00  
% 35.45/5.00  fof(f22,axiom,(
% 35.45/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f40,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(ennf_transformation,[],[f22])).
% 35.45/5.00  
% 35.45/5.00  fof(f85,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f40])).
% 35.45/5.00  
% 35.45/5.00  fof(f16,axiom,(
% 35.45/5.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f34,plain,(
% 35.45/5.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.45/5.00    inference(ennf_transformation,[],[f16])).
% 35.45/5.00  
% 35.45/5.00  fof(f77,plain,(
% 35.45/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.45/5.00    inference(cnf_transformation,[],[f34])).
% 35.45/5.00  
% 35.45/5.00  fof(f3,axiom,(
% 35.45/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f64,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.45/5.00    inference(cnf_transformation,[],[f3])).
% 35.45/5.00  
% 35.45/5.00  fof(f104,plain,(
% 35.45/5.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.45/5.00    inference(definition_unfolding,[],[f77,f64])).
% 35.45/5.00  
% 35.45/5.00  fof(f91,plain,(
% 35.45/5.00    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) | v4_pre_topc(sK2,sK1)),
% 35.45/5.00    inference(cnf_transformation,[],[f56])).
% 35.45/5.00  
% 35.45/5.00  fof(f23,axiom,(
% 35.45/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f41,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(ennf_transformation,[],[f23])).
% 35.45/5.00  
% 35.45/5.00  fof(f42,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(flattening,[],[f41])).
% 35.45/5.00  
% 35.45/5.00  fof(f86,plain,(
% 35.45/5.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f42])).
% 35.45/5.00  
% 35.45/5.00  fof(f5,axiom,(
% 35.45/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f28,plain,(
% 35.45/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.45/5.00    inference(ennf_transformation,[],[f5])).
% 35.45/5.00  
% 35.45/5.00  fof(f66,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f28])).
% 35.45/5.00  
% 35.45/5.00  fof(f7,axiom,(
% 35.45/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f68,plain,(
% 35.45/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f7])).
% 35.45/5.00  
% 35.45/5.00  fof(f100,plain,(
% 35.45/5.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 35.45/5.00    inference(definition_unfolding,[],[f68,f64])).
% 35.45/5.00  
% 35.45/5.00  fof(f8,axiom,(
% 35.45/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f69,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.45/5.00    inference(cnf_transformation,[],[f8])).
% 35.45/5.00  
% 35.45/5.00  fof(f101,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 35.45/5.00    inference(definition_unfolding,[],[f69,f64])).
% 35.45/5.00  
% 35.45/5.00  fof(f9,axiom,(
% 35.45/5.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f70,plain,(
% 35.45/5.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.45/5.00    inference(cnf_transformation,[],[f9])).
% 35.45/5.00  
% 35.45/5.00  fof(f102,plain,(
% 35.45/5.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 35.45/5.00    inference(definition_unfolding,[],[f70,f64])).
% 35.45/5.00  
% 35.45/5.00  fof(f10,axiom,(
% 35.45/5.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f71,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f10])).
% 35.45/5.00  
% 35.45/5.00  fof(f93,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 35.45/5.00    inference(definition_unfolding,[],[f71,f64,f64])).
% 35.45/5.00  
% 35.45/5.00  fof(f2,axiom,(
% 35.45/5.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f27,plain,(
% 35.45/5.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 35.45/5.00    inference(rectify,[],[f2])).
% 35.45/5.00  
% 35.45/5.00  fof(f63,plain,(
% 35.45/5.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.45/5.00    inference(cnf_transformation,[],[f27])).
% 35.45/5.00  
% 35.45/5.00  fof(f4,axiom,(
% 35.45/5.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f65,plain,(
% 35.45/5.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.45/5.00    inference(cnf_transformation,[],[f4])).
% 35.45/5.00  
% 35.45/5.00  fof(f6,axiom,(
% 35.45/5.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f67,plain,(
% 35.45/5.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f6])).
% 35.45/5.00  
% 35.45/5.00  fof(f11,axiom,(
% 35.45/5.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f72,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f11])).
% 35.45/5.00  
% 35.45/5.00  fof(f17,axiom,(
% 35.45/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f78,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.45/5.00    inference(cnf_transformation,[],[f17])).
% 35.45/5.00  
% 35.45/5.00  fof(f24,axiom,(
% 35.45/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f43,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(ennf_transformation,[],[f24])).
% 35.45/5.00  
% 35.45/5.00  fof(f87,plain,(
% 35.45/5.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f43])).
% 35.45/5.00  
% 35.45/5.00  fof(f92,plain,(
% 35.45/5.00    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) | ~v4_pre_topc(sK2,sK1)),
% 35.45/5.00    inference(cnf_transformation,[],[f56])).
% 35.45/5.00  
% 35.45/5.00  fof(f19,axiom,(
% 35.45/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 35.45/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.45/5.00  
% 35.45/5.00  fof(f35,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(ennf_transformation,[],[f19])).
% 35.45/5.00  
% 35.45/5.00  fof(f36,plain,(
% 35.45/5.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.45/5.00    inference(flattening,[],[f35])).
% 35.45/5.00  
% 35.45/5.00  fof(f82,plain,(
% 35.45/5.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.45/5.00    inference(cnf_transformation,[],[f36])).
% 35.45/5.00  
% 35.45/5.00  fof(f88,plain,(
% 35.45/5.00    v2_pre_topc(sK1)),
% 35.45/5.00    inference(cnf_transformation,[],[f56])).
% 35.45/5.00  
% 35.45/5.00  cnf(c_32,negated_conjecture,
% 35.45/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 35.45/5.00      inference(cnf_transformation,[],[f90]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1056,plain,
% 35.45/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_22,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f79]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1066,plain,
% 35.45/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.45/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_3757,plain,
% 35.45/5.00      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1056,c_1066]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_26,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | ~ l1_pre_topc(X1)
% 35.45/5.00      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 35.45/5.00      inference(cnf_transformation,[],[f84]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1062,plain,
% 35.45/5.00      ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
% 35.45/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.45/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_21679,plain,
% 35.45/5.00      ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2)
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1056,c_1062]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_33,negated_conjecture,
% 35.45/5.00      ( l1_pre_topc(sK1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f89]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1396,plain,
% 35.45/5.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 35.45/5.00      | ~ l1_pre_topc(sK1)
% 35.45/5.00      | k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(instantiation,[status(thm)],[c_26]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_22013,plain,
% 35.45/5.00      ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(global_propositional_subsumption,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_21679,c_33,c_32,c_1396]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_25,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | ~ l1_pre_topc(X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f83]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1063,plain,
% 35.45/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.45/5.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 35.45/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_22020,plain,
% 35.45/5.00      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 35.45/5.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_22013,c_1063]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_36,plain,
% 35.45/5.00      ( l1_pre_topc(sK1) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_37,plain,
% 35.45/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1333,plain,
% 35.45/5.00      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 35.45/5.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 35.45/5.00      | ~ l1_pre_topc(sK1) ),
% 35.45/5.00      inference(instantiation,[status(thm)],[c_25]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1334,plain,
% 35.45/5.00      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 35.45/5.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_22382,plain,
% 35.45/5.00      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 35.45/5.00      inference(global_propositional_subsumption,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_22020,c_36,c_37,c_1334]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_18,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.45/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.45/5.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 35.45/5.00      inference(cnf_transformation,[],[f76]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_21,plain,
% 35.45/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f80]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_207,plain,
% 35.45/5.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.45/5.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_208,plain,
% 35.45/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.45/5.00      inference(renaming,[status(thm)],[c_207]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_268,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.45/5.00      | ~ r1_tarski(X2,X1)
% 35.45/5.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 35.45/5.00      inference(bin_hyper_res,[status(thm)],[c_18,c_208]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1050,plain,
% 35.45/5.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 35.45/5.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 35.45/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_127508,plain,
% 35.45/5.00      ( k4_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,sK2)) = k2_xboole_0(X0,k2_tops_1(sK1,sK2))
% 35.45/5.00      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_22382,c_1050]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_131005,plain,
% 35.45/5.00      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_3757,c_127508]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_27,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | ~ l1_pre_topc(X1)
% 35.45/5.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 35.45/5.00      inference(cnf_transformation,[],[f85]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1061,plain,
% 35.45/5.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 35.45/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.45/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_26759,plain,
% 35.45/5.00      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2)
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1056,c_1061]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1432,plain,
% 35.45/5.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 35.45/5.00      | ~ l1_pre_topc(sK1)
% 35.45/5.00      | k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 35.45/5.00      inference(instantiation,[status(thm)],[c_27]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_26957,plain,
% 35.45/5.00      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 35.45/5.00      inference(global_propositional_subsumption,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_26759,c_33,c_32,c_1432]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_19,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.45/5.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 35.45/5.00      inference(cnf_transformation,[],[f104]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_269,plain,
% 35.45/5.00      ( ~ r1_tarski(X0,X1)
% 35.45/5.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 35.45/5.00      inference(bin_hyper_res,[status(thm)],[c_19,c_208]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1049,plain,
% 35.45/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 35.45/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_4019,plain,
% 35.45/5.00      ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_3757,c_1049]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_31,negated_conjecture,
% 35.45/5.00      ( v4_pre_topc(sK2,sK1)
% 35.45/5.00      | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(cnf_transformation,[],[f91]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1057,plain,
% 35.45/5.00      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_4298,plain,
% 35.45/5.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) = k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) = iProver_top ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_4019,c_1057]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_28,plain,
% 35.45/5.00      ( ~ v4_pre_topc(X0,X1)
% 35.45/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 35.45/5.00      | ~ l1_pre_topc(X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f86]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1060,plain,
% 35.45/5.00      ( v4_pre_topc(X0,X1) != iProver_top
% 35.45/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.45/5.00      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 35.45/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2591,plain,
% 35.45/5.00      ( v4_pre_topc(sK2,sK1) != iProver_top
% 35.45/5.00      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1056,c_1060]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2911,plain,
% 35.45/5.00      ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top
% 35.45/5.00      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 35.45/5.00      inference(global_propositional_subsumption,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_2591,c_36]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2912,plain,
% 35.45/5.00      ( v4_pre_topc(sK2,sK1) != iProver_top
% 35.45/5.00      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 35.45/5.00      inference(renaming,[status(thm)],[c_2911]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_9,plain,
% 35.45/5.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.45/5.00      inference(cnf_transformation,[],[f66]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1070,plain,
% 35.45/5.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_3609,plain,
% 35.45/5.00      ( k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_2912,c_1070]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_4852,plain,
% 35.45/5.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) = k2_tops_1(sK1,sK2)
% 35.45/5.00      | k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_4298,c_3609]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_11,plain,
% 35.45/5.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 35.45/5.00      inference(cnf_transformation,[],[f100]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1068,plain,
% 35.45/5.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_4856,plain,
% 35.45/5.00      ( k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2)
% 35.45/5.00      | r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_4852,c_1068]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_5968,plain,
% 35.45/5.00      ( k3_xboole_0(k2_tops_1(sK1,sK2),sK2) = k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(forward_subsumption_resolution,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_4856,c_1070]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_12,plain,
% 35.45/5.00      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f101]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_5978,plain,
% 35.45/5.00      ( k2_xboole_0(sK2,k5_xboole_0(k2_tops_1(sK1,sK2),k2_tops_1(sK1,sK2))) = k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_5968,c_12]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_13,plain,
% 35.45/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 35.45/5.00      inference(cnf_transformation,[],[f102]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_0,plain,
% 35.45/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f93]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2655,plain,
% 35.45/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_7,plain,
% 35.45/5.00      ( k3_xboole_0(X0,X0) = X0 ),
% 35.45/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2677,plain,
% 35.45/5.00      ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 35.45/5.00      inference(light_normalisation,[status(thm)],[c_2655,c_7]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_5990,plain,
% 35.45/5.00      ( k2_xboole_0(sK2,k3_xboole_0(k2_tops_1(sK1,sK2),k1_xboole_0)) = k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_5978,c_2677]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_8,plain,
% 35.45/5.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.45/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_10,plain,
% 35.45/5.00      ( r1_tarski(k1_xboole_0,X0) ),
% 35.45/5.00      inference(cnf_transformation,[],[f67]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1069,plain,
% 35.45/5.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_3606,plain,
% 35.45/5.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1069,c_1070]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_14,plain,
% 35.45/5.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 35.45/5.00      inference(cnf_transformation,[],[f72]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_20,plain,
% 35.45/5.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f78]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1531,plain,
% 35.45/5.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_14,c_20]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1909,plain,
% 35.45/5.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1531,c_20]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_32181,plain,
% 35.45/5.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_3606,c_1909]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_38925,plain,
% 35.45/5.00      ( k2_xboole_0(sK2,k2_tops_1(sK1,sK2)) = sK2 ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_5990,c_8,c_32181]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_131034,plain,
% 35.45/5.00      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 35.45/5.00      inference(light_normalisation,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_131005,c_26957,c_38925]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_29,plain,
% 35.45/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | ~ l1_pre_topc(X1)
% 35.45/5.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 35.45/5.00      inference(cnf_transformation,[],[f87]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1059,plain,
% 35.45/5.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 35.45/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.45/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_26722,plain,
% 35.45/5.00      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_1056,c_1059]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2164,plain,
% 35.45/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_13,c_1068]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_2274,plain,
% 35.45/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_2164,c_1049]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_7301,plain,
% 35.45/5.00      ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_2274,c_4019]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_26730,plain,
% 35.45/5.00      ( k7_subset_1(sK2,sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2)
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_26722,c_7301]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_27051,plain,
% 35.45/5.00      ( k7_subset_1(sK2,sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(global_propositional_subsumption,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_26730,c_36]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_7295,plain,
% 35.45/5.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,X1) ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_2274,c_0]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_27065,plain,
% 35.45/5.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) = k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_27051,c_7295]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_27110,plain,
% 35.45/5.00      ( k7_subset_1(sK2,sK2,k1_tops_1(sK1,sK2)) = k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_27065,c_2274]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_30,negated_conjecture,
% 35.45/5.00      ( ~ v4_pre_topc(sK2,sK1)
% 35.45/5.00      | k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(cnf_transformation,[],[f92]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1058,plain,
% 35.45/5.00      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_4299,plain,
% 35.45/5.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tops_1(sK1,sK2))) != k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_4019,c_1058]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_7305,plain,
% 35.45/5.00      ( k7_subset_1(sK2,sK2,k1_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_2274,c_4299]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_32334,plain,
% 35.45/5.00      ( k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) != k2_tops_1(sK1,sK2)
% 35.45/5.00      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 35.45/5.00      inference(demodulation,[status(thm)],[c_27110,c_7305]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_5977,plain,
% 35.45/5.00      ( k3_xboole_0(sK2,k2_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 35.45/5.00      inference(superposition,[status(thm)],[c_5968,c_1909]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_23,plain,
% 35.45/5.00      ( v4_pre_topc(X0,X1)
% 35.45/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.45/5.00      | ~ l1_pre_topc(X1)
% 35.45/5.00      | ~ v2_pre_topc(X1)
% 35.45/5.00      | k2_pre_topc(X1,X0) != X0 ),
% 35.45/5.00      inference(cnf_transformation,[],[f82]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1429,plain,
% 35.45/5.00      ( v4_pre_topc(sK2,sK1)
% 35.45/5.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 35.45/5.00      | ~ l1_pre_topc(sK1)
% 35.45/5.00      | ~ v2_pre_topc(sK1)
% 35.45/5.00      | k2_pre_topc(sK1,sK2) != sK2 ),
% 35.45/5.00      inference(instantiation,[status(thm)],[c_23]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_1430,plain,
% 35.45/5.00      ( k2_pre_topc(sK1,sK2) != sK2
% 35.45/5.00      | v4_pre_topc(sK2,sK1) = iProver_top
% 35.45/5.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 35.45/5.00      | l1_pre_topc(sK1) != iProver_top
% 35.45/5.00      | v2_pre_topc(sK1) != iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_34,negated_conjecture,
% 35.45/5.00      ( v2_pre_topc(sK1) ),
% 35.45/5.00      inference(cnf_transformation,[],[f88]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(c_35,plain,
% 35.45/5.00      ( v2_pre_topc(sK1) = iProver_top ),
% 35.45/5.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.45/5.00  
% 35.45/5.00  cnf(contradiction,plain,
% 35.45/5.00      ( $false ),
% 35.45/5.00      inference(minisat,
% 35.45/5.00                [status(thm)],
% 35.45/5.00                [c_131034,c_32334,c_5977,c_1430,c_37,c_36,c_35]) ).
% 35.45/5.00  
% 35.45/5.00  
% 35.45/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.45/5.00  
% 35.45/5.00  ------                               Statistics
% 35.45/5.00  
% 35.45/5.00  ------ Selected
% 35.45/5.00  
% 35.45/5.00  total_time:                             4.141
% 35.45/5.00  
%------------------------------------------------------------------------------
