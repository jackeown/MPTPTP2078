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
% DateTime   : Thu Dec  3 12:15:15 EST 2020

% Result     : Theorem 47.45s
% Output     : CNFRefutation 47.45s
% Verified   : 
% Statistics : Number of formulae       :  231 (1146 expanded)
%              Number of clauses        :  147 ( 366 expanded)
%              Number of leaves         :   25 ( 247 expanded)
%              Depth                    :   20
%              Number of atoms          :  689 (4899 expanded)
%              Number of equality atoms :  245 ( 517 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).

fof(f95,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1631,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_1628,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_2033,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1631,c_1628])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_1626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_2043,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_1626])).

cnf(c_33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_579,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_3560,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2043,c_33,c_579])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1639,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4324,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_1639])).

cnf(c_51944,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_4324])).

cnf(c_174248,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1631,c_51944])).

cnf(c_29,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_247,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_20,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_434,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = k2_struct_0(X3)
    | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_435,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_449,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_435,c_8])).

cnf(c_467,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_449,c_31])).

cnf(c_468,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_468])).

cnf(c_694,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_854,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(prop_impl,[status(thm)],[c_30,c_694])).

cnf(c_1620,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1645,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3185,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1645])).

cnf(c_26,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_512,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_513,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_513,c_468])).

cnf(c_652,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_1627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_1700,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_1627])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1641,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3988,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1641])).

cnf(c_5403,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_3988])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_530,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_27,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_497,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_498,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_498])).

cnf(c_680,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_682,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_30])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1778,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_tops_1(sK0,X2),X3)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(k1_tops_1(sK0,X2),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2086,plain,
    ( r1_xboole_0(k1_tops_1(sK0,X0),X1)
    | ~ r1_xboole_0(k1_tops_1(sK0,X2),k2_tops_1(sK0,X2))
    | ~ r1_tarski(X1,k2_tops_1(sK0,X2))
    | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X2)) ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_2088,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | r1_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2339,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2341,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2339])).

cnf(c_1644,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5402,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_3988])).

cnf(c_5404,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5402])).

cnf(c_5407,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5403,c_30,c_530,c_682,c_2088,c_2341,c_5404])).

cnf(c_15438,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3185,c_30,c_530,c_652,c_682,c_2088,c_2341,c_5404])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_1629,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_2995,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1629])).

cnf(c_13150,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_1631,c_2995])).

cnf(c_13157,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_13150,c_2033])).

cnf(c_15440,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_15438,c_13157])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1636,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3961,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k2_xboole_0(X1,k3_subset_1(X0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1636])).

cnf(c_135465,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_3961])).

cnf(c_135752,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_3560,c_135465])).

cnf(c_174267,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_174248,c_15440,c_135752])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1640,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_174491,plain,
    ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_174267,c_1640])).

cnf(c_174495,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_174491])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32223,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_32224,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32223])).

cnf(c_1884,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,k3_subset_1(X3,X4))
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,k3_subset_1(X3,X4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7567,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_16309,plain,
    ( ~ r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_7567])).

cnf(c_16310,plain,
    ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16309])).

cnf(c_16312,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_xboole_0(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16310])).

cnf(c_1009,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1999,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_struct_0(sK0))
    | X2 != X0
    | k2_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_8708,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)))
    | r1_tarski(X2,k2_struct_0(sK0))
    | X2 != X0
    | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_8718,plain,
    ( X0 != X1
    | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2))
    | r1_tarski(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8708])).

cnf(c_8720,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 != sK1
    | r1_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top
    | r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8718])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_1625,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_2523,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1631,c_1625])).

cnf(c_5411,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5407,c_2523])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_subset_1(X1,X0))
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X2,k3_subset_1(X1,X0)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5542,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5411,c_1633])).

cnf(c_5552,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5542])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X2,k3_subset_1(X1,X0))
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4504,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4503])).

cnf(c_4506,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4504])).

cnf(c_4483,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4484,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4483])).

cnf(c_1008,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1769,plain,
    ( X0 != X1
    | k2_struct_0(sK0) != X1
    | k2_struct_0(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_2015,plain,
    ( X0 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = X0
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_3157,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_3158,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_2965,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_2966,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2965])).

cnf(c_2968,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_1007,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2047,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_28,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_245,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_245,c_513])).

cnf(c_708,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_710,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_30])).

cnf(c_712,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_112,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_107,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_109,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_108,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_174495,c_32224,c_16312,c_8720,c_5552,c_5407,c_4506,c_4484,c_3158,c_2968,c_2047,c_712,c_652,c_112,c_109,c_108,c_33,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 47.45/6.57  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.45/6.57  
% 47.45/6.57  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.45/6.57  
% 47.45/6.57  ------  iProver source info
% 47.45/6.57  
% 47.45/6.57  git: date: 2020-06-30 10:37:57 +0100
% 47.45/6.57  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.45/6.57  git: non_committed_changes: false
% 47.45/6.57  git: last_make_outside_of_git: false
% 47.45/6.57  
% 47.45/6.57  ------ 
% 47.45/6.57  
% 47.45/6.57  ------ Input Options
% 47.45/6.57  
% 47.45/6.57  --out_options                           all
% 47.45/6.57  --tptp_safe_out                         true
% 47.45/6.57  --problem_path                          ""
% 47.45/6.57  --include_path                          ""
% 47.45/6.57  --clausifier                            res/vclausify_rel
% 47.45/6.57  --clausifier_options                    ""
% 47.45/6.57  --stdin                                 false
% 47.45/6.57  --stats_out                             all
% 47.45/6.57  
% 47.45/6.57  ------ General Options
% 47.45/6.57  
% 47.45/6.57  --fof                                   false
% 47.45/6.57  --time_out_real                         305.
% 47.45/6.57  --time_out_virtual                      -1.
% 47.45/6.57  --symbol_type_check                     false
% 47.45/6.57  --clausify_out                          false
% 47.45/6.57  --sig_cnt_out                           false
% 47.45/6.57  --trig_cnt_out                          false
% 47.45/6.57  --trig_cnt_out_tolerance                1.
% 47.45/6.57  --trig_cnt_out_sk_spl                   false
% 47.45/6.57  --abstr_cl_out                          false
% 47.45/6.57  
% 47.45/6.57  ------ Global Options
% 47.45/6.57  
% 47.45/6.57  --schedule                              default
% 47.45/6.57  --add_important_lit                     false
% 47.45/6.57  --prop_solver_per_cl                    1000
% 47.45/6.57  --min_unsat_core                        false
% 47.45/6.57  --soft_assumptions                      false
% 47.45/6.57  --soft_lemma_size                       3
% 47.45/6.57  --prop_impl_unit_size                   0
% 47.45/6.57  --prop_impl_unit                        []
% 47.45/6.57  --share_sel_clauses                     true
% 47.45/6.57  --reset_solvers                         false
% 47.45/6.57  --bc_imp_inh                            [conj_cone]
% 47.45/6.57  --conj_cone_tolerance                   3.
% 47.45/6.57  --extra_neg_conj                        none
% 47.45/6.57  --large_theory_mode                     true
% 47.45/6.57  --prolific_symb_bound                   200
% 47.45/6.57  --lt_threshold                          2000
% 47.45/6.57  --clause_weak_htbl                      true
% 47.45/6.57  --gc_record_bc_elim                     false
% 47.45/6.57  
% 47.45/6.57  ------ Preprocessing Options
% 47.45/6.57  
% 47.45/6.57  --preprocessing_flag                    true
% 47.45/6.57  --time_out_prep_mult                    0.1
% 47.45/6.57  --splitting_mode                        input
% 47.45/6.57  --splitting_grd                         true
% 47.45/6.57  --splitting_cvd                         false
% 47.45/6.57  --splitting_cvd_svl                     false
% 47.45/6.57  --splitting_nvd                         32
% 47.45/6.57  --sub_typing                            true
% 47.45/6.57  --prep_gs_sim                           true
% 47.45/6.57  --prep_unflatten                        true
% 47.45/6.57  --prep_res_sim                          true
% 47.45/6.57  --prep_upred                            true
% 47.45/6.57  --prep_sem_filter                       exhaustive
% 47.45/6.57  --prep_sem_filter_out                   false
% 47.45/6.57  --pred_elim                             true
% 47.45/6.57  --res_sim_input                         true
% 47.45/6.57  --eq_ax_congr_red                       true
% 47.45/6.57  --pure_diseq_elim                       true
% 47.45/6.57  --brand_transform                       false
% 47.45/6.57  --non_eq_to_eq                          false
% 47.45/6.57  --prep_def_merge                        true
% 47.45/6.57  --prep_def_merge_prop_impl              false
% 47.45/6.57  --prep_def_merge_mbd                    true
% 47.45/6.57  --prep_def_merge_tr_red                 false
% 47.45/6.57  --prep_def_merge_tr_cl                  false
% 47.45/6.57  --smt_preprocessing                     true
% 47.45/6.57  --smt_ac_axioms                         fast
% 47.45/6.57  --preprocessed_out                      false
% 47.45/6.57  --preprocessed_stats                    false
% 47.45/6.57  
% 47.45/6.57  ------ Abstraction refinement Options
% 47.45/6.57  
% 47.45/6.57  --abstr_ref                             []
% 47.45/6.57  --abstr_ref_prep                        false
% 47.45/6.57  --abstr_ref_until_sat                   false
% 47.45/6.57  --abstr_ref_sig_restrict                funpre
% 47.45/6.57  --abstr_ref_af_restrict_to_split_sk     false
% 47.45/6.57  --abstr_ref_under                       []
% 47.45/6.57  
% 47.45/6.57  ------ SAT Options
% 47.45/6.57  
% 47.45/6.57  --sat_mode                              false
% 47.45/6.57  --sat_fm_restart_options                ""
% 47.45/6.57  --sat_gr_def                            false
% 47.45/6.57  --sat_epr_types                         true
% 47.45/6.57  --sat_non_cyclic_types                  false
% 47.45/6.57  --sat_finite_models                     false
% 47.45/6.57  --sat_fm_lemmas                         false
% 47.45/6.57  --sat_fm_prep                           false
% 47.45/6.57  --sat_fm_uc_incr                        true
% 47.45/6.57  --sat_out_model                         small
% 47.45/6.57  --sat_out_clauses                       false
% 47.45/6.57  
% 47.45/6.57  ------ QBF Options
% 47.45/6.57  
% 47.45/6.57  --qbf_mode                              false
% 47.45/6.57  --qbf_elim_univ                         false
% 47.45/6.57  --qbf_dom_inst                          none
% 47.45/6.57  --qbf_dom_pre_inst                      false
% 47.45/6.57  --qbf_sk_in                             false
% 47.45/6.57  --qbf_pred_elim                         true
% 47.45/6.57  --qbf_split                             512
% 47.45/6.57  
% 47.45/6.57  ------ BMC1 Options
% 47.45/6.57  
% 47.45/6.57  --bmc1_incremental                      false
% 47.45/6.57  --bmc1_axioms                           reachable_all
% 47.45/6.57  --bmc1_min_bound                        0
% 47.45/6.57  --bmc1_max_bound                        -1
% 47.45/6.57  --bmc1_max_bound_default                -1
% 47.45/6.57  --bmc1_symbol_reachability              true
% 47.45/6.57  --bmc1_property_lemmas                  false
% 47.45/6.57  --bmc1_k_induction                      false
% 47.45/6.57  --bmc1_non_equiv_states                 false
% 47.45/6.57  --bmc1_deadlock                         false
% 47.45/6.57  --bmc1_ucm                              false
% 47.45/6.57  --bmc1_add_unsat_core                   none
% 47.45/6.57  --bmc1_unsat_core_children              false
% 47.45/6.57  --bmc1_unsat_core_extrapolate_axioms    false
% 47.45/6.57  --bmc1_out_stat                         full
% 47.45/6.57  --bmc1_ground_init                      false
% 47.45/6.57  --bmc1_pre_inst_next_state              false
% 47.45/6.57  --bmc1_pre_inst_state                   false
% 47.45/6.57  --bmc1_pre_inst_reach_state             false
% 47.45/6.57  --bmc1_out_unsat_core                   false
% 47.45/6.57  --bmc1_aig_witness_out                  false
% 47.45/6.57  --bmc1_verbose                          false
% 47.45/6.57  --bmc1_dump_clauses_tptp                false
% 47.45/6.57  --bmc1_dump_unsat_core_tptp             false
% 47.45/6.57  --bmc1_dump_file                        -
% 47.45/6.57  --bmc1_ucm_expand_uc_limit              128
% 47.45/6.57  --bmc1_ucm_n_expand_iterations          6
% 47.45/6.57  --bmc1_ucm_extend_mode                  1
% 47.45/6.57  --bmc1_ucm_init_mode                    2
% 47.45/6.57  --bmc1_ucm_cone_mode                    none
% 47.45/6.57  --bmc1_ucm_reduced_relation_type        0
% 47.45/6.57  --bmc1_ucm_relax_model                  4
% 47.45/6.57  --bmc1_ucm_full_tr_after_sat            true
% 47.45/6.57  --bmc1_ucm_expand_neg_assumptions       false
% 47.45/6.57  --bmc1_ucm_layered_model                none
% 47.45/6.57  --bmc1_ucm_max_lemma_size               10
% 47.45/6.57  
% 47.45/6.57  ------ AIG Options
% 47.45/6.57  
% 47.45/6.57  --aig_mode                              false
% 47.45/6.57  
% 47.45/6.57  ------ Instantiation Options
% 47.45/6.57  
% 47.45/6.57  --instantiation_flag                    true
% 47.45/6.57  --inst_sos_flag                         true
% 47.45/6.57  --inst_sos_phase                        true
% 47.45/6.57  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.45/6.57  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.45/6.57  --inst_lit_sel_side                     num_symb
% 47.45/6.57  --inst_solver_per_active                1400
% 47.45/6.57  --inst_solver_calls_frac                1.
% 47.45/6.57  --inst_passive_queue_type               priority_queues
% 47.45/6.57  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.45/6.57  --inst_passive_queues_freq              [25;2]
% 47.45/6.57  --inst_dismatching                      true
% 47.45/6.57  --inst_eager_unprocessed_to_passive     true
% 47.45/6.57  --inst_prop_sim_given                   true
% 47.45/6.57  --inst_prop_sim_new                     false
% 47.45/6.57  --inst_subs_new                         false
% 47.45/6.57  --inst_eq_res_simp                      false
% 47.45/6.57  --inst_subs_given                       false
% 47.45/6.57  --inst_orphan_elimination               true
% 47.45/6.57  --inst_learning_loop_flag               true
% 47.45/6.57  --inst_learning_start                   3000
% 47.45/6.57  --inst_learning_factor                  2
% 47.45/6.57  --inst_start_prop_sim_after_learn       3
% 47.45/6.57  --inst_sel_renew                        solver
% 47.45/6.57  --inst_lit_activity_flag                true
% 47.45/6.57  --inst_restr_to_given                   false
% 47.45/6.57  --inst_activity_threshold               500
% 47.45/6.57  --inst_out_proof                        true
% 47.45/6.57  
% 47.45/6.57  ------ Resolution Options
% 47.45/6.57  
% 47.45/6.57  --resolution_flag                       true
% 47.45/6.57  --res_lit_sel                           adaptive
% 47.45/6.57  --res_lit_sel_side                      none
% 47.45/6.57  --res_ordering                          kbo
% 47.45/6.57  --res_to_prop_solver                    active
% 47.45/6.57  --res_prop_simpl_new                    false
% 47.45/6.57  --res_prop_simpl_given                  true
% 47.45/6.57  --res_passive_queue_type                priority_queues
% 47.45/6.57  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.45/6.57  --res_passive_queues_freq               [15;5]
% 47.45/6.57  --res_forward_subs                      full
% 47.45/6.57  --res_backward_subs                     full
% 47.45/6.57  --res_forward_subs_resolution           true
% 47.45/6.57  --res_backward_subs_resolution          true
% 47.45/6.57  --res_orphan_elimination                true
% 47.45/6.57  --res_time_limit                        2.
% 47.45/6.57  --res_out_proof                         true
% 47.45/6.57  
% 47.45/6.57  ------ Superposition Options
% 47.45/6.57  
% 47.45/6.57  --superposition_flag                    true
% 47.45/6.57  --sup_passive_queue_type                priority_queues
% 47.45/6.57  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.45/6.57  --sup_passive_queues_freq               [8;1;4]
% 47.45/6.57  --demod_completeness_check              fast
% 47.45/6.57  --demod_use_ground                      true
% 47.45/6.57  --sup_to_prop_solver                    passive
% 47.45/6.57  --sup_prop_simpl_new                    true
% 47.45/6.57  --sup_prop_simpl_given                  true
% 47.45/6.57  --sup_fun_splitting                     true
% 47.45/6.57  --sup_smt_interval                      50000
% 47.45/6.57  
% 47.45/6.57  ------ Superposition Simplification Setup
% 47.45/6.57  
% 47.45/6.57  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.45/6.57  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.45/6.57  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.45/6.57  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.45/6.57  --sup_full_triv                         [TrivRules;PropSubs]
% 47.45/6.57  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.45/6.57  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.45/6.57  --sup_immed_triv                        [TrivRules]
% 47.45/6.57  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.57  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.57  --sup_immed_bw_main                     []
% 47.45/6.57  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.45/6.57  --sup_input_triv                        [Unflattening;TrivRules]
% 47.45/6.57  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.57  --sup_input_bw                          []
% 47.45/6.57  
% 47.45/6.57  ------ Combination Options
% 47.45/6.57  
% 47.45/6.57  --comb_res_mult                         3
% 47.45/6.57  --comb_sup_mult                         2
% 47.45/6.57  --comb_inst_mult                        10
% 47.45/6.57  
% 47.45/6.57  ------ Debug Options
% 47.45/6.57  
% 47.45/6.57  --dbg_backtrace                         false
% 47.45/6.57  --dbg_dump_prop_clauses                 false
% 47.45/6.57  --dbg_dump_prop_clauses_file            -
% 47.45/6.57  --dbg_out_stat                          false
% 47.45/6.57  ------ Parsing...
% 47.45/6.57  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.45/6.57  
% 47.45/6.57  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 47.45/6.57  
% 47.45/6.57  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.45/6.57  
% 47.45/6.57  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.45/6.57  ------ Proving...
% 47.45/6.57  ------ Problem Properties 
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  clauses                                 28
% 47.45/6.57  conjectures                             1
% 47.45/6.57  EPR                                     5
% 47.45/6.57  Horn                                    26
% 47.45/6.57  unary                                   4
% 47.45/6.57  binary                                  13
% 47.45/6.57  lits                                    68
% 47.45/6.57  lits eq                                 16
% 47.45/6.57  fd_pure                                 0
% 47.45/6.57  fd_pseudo                               0
% 47.45/6.57  fd_cond                                 1
% 47.45/6.57  fd_pseudo_cond                          1
% 47.45/6.57  AC symbols                              0
% 47.45/6.57  
% 47.45/6.57  ------ Schedule dynamic 5 is on 
% 47.45/6.57  
% 47.45/6.57  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  ------ 
% 47.45/6.57  Current options:
% 47.45/6.57  ------ 
% 47.45/6.57  
% 47.45/6.57  ------ Input Options
% 47.45/6.57  
% 47.45/6.57  --out_options                           all
% 47.45/6.57  --tptp_safe_out                         true
% 47.45/6.57  --problem_path                          ""
% 47.45/6.57  --include_path                          ""
% 47.45/6.57  --clausifier                            res/vclausify_rel
% 47.45/6.57  --clausifier_options                    ""
% 47.45/6.57  --stdin                                 false
% 47.45/6.57  --stats_out                             all
% 47.45/6.57  
% 47.45/6.57  ------ General Options
% 47.45/6.57  
% 47.45/6.57  --fof                                   false
% 47.45/6.57  --time_out_real                         305.
% 47.45/6.57  --time_out_virtual                      -1.
% 47.45/6.57  --symbol_type_check                     false
% 47.45/6.57  --clausify_out                          false
% 47.45/6.57  --sig_cnt_out                           false
% 47.45/6.57  --trig_cnt_out                          false
% 47.45/6.57  --trig_cnt_out_tolerance                1.
% 47.45/6.57  --trig_cnt_out_sk_spl                   false
% 47.45/6.57  --abstr_cl_out                          false
% 47.45/6.57  
% 47.45/6.57  ------ Global Options
% 47.45/6.57  
% 47.45/6.57  --schedule                              default
% 47.45/6.57  --add_important_lit                     false
% 47.45/6.57  --prop_solver_per_cl                    1000
% 47.45/6.57  --min_unsat_core                        false
% 47.45/6.57  --soft_assumptions                      false
% 47.45/6.57  --soft_lemma_size                       3
% 47.45/6.57  --prop_impl_unit_size                   0
% 47.45/6.57  --prop_impl_unit                        []
% 47.45/6.57  --share_sel_clauses                     true
% 47.45/6.57  --reset_solvers                         false
% 47.45/6.57  --bc_imp_inh                            [conj_cone]
% 47.45/6.57  --conj_cone_tolerance                   3.
% 47.45/6.57  --extra_neg_conj                        none
% 47.45/6.57  --large_theory_mode                     true
% 47.45/6.57  --prolific_symb_bound                   200
% 47.45/6.57  --lt_threshold                          2000
% 47.45/6.57  --clause_weak_htbl                      true
% 47.45/6.57  --gc_record_bc_elim                     false
% 47.45/6.57  
% 47.45/6.57  ------ Preprocessing Options
% 47.45/6.57  
% 47.45/6.57  --preprocessing_flag                    true
% 47.45/6.57  --time_out_prep_mult                    0.1
% 47.45/6.57  --splitting_mode                        input
% 47.45/6.57  --splitting_grd                         true
% 47.45/6.57  --splitting_cvd                         false
% 47.45/6.57  --splitting_cvd_svl                     false
% 47.45/6.57  --splitting_nvd                         32
% 47.45/6.57  --sub_typing                            true
% 47.45/6.57  --prep_gs_sim                           true
% 47.45/6.57  --prep_unflatten                        true
% 47.45/6.57  --prep_res_sim                          true
% 47.45/6.57  --prep_upred                            true
% 47.45/6.57  --prep_sem_filter                       exhaustive
% 47.45/6.57  --prep_sem_filter_out                   false
% 47.45/6.57  --pred_elim                             true
% 47.45/6.57  --res_sim_input                         true
% 47.45/6.57  --eq_ax_congr_red                       true
% 47.45/6.57  --pure_diseq_elim                       true
% 47.45/6.57  --brand_transform                       false
% 47.45/6.57  --non_eq_to_eq                          false
% 47.45/6.57  --prep_def_merge                        true
% 47.45/6.57  --prep_def_merge_prop_impl              false
% 47.45/6.57  --prep_def_merge_mbd                    true
% 47.45/6.57  --prep_def_merge_tr_red                 false
% 47.45/6.57  --prep_def_merge_tr_cl                  false
% 47.45/6.57  --smt_preprocessing                     true
% 47.45/6.57  --smt_ac_axioms                         fast
% 47.45/6.57  --preprocessed_out                      false
% 47.45/6.57  --preprocessed_stats                    false
% 47.45/6.57  
% 47.45/6.57  ------ Abstraction refinement Options
% 47.45/6.57  
% 47.45/6.57  --abstr_ref                             []
% 47.45/6.57  --abstr_ref_prep                        false
% 47.45/6.57  --abstr_ref_until_sat                   false
% 47.45/6.57  --abstr_ref_sig_restrict                funpre
% 47.45/6.57  --abstr_ref_af_restrict_to_split_sk     false
% 47.45/6.57  --abstr_ref_under                       []
% 47.45/6.57  
% 47.45/6.57  ------ SAT Options
% 47.45/6.57  
% 47.45/6.57  --sat_mode                              false
% 47.45/6.57  --sat_fm_restart_options                ""
% 47.45/6.57  --sat_gr_def                            false
% 47.45/6.57  --sat_epr_types                         true
% 47.45/6.57  --sat_non_cyclic_types                  false
% 47.45/6.57  --sat_finite_models                     false
% 47.45/6.57  --sat_fm_lemmas                         false
% 47.45/6.57  --sat_fm_prep                           false
% 47.45/6.57  --sat_fm_uc_incr                        true
% 47.45/6.57  --sat_out_model                         small
% 47.45/6.57  --sat_out_clauses                       false
% 47.45/6.57  
% 47.45/6.57  ------ QBF Options
% 47.45/6.57  
% 47.45/6.57  --qbf_mode                              false
% 47.45/6.57  --qbf_elim_univ                         false
% 47.45/6.57  --qbf_dom_inst                          none
% 47.45/6.57  --qbf_dom_pre_inst                      false
% 47.45/6.57  --qbf_sk_in                             false
% 47.45/6.57  --qbf_pred_elim                         true
% 47.45/6.57  --qbf_split                             512
% 47.45/6.57  
% 47.45/6.57  ------ BMC1 Options
% 47.45/6.57  
% 47.45/6.57  --bmc1_incremental                      false
% 47.45/6.57  --bmc1_axioms                           reachable_all
% 47.45/6.57  --bmc1_min_bound                        0
% 47.45/6.57  --bmc1_max_bound                        -1
% 47.45/6.57  --bmc1_max_bound_default                -1
% 47.45/6.57  --bmc1_symbol_reachability              true
% 47.45/6.57  --bmc1_property_lemmas                  false
% 47.45/6.57  --bmc1_k_induction                      false
% 47.45/6.57  --bmc1_non_equiv_states                 false
% 47.45/6.57  --bmc1_deadlock                         false
% 47.45/6.57  --bmc1_ucm                              false
% 47.45/6.57  --bmc1_add_unsat_core                   none
% 47.45/6.57  --bmc1_unsat_core_children              false
% 47.45/6.57  --bmc1_unsat_core_extrapolate_axioms    false
% 47.45/6.57  --bmc1_out_stat                         full
% 47.45/6.57  --bmc1_ground_init                      false
% 47.45/6.57  --bmc1_pre_inst_next_state              false
% 47.45/6.57  --bmc1_pre_inst_state                   false
% 47.45/6.57  --bmc1_pre_inst_reach_state             false
% 47.45/6.57  --bmc1_out_unsat_core                   false
% 47.45/6.57  --bmc1_aig_witness_out                  false
% 47.45/6.57  --bmc1_verbose                          false
% 47.45/6.57  --bmc1_dump_clauses_tptp                false
% 47.45/6.57  --bmc1_dump_unsat_core_tptp             false
% 47.45/6.57  --bmc1_dump_file                        -
% 47.45/6.57  --bmc1_ucm_expand_uc_limit              128
% 47.45/6.57  --bmc1_ucm_n_expand_iterations          6
% 47.45/6.57  --bmc1_ucm_extend_mode                  1
% 47.45/6.57  --bmc1_ucm_init_mode                    2
% 47.45/6.57  --bmc1_ucm_cone_mode                    none
% 47.45/6.57  --bmc1_ucm_reduced_relation_type        0
% 47.45/6.57  --bmc1_ucm_relax_model                  4
% 47.45/6.57  --bmc1_ucm_full_tr_after_sat            true
% 47.45/6.57  --bmc1_ucm_expand_neg_assumptions       false
% 47.45/6.57  --bmc1_ucm_layered_model                none
% 47.45/6.57  --bmc1_ucm_max_lemma_size               10
% 47.45/6.57  
% 47.45/6.57  ------ AIG Options
% 47.45/6.57  
% 47.45/6.57  --aig_mode                              false
% 47.45/6.57  
% 47.45/6.57  ------ Instantiation Options
% 47.45/6.57  
% 47.45/6.57  --instantiation_flag                    true
% 47.45/6.57  --inst_sos_flag                         true
% 47.45/6.57  --inst_sos_phase                        true
% 47.45/6.57  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.45/6.57  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.45/6.57  --inst_lit_sel_side                     none
% 47.45/6.57  --inst_solver_per_active                1400
% 47.45/6.57  --inst_solver_calls_frac                1.
% 47.45/6.57  --inst_passive_queue_type               priority_queues
% 47.45/6.57  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.45/6.57  --inst_passive_queues_freq              [25;2]
% 47.45/6.57  --inst_dismatching                      true
% 47.45/6.57  --inst_eager_unprocessed_to_passive     true
% 47.45/6.57  --inst_prop_sim_given                   true
% 47.45/6.57  --inst_prop_sim_new                     false
% 47.45/6.57  --inst_subs_new                         false
% 47.45/6.57  --inst_eq_res_simp                      false
% 47.45/6.57  --inst_subs_given                       false
% 47.45/6.57  --inst_orphan_elimination               true
% 47.45/6.57  --inst_learning_loop_flag               true
% 47.45/6.57  --inst_learning_start                   3000
% 47.45/6.57  --inst_learning_factor                  2
% 47.45/6.57  --inst_start_prop_sim_after_learn       3
% 47.45/6.57  --inst_sel_renew                        solver
% 47.45/6.57  --inst_lit_activity_flag                true
% 47.45/6.57  --inst_restr_to_given                   false
% 47.45/6.57  --inst_activity_threshold               500
% 47.45/6.57  --inst_out_proof                        true
% 47.45/6.57  
% 47.45/6.57  ------ Resolution Options
% 47.45/6.57  
% 47.45/6.57  --resolution_flag                       false
% 47.45/6.57  --res_lit_sel                           adaptive
% 47.45/6.57  --res_lit_sel_side                      none
% 47.45/6.57  --res_ordering                          kbo
% 47.45/6.57  --res_to_prop_solver                    active
% 47.45/6.57  --res_prop_simpl_new                    false
% 47.45/6.57  --res_prop_simpl_given                  true
% 47.45/6.57  --res_passive_queue_type                priority_queues
% 47.45/6.57  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.45/6.57  --res_passive_queues_freq               [15;5]
% 47.45/6.57  --res_forward_subs                      full
% 47.45/6.57  --res_backward_subs                     full
% 47.45/6.57  --res_forward_subs_resolution           true
% 47.45/6.57  --res_backward_subs_resolution          true
% 47.45/6.57  --res_orphan_elimination                true
% 47.45/6.57  --res_time_limit                        2.
% 47.45/6.57  --res_out_proof                         true
% 47.45/6.57  
% 47.45/6.57  ------ Superposition Options
% 47.45/6.57  
% 47.45/6.57  --superposition_flag                    true
% 47.45/6.57  --sup_passive_queue_type                priority_queues
% 47.45/6.57  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.45/6.57  --sup_passive_queues_freq               [8;1;4]
% 47.45/6.57  --demod_completeness_check              fast
% 47.45/6.57  --demod_use_ground                      true
% 47.45/6.57  --sup_to_prop_solver                    passive
% 47.45/6.57  --sup_prop_simpl_new                    true
% 47.45/6.57  --sup_prop_simpl_given                  true
% 47.45/6.57  --sup_fun_splitting                     true
% 47.45/6.57  --sup_smt_interval                      50000
% 47.45/6.57  
% 47.45/6.57  ------ Superposition Simplification Setup
% 47.45/6.57  
% 47.45/6.57  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.45/6.57  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.45/6.57  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.45/6.57  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.45/6.57  --sup_full_triv                         [TrivRules;PropSubs]
% 47.45/6.57  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.45/6.57  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.45/6.57  --sup_immed_triv                        [TrivRules]
% 47.45/6.57  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.57  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.57  --sup_immed_bw_main                     []
% 47.45/6.57  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.45/6.57  --sup_input_triv                        [Unflattening;TrivRules]
% 47.45/6.57  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.57  --sup_input_bw                          []
% 47.45/6.57  
% 47.45/6.57  ------ Combination Options
% 47.45/6.57  
% 47.45/6.57  --comb_res_mult                         3
% 47.45/6.57  --comb_sup_mult                         2
% 47.45/6.57  --comb_inst_mult                        10
% 47.45/6.57  
% 47.45/6.57  ------ Debug Options
% 47.45/6.57  
% 47.45/6.57  --dbg_backtrace                         false
% 47.45/6.57  --dbg_dump_prop_clauses                 false
% 47.45/6.57  --dbg_dump_prop_clauses_file            -
% 47.45/6.57  --dbg_out_stat                          false
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  ------ Proving...
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  % SZS status Theorem for theBenchmark.p
% 47.45/6.57  
% 47.45/6.57  % SZS output start CNFRefutation for theBenchmark.p
% 47.45/6.57  
% 47.45/6.57  fof(f24,conjecture,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f25,negated_conjecture,(
% 47.45/6.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 47.45/6.57    inference(negated_conjecture,[],[f24])).
% 47.45/6.57  
% 47.45/6.57  fof(f54,plain,(
% 47.45/6.57    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f25])).
% 47.45/6.57  
% 47.45/6.57  fof(f61,plain,(
% 47.45/6.57    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 47.45/6.57    inference(nnf_transformation,[],[f54])).
% 47.45/6.57  
% 47.45/6.57  fof(f62,plain,(
% 47.45/6.57    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 47.45/6.57    inference(flattening,[],[f61])).
% 47.45/6.57  
% 47.45/6.57  fof(f64,plain,(
% 47.45/6.57    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.45/6.57    introduced(choice_axiom,[])).
% 47.45/6.57  
% 47.45/6.57  fof(f63,plain,(
% 47.45/6.57    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 47.45/6.57    introduced(choice_axiom,[])).
% 47.45/6.57  
% 47.45/6.57  fof(f65,plain,(
% 47.45/6.57    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 47.45/6.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).
% 47.45/6.57  
% 47.45/6.57  fof(f95,plain,(
% 47.45/6.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 47.45/6.57    inference(cnf_transformation,[],[f65])).
% 47.45/6.57  
% 47.45/6.57  fof(f7,axiom,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f35,plain,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.57    inference(ennf_transformation,[],[f7])).
% 47.45/6.57  
% 47.45/6.57  fof(f74,plain,(
% 47.45/6.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.57    inference(cnf_transformation,[],[f35])).
% 47.45/6.57  
% 47.45/6.57  fof(f20,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f50,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f20])).
% 47.45/6.57  
% 47.45/6.57  fof(f89,plain,(
% 47.45/6.57    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f50])).
% 47.45/6.57  
% 47.45/6.57  fof(f94,plain,(
% 47.45/6.57    l1_pre_topc(sK0)),
% 47.45/6.57    inference(cnf_transformation,[],[f65])).
% 47.45/6.57  
% 47.45/6.57  fof(f18,axiom,(
% 47.45/6.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f47,plain,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 47.45/6.57    inference(ennf_transformation,[],[f18])).
% 47.45/6.57  
% 47.45/6.57  fof(f48,plain,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(flattening,[],[f47])).
% 47.45/6.57  
% 47.45/6.57  fof(f87,plain,(
% 47.45/6.57    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f48])).
% 47.45/6.57  
% 47.45/6.57  fof(f6,axiom,(
% 47.45/6.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f33,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 47.45/6.57    inference(ennf_transformation,[],[f6])).
% 47.45/6.57  
% 47.45/6.57  fof(f34,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.57    inference(flattening,[],[f33])).
% 47.45/6.57  
% 47.45/6.57  fof(f73,plain,(
% 47.45/6.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.57    inference(cnf_transformation,[],[f34])).
% 47.45/6.57  
% 47.45/6.57  fof(f96,plain,(
% 47.45/6.57    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 47.45/6.57    inference(cnf_transformation,[],[f65])).
% 47.45/6.57  
% 47.45/6.57  fof(f16,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f45,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f16])).
% 47.45/6.57  
% 47.45/6.57  fof(f58,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(nnf_transformation,[],[f45])).
% 47.45/6.57  
% 47.45/6.57  fof(f83,plain,(
% 47.45/6.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f58])).
% 47.45/6.57  
% 47.45/6.57  fof(f17,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f46,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f17])).
% 47.45/6.57  
% 47.45/6.57  fof(f59,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(nnf_transformation,[],[f46])).
% 47.45/6.57  
% 47.45/6.57  fof(f85,plain,(
% 47.45/6.57    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f59])).
% 47.45/6.57  
% 47.45/6.57  fof(f1,axiom,(
% 47.45/6.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f55,plain,(
% 47.45/6.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.45/6.57    inference(nnf_transformation,[],[f1])).
% 47.45/6.57  
% 47.45/6.57  fof(f56,plain,(
% 47.45/6.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.45/6.57    inference(flattening,[],[f55])).
% 47.45/6.57  
% 47.45/6.57  fof(f68,plain,(
% 47.45/6.57    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f56])).
% 47.45/6.57  
% 47.45/6.57  fof(f23,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f53,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f23])).
% 47.45/6.57  
% 47.45/6.57  fof(f60,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(nnf_transformation,[],[f53])).
% 47.45/6.57  
% 47.45/6.57  fof(f93,plain,(
% 47.45/6.57    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f60])).
% 47.45/6.57  
% 47.45/6.57  fof(f19,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f49,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f19])).
% 47.45/6.57  
% 47.45/6.57  fof(f88,plain,(
% 47.45/6.57    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f49])).
% 47.45/6.57  
% 47.45/6.57  fof(f4,axiom,(
% 47.45/6.57    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f29,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 47.45/6.57    inference(ennf_transformation,[],[f4])).
% 47.45/6.57  
% 47.45/6.57  fof(f30,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 47.45/6.57    inference(flattening,[],[f29])).
% 47.45/6.57  
% 47.45/6.57  fof(f71,plain,(
% 47.45/6.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f30])).
% 47.45/6.57  
% 47.45/6.57  fof(f22,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f52,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f22])).
% 47.45/6.57  
% 47.45/6.57  fof(f91,plain,(
% 47.45/6.57    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f52])).
% 47.45/6.57  
% 47.45/6.57  fof(f92,plain,(
% 47.45/6.57    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f60])).
% 47.45/6.57  
% 47.45/6.57  fof(f3,axiom,(
% 47.45/6.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f27,plain,(
% 47.45/6.57    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 47.45/6.57    inference(ennf_transformation,[],[f3])).
% 47.45/6.57  
% 47.45/6.57  fof(f28,plain,(
% 47.45/6.57    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 47.45/6.57    inference(flattening,[],[f27])).
% 47.45/6.57  
% 47.45/6.57  fof(f70,plain,(
% 47.45/6.57    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f28])).
% 47.45/6.57  
% 47.45/6.57  fof(f66,plain,(
% 47.45/6.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 47.45/6.57    inference(cnf_transformation,[],[f56])).
% 47.45/6.57  
% 47.45/6.57  fof(f99,plain,(
% 47.45/6.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 47.45/6.57    inference(equality_resolution,[],[f66])).
% 47.45/6.57  
% 47.45/6.57  fof(f21,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f51,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f21])).
% 47.45/6.57  
% 47.45/6.57  fof(f90,plain,(
% 47.45/6.57    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f51])).
% 47.45/6.57  
% 47.45/6.57  fof(f9,axiom,(
% 47.45/6.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f37,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 47.45/6.57    inference(ennf_transformation,[],[f9])).
% 47.45/6.57  
% 47.45/6.57  fof(f38,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.57    inference(flattening,[],[f37])).
% 47.45/6.57  
% 47.45/6.57  fof(f76,plain,(
% 47.45/6.57    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.57    inference(cnf_transformation,[],[f38])).
% 47.45/6.57  
% 47.45/6.57  fof(f5,axiom,(
% 47.45/6.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f31,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 47.45/6.57    inference(ennf_transformation,[],[f5])).
% 47.45/6.57  
% 47.45/6.57  fof(f32,plain,(
% 47.45/6.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 47.45/6.57    inference(flattening,[],[f31])).
% 47.45/6.57  
% 47.45/6.57  fof(f72,plain,(
% 47.45/6.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 47.45/6.57    inference(cnf_transformation,[],[f32])).
% 47.45/6.57  
% 47.45/6.57  fof(f2,axiom,(
% 47.45/6.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f69,plain,(
% 47.45/6.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f2])).
% 47.45/6.57  
% 47.45/6.57  fof(f15,axiom,(
% 47.45/6.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f44,plain,(
% 47.45/6.57    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(ennf_transformation,[],[f15])).
% 47.45/6.57  
% 47.45/6.57  fof(f82,plain,(
% 47.45/6.57    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f44])).
% 47.45/6.57  
% 47.45/6.57  fof(f11,axiom,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f41,plain,(
% 47.45/6.57    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.57    inference(ennf_transformation,[],[f11])).
% 47.45/6.57  
% 47.45/6.57  fof(f57,plain,(
% 47.45/6.57    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.57    inference(nnf_transformation,[],[f41])).
% 47.45/6.57  
% 47.45/6.57  fof(f78,plain,(
% 47.45/6.57    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.57    inference(cnf_transformation,[],[f57])).
% 47.45/6.57  
% 47.45/6.57  fof(f79,plain,(
% 47.45/6.57    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.57    inference(cnf_transformation,[],[f57])).
% 47.45/6.57  
% 47.45/6.57  fof(f14,axiom,(
% 47.45/6.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 47.45/6.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.57  
% 47.45/6.57  fof(f42,plain,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 47.45/6.57    inference(ennf_transformation,[],[f14])).
% 47.45/6.57  
% 47.45/6.57  fof(f43,plain,(
% 47.45/6.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 47.45/6.57    inference(flattening,[],[f42])).
% 47.45/6.57  
% 47.45/6.57  fof(f81,plain,(
% 47.45/6.57    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.45/6.57    inference(cnf_transformation,[],[f43])).
% 47.45/6.57  
% 47.45/6.57  fof(f97,plain,(
% 47.45/6.57    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 47.45/6.57    inference(cnf_transformation,[],[f65])).
% 47.45/6.57  
% 47.45/6.57  cnf(c_30,negated_conjecture,
% 47.45/6.57      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.45/6.57      inference(cnf_transformation,[],[f95]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1631,plain,
% 47.45/6.57      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_8,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.57      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 47.45/6.57      inference(cnf_transformation,[],[f74]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1638,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.45/6.57      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_23,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f89]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_31,negated_conjecture,
% 47.45/6.57      ( l1_pre_topc(sK0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f94]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_551,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_552,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_551]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1628,plain,
% 47.45/6.57      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2033,plain,
% 47.45/6.57      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1631,c_1628]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_21,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f87]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_575,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_576,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_575]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1626,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2043,plain,
% 47.45/6.57      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 47.45/6.57      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_2033,c_1626]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_33,plain,
% 47.45/6.57      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_577,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_579,plain,
% 47.45/6.57      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 47.45/6.57      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_577]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3560,plain,
% 47.45/6.57      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.45/6.57      inference(global_propositional_subsumption,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_2043,c_33,c_579]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_7,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.57      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.45/6.57      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f73]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1639,plain,
% 47.45/6.57      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 47.45/6.57      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 47.45/6.57      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4324,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_3560,c_1639]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_51944,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,sK1))
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1638,c_4324]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_174248,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1631,c_51944]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_29,negated_conjecture,
% 47.45/6.57      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(cnf_transformation,[],[f96]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_247,plain,
% 47.45/6.57      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(prop_impl,[status(thm)],[c_29]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_18,plain,
% 47.45/6.57      ( ~ v1_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f83]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_20,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f85]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_434,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X3)
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | X1 != X3
% 47.45/6.57      | k2_pre_topc(X3,X2) = k2_struct_0(X3)
% 47.45/6.57      | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_435,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_434]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_449,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 47.45/6.57      inference(forward_subsumption_resolution,[status(thm)],[c_435,c_8]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_467,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_449,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_468,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,sK0)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_467]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_693,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 47.45/6.57      | sK0 != sK0
% 47.45/6.57      | sK1 != X0 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_247,c_468]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_694,plain,
% 47.45/6.57      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_693]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_854,plain,
% 47.45/6.57      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(prop_impl,[status(thm)],[c_30,c_694]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1620,plain,
% 47.45/6.57      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_0,plain,
% 47.45/6.57      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 47.45/6.57      inference(cnf_transformation,[],[f68]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1645,plain,
% 47.45/6.57      ( X0 = X1
% 47.45/6.57      | r1_tarski(X0,X1) != iProver_top
% 47.45/6.57      | r1_tarski(X1,X0) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3185,plain,
% 47.45/6.57      ( k2_tops_1(sK0,sK1) = sK1
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 47.45/6.57      | r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1620,c_1645]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_26,plain,
% 47.45/6.57      ( v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 47.45/6.57      inference(cnf_transformation,[],[f93]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_512,plain,
% 47.45/6.57      ( v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | k1_tops_1(X1,X0) != k1_xboole_0
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_513,plain,
% 47.45/6.57      ( v2_tops_1(X0,sK0)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_512]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_650,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k1_tops_1(sK0,X0) != k1_xboole_0
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(resolution,[status(thm)],[c_513,c_468]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_652,plain,
% 47.45/6.57      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 47.45/6.57      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_650]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_22,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | r1_tarski(k1_tops_1(X1,X0),X0)
% 47.45/6.57      | ~ l1_pre_topc(X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f88]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_563,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | r1_tarski(k1_tops_1(X1,X0),X0)
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_564,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_563]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1627,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1700,plain,
% 47.45/6.57      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1631,c_1627]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5,plain,
% 47.45/6.57      ( ~ r1_xboole_0(X0,X1)
% 47.45/6.57      | ~ r1_tarski(X2,X0)
% 47.45/6.57      | ~ r1_tarski(X2,X1)
% 47.45/6.57      | k1_xboole_0 = X2 ),
% 47.45/6.57      inference(cnf_transformation,[],[f71]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1641,plain,
% 47.45/6.57      ( k1_xboole_0 = X0
% 47.45/6.57      | r1_xboole_0(X1,X2) != iProver_top
% 47.45/6.57      | r1_tarski(X0,X1) != iProver_top
% 47.45/6.57      | r1_tarski(X0,X2) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3988,plain,
% 47.45/6.57      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 47.45/6.57      | r1_xboole_0(X0,sK1) != iProver_top
% 47.45/6.57      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1700,c_1641]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5403,plain,
% 47.45/6.57      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 47.45/6.57      | r1_xboole_0(sK1,sK1) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1700,c_3988]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_25,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 47.45/6.57      | ~ l1_pre_topc(X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f91]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_527,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_528,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_527]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_530,plain,
% 47.45/6.57      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_528]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_27,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 47.45/6.57      inference(cnf_transformation,[],[f92]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_497,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,X1)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | k1_tops_1(X1,X0) = k1_xboole_0
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_498,plain,
% 47.45/6.57      ( ~ v2_tops_1(X0,sK0)
% 47.45/6.57      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_497]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_679,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k1_tops_1(sK0,X0) = k1_xboole_0
% 47.45/6.57      | sK0 != sK0
% 47.45/6.57      | sK1 != X0 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_247,c_498]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_680,plain,
% 47.45/6.57      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_679]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_682,plain,
% 47.45/6.57      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 47.45/6.57      inference(global_propositional_subsumption,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_680,c_30]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4,plain,
% 47.45/6.57      ( ~ r1_xboole_0(X0,X1)
% 47.45/6.57      | r1_xboole_0(X2,X3)
% 47.45/6.57      | ~ r1_tarski(X2,X0)
% 47.45/6.57      | ~ r1_tarski(X3,X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f70]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1778,plain,
% 47.45/6.57      ( ~ r1_xboole_0(X0,X1)
% 47.45/6.57      | r1_xboole_0(k1_tops_1(sK0,X2),X3)
% 47.45/6.57      | ~ r1_tarski(X3,X1)
% 47.45/6.57      | ~ r1_tarski(k1_tops_1(sK0,X2),X0) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_4]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2086,plain,
% 47.45/6.57      ( r1_xboole_0(k1_tops_1(sK0,X0),X1)
% 47.45/6.57      | ~ r1_xboole_0(k1_tops_1(sK0,X2),k2_tops_1(sK0,X2))
% 47.45/6.57      | ~ r1_tarski(X1,k2_tops_1(sK0,X2))
% 47.45/6.57      | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X2)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1778]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2088,plain,
% 47.45/6.57      ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
% 47.45/6.57      | r1_xboole_0(k1_tops_1(sK0,sK1),sK1)
% 47.45/6.57      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 47.45/6.57      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_2086]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2,plain,
% 47.45/6.57      ( r1_tarski(X0,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f99]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2339,plain,
% 47.45/6.57      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X0)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_2]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2341,plain,
% 47.45/6.57      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_2339]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1644,plain,
% 47.45/6.57      ( r1_tarski(X0,X0) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5402,plain,
% 47.45/6.57      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 47.45/6.57      | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1644,c_3988]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5404,plain,
% 47.45/6.57      ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),sK1)
% 47.45/6.57      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 47.45/6.57      inference(predicate_to_equality_rev,[status(thm)],[c_5402]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5407,plain,
% 47.45/6.57      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 47.45/6.57      inference(global_propositional_subsumption,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_5403,c_30,c_530,c_682,c_2088,c_2341,c_5404]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_15438,plain,
% 47.45/6.57      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(global_propositional_subsumption,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_3185,c_30,c_530,c_652,c_682,c_2088,c_2341,c_5404]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_24,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f90]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_539,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_540,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_539]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1629,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2995,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1638,c_1629]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_13150,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1631,c_2995]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_13157,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 47.45/6.57      inference(light_normalisation,[status(thm)],[c_13150,c_2033]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_15440,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(demodulation,[status(thm)],[c_15438,c_13157]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_10,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.57      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.45/6.57      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f76]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1636,plain,
% 47.45/6.57      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 47.45/6.57      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 47.45/6.57      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3961,plain,
% 47.45/6.57      ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k2_xboole_0(X1,k3_subset_1(X0,X2))
% 47.45/6.57      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 47.45/6.57      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1638,c_1636]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_135465,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1631,c_3961]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_135752,plain,
% 47.45/6.57      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_3560,c_135465]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_174267,plain,
% 47.45/6.57      ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(light_normalisation,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_174248,c_15440,c_135752]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_6,plain,
% 47.45/6.57      ( ~ r1_xboole_0(X0,X1)
% 47.45/6.57      | r1_tarski(X0,X2)
% 47.45/6.57      | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 47.45/6.57      inference(cnf_transformation,[],[f72]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1640,plain,
% 47.45/6.57      ( r1_xboole_0(X0,X1) != iProver_top
% 47.45/6.57      | r1_tarski(X0,X2) = iProver_top
% 47.45/6.57      | r1_tarski(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_174491,plain,
% 47.45/6.57      ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 47.45/6.57      | r1_tarski(X0,k2_tops_1(sK0,sK1)) = iProver_top
% 47.45/6.57      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_174267,c_1640]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_174495,plain,
% 47.45/6.57      ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 47.45/6.57      | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_174491]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3,plain,
% 47.45/6.57      ( r1_tarski(k1_xboole_0,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f69]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_32223,plain,
% 47.45/6.57      ( r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_3]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_32224,plain,
% 47.45/6.57      ( r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_32223]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1884,plain,
% 47.45/6.57      ( r1_xboole_0(X0,X1)
% 47.45/6.57      | ~ r1_xboole_0(X2,k3_subset_1(X3,X4))
% 47.45/6.57      | ~ r1_tarski(X0,X2)
% 47.45/6.57      | ~ r1_tarski(X1,k3_subset_1(X3,X4)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_4]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_7567,plain,
% 47.45/6.57      ( r1_xboole_0(X0,X1)
% 47.45/6.57      | ~ r1_xboole_0(X2,k3_subset_1(u1_struct_0(sK0),sK1))
% 47.45/6.57      | ~ r1_tarski(X0,X2)
% 47.45/6.57      | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1884]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_16309,plain,
% 47.45/6.57      ( ~ r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
% 47.45/6.57      | r1_xboole_0(X1,k1_xboole_0)
% 47.45/6.57      | ~ r1_tarski(X1,X0)
% 47.45/6.57      | ~ r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_7567]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_16310,plain,
% 47.45/6.57      ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 47.45/6.57      | r1_xboole_0(X1,k1_xboole_0) = iProver_top
% 47.45/6.57      | r1_tarski(X1,X0) != iProver_top
% 47.45/6.57      | r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_16309]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_16312,plain,
% 47.45/6.57      ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 47.45/6.57      | r1_xboole_0(sK1,k1_xboole_0) = iProver_top
% 47.45/6.57      | r1_tarski(sK1,sK1) != iProver_top
% 47.45/6.57      | r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_16310]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1009,plain,
% 47.45/6.57      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.45/6.57      theory(equality) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1999,plain,
% 47.45/6.57      ( ~ r1_tarski(X0,X1)
% 47.45/6.57      | r1_tarski(X2,k2_struct_0(sK0))
% 47.45/6.57      | X2 != X0
% 47.45/6.57      | k2_struct_0(sK0) != X1 ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1009]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_8708,plain,
% 47.45/6.57      ( ~ r1_tarski(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)))
% 47.45/6.57      | r1_tarski(X2,k2_struct_0(sK0))
% 47.45/6.57      | X2 != X0
% 47.45/6.57      | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1999]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_8718,plain,
% 47.45/6.57      ( X0 != X1
% 47.45/6.57      | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2))
% 47.45/6.57      | r1_tarski(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2))) != iProver_top
% 47.45/6.57      | r1_tarski(X0,k2_struct_0(sK0)) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_8708]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_8720,plain,
% 47.45/6.57      ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 47.45/6.57      | sK1 != sK1
% 47.45/6.57      | r1_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top
% 47.45/6.57      | r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_8718]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_16,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1)
% 47.45/6.57      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f82]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_587,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_588,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_587]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1625,plain,
% 47.45/6.57      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 47.45/6.57      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2523,plain,
% 47.45/6.57      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_1631,c_1625]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5411,plain,
% 47.45/6.57      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 47.45/6.57      inference(demodulation,[status(thm)],[c_5407,c_2523]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_13,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.57      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.45/6.57      | ~ r1_xboole_0(X2,k3_subset_1(X1,X0))
% 47.45/6.57      | r1_tarski(X2,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f78]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1633,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.45/6.57      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 47.45/6.57      | r1_xboole_0(X2,k3_subset_1(X1,X0)) != iProver_top
% 47.45/6.57      | r1_tarski(X2,X0) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5542,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 47.45/6.57      | r1_tarski(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top ),
% 47.45/6.57      inference(superposition,[status(thm)],[c_5411,c_1633]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_5552,plain,
% 47.45/6.57      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | r1_xboole_0(sK1,k1_xboole_0) != iProver_top
% 47.45/6.57      | r1_tarski(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_5542]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_12,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.57      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.45/6.57      | r1_xboole_0(X2,k3_subset_1(X1,X0))
% 47.45/6.57      | ~ r1_tarski(X2,X0) ),
% 47.45/6.57      inference(cnf_transformation,[],[f79]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4503,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
% 47.45/6.57      | ~ r1_tarski(X0,sK1) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_12]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4504,plain,
% 47.45/6.57      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
% 47.45/6.57      | r1_tarski(X0,sK1) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_4503]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4506,plain,
% 47.45/6.57      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 47.45/6.57      | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
% 47.45/6.57      | r1_tarski(sK1,sK1) != iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_4504]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4483,plain,
% 47.45/6.57      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_8]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_4484,plain,
% 47.45/6.57      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 47.45/6.57      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_4483]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1008,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1769,plain,
% 47.45/6.57      ( X0 != X1 | k2_struct_0(sK0) != X1 | k2_struct_0(sK0) = X0 ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1008]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2015,plain,
% 47.45/6.57      ( X0 != k2_struct_0(sK0)
% 47.45/6.57      | k2_struct_0(sK0) = X0
% 47.45/6.57      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1769]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3157,plain,
% 47.45/6.57      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) != k2_struct_0(sK0)
% 47.45/6.57      | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 47.45/6.57      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_2015]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_3158,plain,
% 47.45/6.57      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
% 47.45/6.57      | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 47.45/6.57      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_3157]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_15,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | ~ l1_pre_topc(X1) ),
% 47.45/6.57      inference(cnf_transformation,[],[f81]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_599,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.45/6.57      | sK0 != X1 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_600,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_599]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2965,plain,
% 47.45/6.57      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_600]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2966,plain,
% 47.45/6.57      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 47.45/6.57      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_2965]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2968,plain,
% 47.45/6.57      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 47.45/6.57      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_2966]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_1007,plain,( X0 = X0 ),theory(equality) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_2047,plain,
% 47.45/6.57      ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_1007]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_28,negated_conjecture,
% 47.45/6.57      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(cnf_transformation,[],[f97]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_245,plain,
% 47.45/6.57      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 47.45/6.57      inference(prop_impl,[status(thm)],[c_28]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_707,plain,
% 47.45/6.57      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k1_tops_1(sK0,X0) != k1_xboole_0
% 47.45/6.57      | sK0 != sK0
% 47.45/6.57      | sK1 != X0 ),
% 47.45/6.57      inference(resolution_lifted,[status(thm)],[c_245,c_513]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_708,plain,
% 47.45/6.57      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.45/6.57      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 47.45/6.57      inference(unflattening,[status(thm)],[c_707]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_710,plain,
% 47.45/6.57      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 47.45/6.57      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 47.45/6.57      inference(global_propositional_subsumption,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_708,c_30]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_712,plain,
% 47.45/6.57      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 47.45/6.57      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_112,plain,
% 47.45/6.57      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_0]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_107,plain,
% 47.45/6.57      ( r1_tarski(X0,X0) = iProver_top ),
% 47.45/6.57      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_109,plain,
% 47.45/6.57      ( r1_tarski(sK1,sK1) = iProver_top ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_107]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(c_108,plain,
% 47.45/6.57      ( r1_tarski(sK1,sK1) ),
% 47.45/6.57      inference(instantiation,[status(thm)],[c_2]) ).
% 47.45/6.57  
% 47.45/6.57  cnf(contradiction,plain,
% 47.45/6.57      ( $false ),
% 47.45/6.57      inference(minisat,
% 47.45/6.57                [status(thm)],
% 47.45/6.57                [c_174495,c_32224,c_16312,c_8720,c_5552,c_5407,c_4506,
% 47.45/6.57                 c_4484,c_3158,c_2968,c_2047,c_712,c_652,c_112,c_109,
% 47.45/6.57                 c_108,c_33,c_30]) ).
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  % SZS output end CNFRefutation for theBenchmark.p
% 47.45/6.57  
% 47.45/6.57  ------                               Statistics
% 47.45/6.57  
% 47.45/6.57  ------ General
% 47.45/6.57  
% 47.45/6.57  abstr_ref_over_cycles:                  0
% 47.45/6.57  abstr_ref_under_cycles:                 0
% 47.45/6.57  gc_basic_clause_elim:                   0
% 47.45/6.57  forced_gc_time:                         0
% 47.45/6.57  parsing_time:                           0.037
% 47.45/6.57  unif_index_cands_time:                  0.
% 47.45/6.57  unif_index_add_time:                    0.
% 47.45/6.57  orderings_time:                         0.
% 47.45/6.57  out_proof_time:                         0.024
% 47.45/6.57  total_time:                             5.654
% 47.45/6.57  num_of_symbols:                         49
% 47.45/6.57  num_of_terms:                           163233
% 47.45/6.57  
% 47.45/6.57  ------ Preprocessing
% 47.45/6.57  
% 47.45/6.57  num_of_splits:                          0
% 47.45/6.57  num_of_split_atoms:                     0
% 47.45/6.57  num_of_reused_defs:                     0
% 47.45/6.57  num_eq_ax_congr_red:                    14
% 47.45/6.57  num_of_sem_filtered_clauses:            1
% 47.45/6.57  num_of_subtypes:                        0
% 47.45/6.57  monotx_restored_types:                  0
% 47.45/6.57  sat_num_of_epr_types:                   0
% 47.45/6.57  sat_num_of_non_cyclic_types:            0
% 47.45/6.57  sat_guarded_non_collapsed_types:        0
% 47.45/6.57  num_pure_diseq_elim:                    0
% 47.45/6.57  simp_replaced_by:                       0
% 47.45/6.57  res_preprocessed:                       142
% 47.45/6.57  prep_upred:                             0
% 47.45/6.57  prep_unflattend:                        19
% 47.45/6.57  smt_new_axioms:                         0
% 47.45/6.57  pred_elim_cands:                        3
% 47.45/6.57  pred_elim:                              3
% 47.45/6.57  pred_elim_cl:                           3
% 47.45/6.57  pred_elim_cycles:                       5
% 47.45/6.57  merged_defs:                            14
% 47.45/6.57  merged_defs_ncl:                        0
% 47.45/6.57  bin_hyper_res:                          14
% 47.45/6.57  prep_cycles:                            4
% 47.45/6.57  pred_elim_time:                         0.012
% 47.45/6.57  splitting_time:                         0.
% 47.45/6.57  sem_filter_time:                        0.
% 47.45/6.57  monotx_time:                            0.033
% 47.45/6.57  subtype_inf_time:                       0.
% 47.45/6.57  
% 47.45/6.57  ------ Problem properties
% 47.45/6.57  
% 47.45/6.57  clauses:                                28
% 47.45/6.57  conjectures:                            1
% 47.45/6.57  epr:                                    5
% 47.45/6.57  horn:                                   26
% 47.45/6.57  ground:                                 5
% 47.45/6.57  unary:                                  4
% 47.45/6.57  binary:                                 13
% 47.45/6.57  lits:                                   68
% 47.45/6.57  lits_eq:                                16
% 47.45/6.57  fd_pure:                                0
% 47.45/6.57  fd_pseudo:                              0
% 47.45/6.57  fd_cond:                                1
% 47.45/6.57  fd_pseudo_cond:                         1
% 47.45/6.57  ac_symbols:                             0
% 47.45/6.57  
% 47.45/6.57  ------ Propositional Solver
% 47.45/6.57  
% 47.45/6.57  prop_solver_calls:                      69
% 47.45/6.57  prop_fast_solver_calls:                 3204
% 47.45/6.57  smt_solver_calls:                       0
% 47.45/6.57  smt_fast_solver_calls:                  0
% 47.45/6.57  prop_num_of_clauses:                    68626
% 47.45/6.57  prop_preprocess_simplified:             128555
% 47.45/6.57  prop_fo_subsumed:                       80
% 47.45/6.57  prop_solver_time:                       0.
% 47.45/6.57  smt_solver_time:                        0.
% 47.45/6.57  smt_fast_solver_time:                   0.
% 47.45/6.57  prop_fast_solver_time:                  0.
% 47.45/6.57  prop_unsat_core_time:                   0.008
% 47.45/6.57  
% 47.45/6.57  ------ QBF
% 47.45/6.57  
% 47.45/6.57  qbf_q_res:                              0
% 47.45/6.57  qbf_num_tautologies:                    0
% 47.45/6.57  qbf_prep_cycles:                        0
% 47.45/6.57  
% 47.45/6.57  ------ BMC1
% 47.45/6.57  
% 47.45/6.57  bmc1_current_bound:                     -1
% 47.45/6.57  bmc1_last_solved_bound:                 -1
% 47.45/6.57  bmc1_unsat_core_size:                   -1
% 47.45/6.57  bmc1_unsat_core_parents_size:           -1
% 47.45/6.57  bmc1_merge_next_fun:                    0
% 47.45/6.57  bmc1_unsat_core_clauses_time:           0.
% 47.45/6.57  
% 47.45/6.57  ------ Instantiation
% 47.45/6.57  
% 47.45/6.57  inst_num_of_clauses:                    7948
% 47.45/6.57  inst_num_in_passive:                    3669
% 47.45/6.57  inst_num_in_active:                     5549
% 47.45/6.57  inst_num_in_unprocessed:                1496
% 47.45/6.57  inst_num_of_loops:                      5819
% 47.45/6.57  inst_num_of_learning_restarts:          1
% 47.45/6.57  inst_num_moves_active_passive:          264
% 47.45/6.57  inst_lit_activity:                      0
% 47.45/6.57  inst_lit_activity_moves:                0
% 47.45/6.57  inst_num_tautologies:                   0
% 47.45/6.57  inst_num_prop_implied:                  0
% 47.45/6.57  inst_num_existing_simplified:           0
% 47.45/6.57  inst_num_eq_res_simplified:             0
% 47.45/6.57  inst_num_child_elim:                    0
% 47.45/6.57  inst_num_of_dismatching_blockings:      32343
% 47.45/6.57  inst_num_of_non_proper_insts:           24273
% 47.45/6.57  inst_num_of_duplicates:                 0
% 47.45/6.57  inst_inst_num_from_inst_to_res:         0
% 47.45/6.57  inst_dismatching_checking_time:         0.
% 47.45/6.57  
% 47.45/6.57  ------ Resolution
% 47.45/6.57  
% 47.45/6.57  res_num_of_clauses:                     41
% 47.45/6.57  res_num_in_passive:                     41
% 47.45/6.57  res_num_in_active:                      0
% 47.45/6.57  res_num_of_loops:                       146
% 47.45/6.57  res_forward_subset_subsumed:            1465
% 47.45/6.57  res_backward_subset_subsumed:           30
% 47.45/6.57  res_forward_subsumed:                   0
% 47.45/6.57  res_backward_subsumed:                  0
% 47.45/6.57  res_forward_subsumption_resolution:     2
% 47.45/6.57  res_backward_subsumption_resolution:    0
% 47.45/6.57  res_clause_to_clause_subsumption:       29951
% 47.45/6.57  res_orphan_elimination:                 0
% 47.45/6.57  res_tautology_del:                      1066
% 47.45/6.57  res_num_eq_res_simplified:              0
% 47.45/6.57  res_num_sel_changes:                    0
% 47.45/6.57  res_moves_from_active_to_pass:          0
% 47.45/6.57  
% 47.45/6.57  ------ Superposition
% 47.45/6.57  
% 47.45/6.57  sup_time_total:                         0.
% 47.45/6.57  sup_time_generating:                    0.
% 47.45/6.57  sup_time_sim_full:                      0.
% 47.45/6.57  sup_time_sim_immed:                     0.
% 47.45/6.57  
% 47.45/6.57  sup_num_of_clauses:                     8026
% 47.45/6.57  sup_num_in_active:                      1131
% 47.45/6.57  sup_num_in_passive:                     6895
% 47.45/6.57  sup_num_of_loops:                       1162
% 47.45/6.57  sup_fw_superposition:                   7763
% 47.45/6.57  sup_bw_superposition:                   2639
% 47.45/6.57  sup_immediate_simplified:               3005
% 47.45/6.57  sup_given_eliminated:                   0
% 47.45/6.57  comparisons_done:                       0
% 47.45/6.57  comparisons_avoided:                    0
% 47.45/6.57  
% 47.45/6.57  ------ Simplifications
% 47.45/6.57  
% 47.45/6.57  
% 47.45/6.57  sim_fw_subset_subsumed:                 88
% 47.45/6.57  sim_bw_subset_subsumed:                 21
% 47.45/6.57  sim_fw_subsumed:                        191
% 47.45/6.57  sim_bw_subsumed:                        13
% 47.45/6.57  sim_fw_subsumption_res:                 0
% 47.45/6.57  sim_bw_subsumption_res:                 0
% 47.45/6.57  sim_tautology_del:                      27
% 47.45/6.57  sim_eq_tautology_del:                   746
% 47.45/6.57  sim_eq_res_simp:                        2
% 47.45/6.57  sim_fw_demodulated:                     342
% 47.45/6.57  sim_bw_demodulated:                     146
% 47.45/6.57  sim_light_normalised:                   2368
% 47.45/6.57  sim_joinable_taut:                      0
% 47.45/6.57  sim_joinable_simp:                      0
% 47.45/6.57  sim_ac_normalised:                      0
% 47.45/6.57  sim_smt_subsumption:                    0
% 47.45/6.57  
%------------------------------------------------------------------------------
