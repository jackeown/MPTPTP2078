%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:19 EST 2020

% Result     : Theorem 43.37s
% Output     : CNFRefutation 43.37s
% Verified   : 
% Statistics : Number of formulae       :  355 (2625 expanded)
%              Number of clauses        :  279 (1019 expanded)
%              Number of leaves         :   24 ( 548 expanded)
%              Depth                    :   35
%              Number of atoms          : 1046 (8137 expanded)
%              Number of equality atoms :  507 (1561 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
        & v3_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f57,f56])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_tops_1(X0,X1) != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_14,c_12])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40862,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X0))
    | r1_tarski(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_31310,c_3])).

cnf(c_570,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_575,plain,
    ( X0 != X1
    | k2_pre_topc(X2,X0) = k2_pre_topc(X2,X1) ),
    theory(equality)).

cnf(c_31406,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(X1,X2))
    | r1_tarski(X3,k2_pre_topc(X1,X4))
    | X3 != X0
    | X4 != X2 ),
    inference(resolution,[status(thm)],[c_570,c_575])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_29893,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_16,c_30])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7659,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_30133,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29893,c_31,c_30,c_7659])).

cnf(c_62121,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X1))
    | X0 != sK1
    | X1 != sK1 ),
    inference(resolution,[status(thm)],[c_31406,c_30133])).

cnf(c_156551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | X0 != sK1
    | X1 != sK1 ),
    inference(resolution,[status(thm)],[c_40862,c_62121])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3779,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4281,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_5656,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4281])).

cnf(c_5657,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5656])).

cnf(c_5702,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,sK1)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_5657])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5731,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7541,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7546,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7860,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7541,c_7546])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7548,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7971,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_7860,c_7548])).

cnf(c_7542,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7549,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8080,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7542,c_7549])).

cnf(c_8504,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7971,c_8080])).

cnf(c_8513,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8504])).

cnf(c_22791,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_270,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_217])).

cnf(c_29584,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(X0),X1),k1_zfmisc_1(k2_struct_0(X0)))
    | ~ r1_tarski(X1,k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_45413,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_29584])).

cnf(c_55301,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X3),X4)
    | X4 != X1
    | k1_tops_1(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_55832,plain,
    ( ~ r1_tarski(k1_tops_1(X0,X1),X2)
    | r1_tarski(k1_tops_1(X0,X1),X3)
    | X3 != X2
    | k1_tops_1(X0,X1) != k1_tops_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_55301])).

cnf(c_55833,plain,
    ( ~ r1_tarski(k1_tops_1(X0,X1),X2)
    | r1_tarski(k1_tops_1(X0,X1),X3)
    | X3 != X2 ),
    inference(equality_resolution_simp,[status(thm)],[c_55832])).

cnf(c_56407,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_55833])).

cnf(c_16881,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16894,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17418,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16881,c_16894])).

cnf(c_16896,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17593,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_17418,c_16896])).

cnf(c_16901,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_217])).

cnf(c_16879,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_22701,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_16901,c_16879])).

cnf(c_20,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_16889,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22863,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),X0) = iProver_top
    | v1_tops_1(u1_struct_0(X0),X0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22701,c_16889])).

cnf(c_2941,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2946,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_2947,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2946])).

cnf(c_2977,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2978,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2977])).

cnf(c_3862,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X1,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_3934,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3862])).

cnf(c_3935,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3934])).

cnf(c_569,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8105,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_569,c_0])).

cnf(c_9098,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X0)
    | ~ l1_struct_0(X1)
    | X0 = u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_8105,c_13])).

cnf(c_9129,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(X2,k2_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),X0)
    | ~ r1_tarski(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1)
    | X0 = X2 ),
    inference(resolution,[status(thm)],[c_9098,c_8105])).

cnf(c_9579,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),X0)
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X1))
    | ~ l1_struct_0(X1)
    | X0 = k2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_9129,c_2])).

cnf(c_9593,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),X0)
    | ~ l1_struct_0(X1)
    | X0 = k2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9579,c_2])).

cnf(c_18,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9672,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_9593,c_18])).

cnf(c_8239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_14,c_12])).

cnf(c_10051,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9672,c_8239])).

cnf(c_10052,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_10051])).

cnf(c_10062,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10052,c_15])).

cnf(c_7984,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_16,c_11])).

cnf(c_10205,plain,
    ( v1_tops_1(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_10062,c_7984])).

cnf(c_10206,plain,
    ( v1_tops_1(u1_struct_0(X0),X0) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10205])).

cnf(c_143571,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22863,c_2947,c_2978,c_3935,c_10206])).

cnf(c_143579,plain,
    ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_143571])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8144,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8145,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8144])).

cnf(c_8147,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8145])).

cnf(c_8054,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_struct_0(X0),X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8543,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_8054])).

cnf(c_8544,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0))) = iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8543])).

cnf(c_8546,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8544])).

cnf(c_7547,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8878,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7971,c_7547])).

cnf(c_8896,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8878,c_7971])).

cnf(c_9207,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8896,c_32])).

cnf(c_9208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9207])).

cnf(c_9215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9208,c_7549])).

cnf(c_7550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7545,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7971,c_7545])).

cnf(c_9065,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8516,c_32])).

cnf(c_9066,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9065])).

cnf(c_9074,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7550,c_9066])).

cnf(c_7553,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9234,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9074,c_7553])).

cnf(c_9558,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0)
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9215,c_9234])).

cnf(c_10165,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9558,c_8147,c_8546])).

cnf(c_7544,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10168,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10165,c_7544])).

cnf(c_10190,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10168,c_7971])).

cnf(c_21561,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_16889])).

cnf(c_21566,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21561,c_17593])).

cnf(c_22207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21566,c_32])).

cnf(c_22208,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22207])).

cnf(c_22866,plain,
    ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) = iProver_top
    | v1_tops_1(k2_struct_0(sK0),sK0) != iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22701,c_22208])).

cnf(c_42070,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0)))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_29584])).

cnf(c_42071,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0))) = iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42070])).

cnf(c_42073,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42071])).

cnf(c_146028,plain,
    ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_143579,c_32,c_8147,c_8546,c_10190,c_22866,c_42073])).

cnf(c_16880,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_27,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16884,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20041,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_16884])).

cnf(c_20715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v2_tops_1(X0,sK0) != iProver_top
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20041,c_32])).

cnf(c_20716,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20715])).

cnf(c_23982,plain,
    ( k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k1_xboole_0
    | v2_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16880,c_20716])).

cnf(c_146033,plain,
    ( k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) = k1_xboole_0
    | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_146028,c_23982])).

cnf(c_148557,plain,
    ( k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_146033,c_8147])).

cnf(c_16898,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_16886,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16882,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(k2_pre_topc(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16475,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ arAF0_v3_tops_1_0_1(X1)
    | ~ l1_pre_topc(X0)
    | ~ iProver_ARSWP_105 ),
    inference(arg_filter_abstr,[status(unp)],[c_23])).

cnf(c_16868,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | arAF0_v3_tops_1_0_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16475])).

cnf(c_17569,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | arAF0_v3_tops_1_0_1(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_105 != iProver_top ),
    inference(superposition,[status(thm)],[c_16882,c_16868])).

cnf(c_33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_34,plain,
    ( v3_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1320,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1321,plain,
    ( v3_tops_1(sK1,sK0) != iProver_top
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_18048,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17569,c_32,c_33,c_34,c_1321])).

cnf(c_16895,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18966,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_16895])).

cnf(c_19013,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18966,c_17593])).

cnf(c_20507,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19013,c_32,c_8896])).

cnf(c_20508,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_20507])).

cnf(c_20727,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_xboole_0
    | v2_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20508,c_20716])).

cnf(c_35856,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18048,c_20727])).

cnf(c_7691,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17453,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_35924,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35856,c_31,c_30,c_29,c_1320,c_7691,c_17453])).

cnf(c_18056,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17593,c_16882])).

cnf(c_16900,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X2),X3) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16886,c_16900])).

cnf(c_77471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_21677])).

cnf(c_77478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_77471,c_17593])).

cnf(c_78653,plain,
    ( r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_77478,c_32])).

cnf(c_78654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top ),
    inference(renaming,[status(thm)],[c_78653])).

cnf(c_78665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18056,c_78654])).

cnf(c_78742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16886,c_78665])).

cnf(c_78864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78742,c_17593])).

cnf(c_8506,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7971,c_7542])).

cnf(c_111339,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_78864,c_32,c_8506])).

cnf(c_111340,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_111339])).

cnf(c_111349,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35924,c_111340])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_79,plain,
    ( ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_7660,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7659])).

cnf(c_7692,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7691])).

cnf(c_7701,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7784,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7701])).

cnf(c_7785,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7784])).

cnf(c_17638,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_struct_0(X3))
    | X2 != X0
    | k2_struct_0(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_18138,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | r1_tarski(X2,k2_struct_0(X1))
    | X2 != X0
    | k2_struct_0(X1) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_17638])).

cnf(c_18139,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | r1_tarski(X2,k2_struct_0(X1))
    | X2 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_18138])).

cnf(c_18922,plain,
    ( r1_tarski(X0,k2_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X1))
    | X0 != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_18139])).

cnf(c_19513,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(X0))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X0))
    | u1_struct_0(X0) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_18922])).

cnf(c_19514,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) = iProver_top
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19513])).

cnf(c_19516,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) = iProver_top
    | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19514])).

cnf(c_27858,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_struct_0(X2))
    | r1_tarski(X0,k2_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_31871,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | r1_tarski(X0,k2_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_27858])).

cnf(c_45336,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_31871])).

cnf(c_45337,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) = iProver_top
    | r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45336])).

cnf(c_28318,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_81644,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_28318])).

cnf(c_81653,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81644])).

cnf(c_113597,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_111349,c_31,c_32,c_33,c_73,c_79,c_7660,c_7692,c_7785,c_8147,c_19516,c_45337,c_81653])).

cnf(c_113598,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_113597])).

cnf(c_113608,plain,
    ( r1_tarski(X0,k2_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16898,c_113598])).

cnf(c_45430,plain,
    ( r1_tarski(X0,k2_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_27858])).

cnf(c_45431,plain,
    ( r1_tarski(X0,k2_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45430])).

cnf(c_118345,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_113608,c_8504,c_45431])).

cnf(c_118362,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_118345,c_16900])).

cnf(c_16902,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_120824,plain,
    ( k1_tops_1(sK0,X0) = X1
    | r1_tarski(X1,k1_tops_1(sK0,X0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_118362,c_16902])).

cnf(c_126120,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16886,c_120824])).

cnf(c_126481,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_126120,c_17593])).

cnf(c_4278,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK1)
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4279,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4278])).

cnf(c_78739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16901,c_78665])).

cnf(c_113609,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18056,c_113598])).

cnf(c_5732,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5731])).

cnf(c_114207,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_113609,c_5732])).

cnf(c_114219,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_114207,c_16900])).

cnf(c_114777,plain,
    ( k1_tops_1(sK0,sK1) = X0
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_114219,c_16902])).

cnf(c_28,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_21,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3813,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_26,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4162,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_6249,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_20412,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_20413,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20412])).

cnf(c_22792,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22791])).

cnf(c_23237,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_24577,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23237])).

cnf(c_24578,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_24577])).

cnf(c_24914,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24578])).

cnf(c_25601,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24914])).

cnf(c_25602,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k1_xboole_0
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25601])).

cnf(c_17470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_25855,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17470])).

cnf(c_25856,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25855])).

cnf(c_23229,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_25892,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_23229])).

cnf(c_25893,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25892])).

cnf(c_21782,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | r1_tarski(X0,k1_tops_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_26316,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_21782])).

cnf(c_26317,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26316])).

cnf(c_118071,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_114777,c_31,c_32,c_30,c_33,c_29,c_28,c_1320,c_3813,c_4162,c_6249,c_7660,c_7691,c_7692,c_17453,c_20413,c_22792,c_25602,c_25856,c_25893,c_26317])).

cnf(c_118085,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_78739,c_118071])).

cnf(c_127271,plain,
    ( r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_126481,c_4279,c_118085])).

cnf(c_127272,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_127271])).

cnf(c_127281,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16898,c_127272])).

cnf(c_18863,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_16,c_30])).

cnf(c_19048,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18863,c_31,c_30,c_7659])).

cnf(c_19060,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_19048,c_3])).

cnf(c_19203,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(X1,sK1) ),
    inference(resolution,[status(thm)],[c_19060,c_3])).

cnf(c_19204,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19203])).

cnf(c_81685,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | r1_tarski(X0,k2_struct_0(sK0))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_27858])).

cnf(c_81686,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81685])).

cnf(c_130339,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_127281,c_31,c_32,c_33,c_73,c_79,c_7692,c_7785,c_8147,c_19204,c_19516,c_45337,c_81686])).

cnf(c_148569,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_148557,c_130339])).

cnf(c_148915,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_148569])).

cnf(c_16897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20508,c_16897])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16892,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21390,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17593,c_16892])).

cnf(c_21394,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21390,c_17593])).

cnf(c_21864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21394,c_32])).

cnf(c_21865,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21864])).

cnf(c_21874,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_18056,c_21865])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_217])).

cnf(c_435,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_436,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_490,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_272,c_436])).

cnf(c_16871,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_22861,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X1),X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X1),k3_subset_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22701,c_16871])).

cnf(c_135620,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X1),X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_22861,c_16900])).

cnf(c_155692,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21874,c_135620])).

cnf(c_27852,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X1)))
    | r1_tarski(X0,k2_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_28314,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(X0),X1),k1_zfmisc_1(k2_struct_0(X0)))
    | r1_tarski(k3_subset_1(k2_struct_0(X0),X1),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_27852])).

cnf(c_42115,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0)))
    | r1_tarski(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_28314])).

cnf(c_42116,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k2_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42115])).

cnf(c_42118,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42116])).

cnf(c_156831,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_155692,c_8147,c_42073,c_42118])).

cnf(c_156832,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_156831])).

cnf(c_156840,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20513,c_156832])).

cnf(c_156868,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_156840])).

cnf(c_157031,plain,
    ( X0 != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_156551,c_31,c_30,c_3779,c_5702,c_5731,c_8513,c_22791,c_45413,c_56407,c_148915,c_156868])).

cnf(c_568,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_157423,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_157031,c_568])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:49:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 43.37/6.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.37/6.00  
% 43.37/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.37/6.00  
% 43.37/6.00  ------  iProver source info
% 43.37/6.00  
% 43.37/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.37/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.37/6.00  git: non_committed_changes: false
% 43.37/6.00  git: last_make_outside_of_git: false
% 43.37/6.00  
% 43.37/6.00  ------ 
% 43.37/6.00  ------ Parsing...
% 43.37/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  ------ Proving...
% 43.37/6.00  ------ Problem Properties 
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  clauses                                 31
% 43.37/6.00  conjectures                             4
% 43.37/6.00  EPR                                     6
% 43.37/6.00  Horn                                    31
% 43.37/6.00  unary                                   7
% 43.37/6.00  binary                                  6
% 43.37/6.00  lits                                    85
% 43.37/6.00  lits eq                                 9
% 43.37/6.00  fd_pure                                 0
% 43.37/6.00  fd_pseudo                               0
% 43.37/6.00  fd_cond                                 0
% 43.37/6.00  fd_pseudo_cond                          2
% 43.37/6.00  AC symbols                              0
% 43.37/6.00  
% 43.37/6.00  ------ Input Options Time Limit: Unbounded
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing...
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 43.37/6.00  Current options:
% 43.37/6.00  ------ 
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  % SZS status Theorem for theBenchmark.p
% 43.37/6.00  
% 43.37/6.00   Resolution empty clause
% 43.37/6.00  
% 43.37/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.37/6.00  
% 43.37/6.00  fof(f12,axiom,(
% 43.37/6.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f34,plain,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 43.37/6.00    inference(ennf_transformation,[],[f12])).
% 43.37/6.00  
% 43.37/6.00  fof(f35,plain,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(flattening,[],[f34])).
% 43.37/6.00  
% 43.37/6.00  fof(f74,plain,(
% 43.37/6.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f35])).
% 43.37/6.00  
% 43.37/6.00  fof(f10,axiom,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f51,plain,(
% 43.37/6.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 43.37/6.00    inference(nnf_transformation,[],[f10])).
% 43.37/6.00  
% 43.37/6.00  fof(f71,plain,(
% 43.37/6.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f51])).
% 43.37/6.00  
% 43.37/6.00  fof(f2,axiom,(
% 43.37/6.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f24,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.37/6.00    inference(ennf_transformation,[],[f2])).
% 43.37/6.00  
% 43.37/6.00  fof(f25,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 43.37/6.00    inference(flattening,[],[f24])).
% 43.37/6.00  
% 43.37/6.00  fof(f62,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f25])).
% 43.37/6.00  
% 43.37/6.00  fof(f14,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f37,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f14])).
% 43.37/6.00  
% 43.37/6.00  fof(f76,plain,(
% 43.37/6.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f37])).
% 43.37/6.00  
% 43.37/6.00  fof(f22,conjecture,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f23,negated_conjecture,(
% 43.37/6.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 43.37/6.00    inference(negated_conjecture,[],[f22])).
% 43.37/6.00  
% 43.37/6.00  fof(f46,plain,(
% 43.37/6.00    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f23])).
% 43.37/6.00  
% 43.37/6.00  fof(f47,plain,(
% 43.37/6.00    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 43.37/6.00    inference(flattening,[],[f46])).
% 43.37/6.00  
% 43.37/6.00  fof(f57,plain,(
% 43.37/6.00    ( ! [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0) & v3_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.37/6.00    introduced(choice_axiom,[])).
% 43.37/6.00  
% 43.37/6.00  fof(f56,plain,(
% 43.37/6.00    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 43.37/6.00    introduced(choice_axiom,[])).
% 43.37/6.00  
% 43.37/6.00  fof(f58,plain,(
% 43.37/6.00    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 43.37/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f57,f56])).
% 43.37/6.00  
% 43.37/6.00  fof(f89,plain,(
% 43.37/6.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 43.37/6.00    inference(cnf_transformation,[],[f58])).
% 43.37/6.00  
% 43.37/6.00  fof(f88,plain,(
% 43.37/6.00    l1_pre_topc(sK0)),
% 43.37/6.00    inference(cnf_transformation,[],[f58])).
% 43.37/6.00  
% 43.37/6.00  fof(f19,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f42,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f19])).
% 43.37/6.00  
% 43.37/6.00  fof(f84,plain,(
% 43.37/6.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f42])).
% 43.37/6.00  
% 43.37/6.00  fof(f1,axiom,(
% 43.37/6.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f48,plain,(
% 43.37/6.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.37/6.00    inference(nnf_transformation,[],[f1])).
% 43.37/6.00  
% 43.37/6.00  fof(f49,plain,(
% 43.37/6.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.37/6.00    inference(flattening,[],[f48])).
% 43.37/6.00  
% 43.37/6.00  fof(f59,plain,(
% 43.37/6.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 43.37/6.00    inference(cnf_transformation,[],[f49])).
% 43.37/6.00  
% 43.37/6.00  fof(f96,plain,(
% 43.37/6.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.37/6.00    inference(equality_resolution,[],[f59])).
% 43.37/6.00  
% 43.37/6.00  fof(f13,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f36,plain,(
% 43.37/6.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f13])).
% 43.37/6.00  
% 43.37/6.00  fof(f75,plain,(
% 43.37/6.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f36])).
% 43.37/6.00  
% 43.37/6.00  fof(f11,axiom,(
% 43.37/6.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f33,plain,(
% 43.37/6.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f11])).
% 43.37/6.00  
% 43.37/6.00  fof(f73,plain,(
% 43.37/6.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f33])).
% 43.37/6.00  
% 43.37/6.00  fof(f4,axiom,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f26,plain,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.37/6.00    inference(ennf_transformation,[],[f4])).
% 43.37/6.00  
% 43.37/6.00  fof(f64,plain,(
% 43.37/6.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f26])).
% 43.37/6.00  
% 43.37/6.00  fof(f72,plain,(
% 43.37/6.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f51])).
% 43.37/6.00  
% 43.37/6.00  fof(f5,axiom,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f27,plain,(
% 43.37/6.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.37/6.00    inference(ennf_transformation,[],[f5])).
% 43.37/6.00  
% 43.37/6.00  fof(f65,plain,(
% 43.37/6.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f27])).
% 43.37/6.00  
% 43.37/6.00  fof(f17,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f40,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f17])).
% 43.37/6.00  
% 43.37/6.00  fof(f53,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(nnf_transformation,[],[f40])).
% 43.37/6.00  
% 43.37/6.00  fof(f81,plain,(
% 43.37/6.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f53])).
% 43.37/6.00  
% 43.37/6.00  fof(f61,plain,(
% 43.37/6.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f49])).
% 43.37/6.00  
% 43.37/6.00  fof(f16,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f39,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f16])).
% 43.37/6.00  
% 43.37/6.00  fof(f52,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(nnf_transformation,[],[f39])).
% 43.37/6.00  
% 43.37/6.00  fof(f79,plain,(
% 43.37/6.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f52])).
% 43.37/6.00  
% 43.37/6.00  fof(f21,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f45,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f21])).
% 43.37/6.00  
% 43.37/6.00  fof(f55,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(nnf_transformation,[],[f45])).
% 43.37/6.00  
% 43.37/6.00  fof(f86,plain,(
% 43.37/6.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f55])).
% 43.37/6.00  
% 43.37/6.00  fof(f20,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f43,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f20])).
% 43.37/6.00  
% 43.37/6.00  fof(f44,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(flattening,[],[f43])).
% 43.37/6.00  
% 43.37/6.00  fof(f85,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f44])).
% 43.37/6.00  
% 43.37/6.00  fof(f18,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f41,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f18])).
% 43.37/6.00  
% 43.37/6.00  fof(f54,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(nnf_transformation,[],[f41])).
% 43.37/6.00  
% 43.37/6.00  fof(f82,plain,(
% 43.37/6.00    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f54])).
% 43.37/6.00  
% 43.37/6.00  fof(f90,plain,(
% 43.37/6.00    v3_tops_1(sK1,sK0)),
% 43.37/6.00    inference(cnf_transformation,[],[f58])).
% 43.37/6.00  
% 43.37/6.00  fof(f91,plain,(
% 43.37/6.00    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 43.37/6.00    inference(cnf_transformation,[],[f58])).
% 43.37/6.00  
% 43.37/6.00  fof(f80,plain,(
% 43.37/6.00    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f53])).
% 43.37/6.00  
% 43.37/6.00  fof(f87,plain,(
% 43.37/6.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f55])).
% 43.37/6.00  
% 43.37/6.00  fof(f15,axiom,(
% 43.37/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f38,plain,(
% 43.37/6.00    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.37/6.00    inference(ennf_transformation,[],[f15])).
% 43.37/6.00  
% 43.37/6.00  fof(f77,plain,(
% 43.37/6.00    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f38])).
% 43.37/6.00  
% 43.37/6.00  fof(f7,axiom,(
% 43.37/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f28,plain,(
% 43.37/6.00    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.37/6.00    inference(ennf_transformation,[],[f7])).
% 43.37/6.00  
% 43.37/6.00  fof(f29,plain,(
% 43.37/6.00    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.37/6.00    inference(flattening,[],[f28])).
% 43.37/6.00  
% 43.37/6.00  fof(f67,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f29])).
% 43.37/6.00  
% 43.37/6.00  cnf(c_14,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f74]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_12,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f71]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_31310,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_14,c_12]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_3,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 43.37/6.00      inference(cnf_transformation,[],[f62]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_40862,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(X2,k2_pre_topc(X1,X0))
% 43.37/6.00      | r1_tarski(X2,u1_struct_0(X1))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_31310,c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_570,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.37/6.00      theory(equality) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_575,plain,
% 43.37/6.00      ( X0 != X1 | k2_pre_topc(X2,X0) = k2_pre_topc(X2,X1) ),
% 43.37/6.00      theory(equality) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_31406,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k2_pre_topc(X1,X2))
% 43.37/6.00      | r1_tarski(X3,k2_pre_topc(X1,X4))
% 43.37/6.00      | X3 != X0
% 43.37/6.00      | X4 != X2 ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_570,c_575]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f76]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_30,negated_conjecture,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 43.37/6.00      inference(cnf_transformation,[],[f89]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_29893,plain,
% 43.37/6.00      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_16,c_30]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_31,negated_conjecture,
% 43.37/6.00      ( l1_pre_topc(sK0) ),
% 43.37/6.00      inference(cnf_transformation,[],[f88]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7659,plain,
% 43.37/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_16]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_30133,plain,
% 43.37/6.00      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_29893,c_31,c_30,c_7659]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_62121,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_pre_topc(sK0,X1)) | X0 != sK1 | X1 != sK1 ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_31406,c_30133]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_156551,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | r1_tarski(X1,u1_struct_0(sK0))
% 43.37/6.00      | ~ l1_pre_topc(sK0)
% 43.37/6.00      | X0 != sK1
% 43.37/6.00      | X1 != sK1 ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_40862,c_62121]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_24,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f84]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_3779,plain,
% 43.37/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_24]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_4281,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_570]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_5656,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_4281]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_5657,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 ),
% 43.37/6.00      inference(equality_resolution_simp,[status(thm)],[c_5656]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_5702,plain,
% 43.37/6.00      ( r1_tarski(X0,sK1) | ~ r1_tarski(sK1,sK1) | X0 != sK1 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_5657]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f96]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_5731,plain,
% 43.37/6.00      ( r1_tarski(sK1,sK1) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7541,plain,
% 43.37/6.00      ( l1_pre_topc(sK0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_15,plain,
% 43.37/6.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 43.37/6.00      inference(cnf_transformation,[],[f75]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7546,plain,
% 43.37/6.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7860,plain,
% 43.37/6.00      ( l1_struct_0(sK0) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_7541,c_7546]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_13,plain,
% 43.37/6.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 43.37/6.00      inference(cnf_transformation,[],[f73]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7548,plain,
% 43.37/6.00      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7971,plain,
% 43.37/6.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_7860,c_7548]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7542,plain,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7549,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8080,plain,
% 43.37/6.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_7542,c_7549]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8504,plain,
% 43.37/6.00      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(demodulation,[status(thm)],[c_7971,c_8080]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8513,plain,
% 43.37/6.00      ( r1_tarski(sK1,k2_struct_0(sK0)) ),
% 43.37/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_8504]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22791,plain,
% 43.37/6.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_5,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.37/6.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 43.37/6.00      inference(cnf_transformation,[],[f64]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_11,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f72]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_216,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.37/6.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_217,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_216]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_270,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~ r1_tarski(X1,X0) ),
% 43.37/6.00      inference(bin_hyper_res,[status(thm)],[c_5,c_217]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_29584,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(X0),X1),k1_zfmisc_1(k2_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(X1,k2_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_270]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_45413,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
% 43.37/6.00      | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_29584]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_55301,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | r1_tarski(k1_tops_1(X2,X3),X4)
% 43.37/6.00      | X4 != X1
% 43.37/6.00      | k1_tops_1(X2,X3) != X0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_570]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_55832,plain,
% 43.37/6.00      ( ~ r1_tarski(k1_tops_1(X0,X1),X2)
% 43.37/6.00      | r1_tarski(k1_tops_1(X0,X1),X3)
% 43.37/6.00      | X3 != X2
% 43.37/6.00      | k1_tops_1(X0,X1) != k1_tops_1(X0,X1) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_55301]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_55833,plain,
% 43.37/6.00      ( ~ r1_tarski(k1_tops_1(X0,X1),X2)
% 43.37/6.00      | r1_tarski(k1_tops_1(X0,X1),X3)
% 43.37/6.00      | X3 != X2 ),
% 43.37/6.00      inference(equality_resolution_simp,[status(thm)],[c_55832]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_56407,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0)
% 43.37/6.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 43.37/6.00      | X0 != sK1 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_55833]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16881,plain,
% 43.37/6.00      ( l1_pre_topc(sK0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16894,plain,
% 43.37/6.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17418,plain,
% 43.37/6.00      ( l1_struct_0(sK0) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16881,c_16894]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16896,plain,
% 43.37/6.00      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17593,plain,
% 43.37/6.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17418,c_16896]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16901,plain,
% 43.37/6.00      ( r1_tarski(X0,X0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_6,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.37/6.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.37/6.00      inference(cnf_transformation,[],[f65]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_271,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.37/6.00      inference(bin_hyper_res,[status(thm)],[c_6,c_217]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16879,plain,
% 43.37/6.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22701,plain,
% 43.37/6.00      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16901,c_16879]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20,plain,
% 43.37/6.00      ( v2_tops_1(X0,X1)
% 43.37/6.00      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f81]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16889,plain,
% 43.37/6.00      ( v2_tops_1(X0,X1) = iProver_top
% 43.37/6.00      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22863,plain,
% 43.37/6.00      ( v2_tops_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),X0) = iProver_top
% 43.37/6.00      | v1_tops_1(u1_struct_0(X0),X0) != iProver_top
% 43.37/6.00      | m1_subset_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_22701,c_16889]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_2941,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_2946,plain,
% 43.37/6.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_2941]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_2947,plain,
% 43.37/6.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 43.37/6.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_2946]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_2977,plain,
% 43.37/6.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_2978,plain,
% 43.37/6.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_2977]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_3862,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(X1,u1_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_270]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_3934,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_3862]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_3935,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 43.37/6.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_3934]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_569,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_0,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 43.37/6.00      inference(cnf_transformation,[],[f61]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8105,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_569,c_0]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9098,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X1),X0)
% 43.37/6.00      | ~ l1_struct_0(X1)
% 43.37/6.00      | X0 = u1_struct_0(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_8105,c_13]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9129,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(X2,k2_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),X0)
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X1),X2)
% 43.37/6.00      | ~ l1_struct_0(X1)
% 43.37/6.00      | X0 = X2 ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_9098,c_8105]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9579,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),X0)
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X1))
% 43.37/6.00      | ~ l1_struct_0(X1)
% 43.37/6.00      | X0 = k2_struct_0(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_9129,c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9593,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),X0)
% 43.37/6.00      | ~ l1_struct_0(X1)
% 43.37/6.00      | X0 = k2_struct_0(X1) ),
% 43.37/6.00      inference(forward_subsumption_resolution,[status(thm)],[c_9579,c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18,plain,
% 43.37/6.00      ( v1_tops_1(X0,X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f79]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9672,plain,
% 43.37/6.00      ( v1_tops_1(X0,X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | ~ l1_struct_0(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_9593,c_18]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8239,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_14,c_12]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10051,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | v1_tops_1(X0,X1)
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | ~ l1_struct_0(X1) ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_9672,c_8239]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10052,plain,
% 43.37/6.00      ( v1_tops_1(X0,X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | ~ l1_struct_0(X1) ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_10051]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10062,plain,
% 43.37/6.00      ( v1_tops_1(X0,X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),k2_pre_topc(X1,X0))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(forward_subsumption_resolution,[status(thm)],[c_10052,c_15]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7984,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 43.37/6.00      | ~ r1_tarski(X0,u1_struct_0(X1))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_16,c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10205,plain,
% 43.37/6.00      ( v1_tops_1(u1_struct_0(X0),X0)
% 43.37/6.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0))
% 43.37/6.00      | ~ l1_pre_topc(X0) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_10062,c_7984]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10206,plain,
% 43.37/6.00      ( v1_tops_1(u1_struct_0(X0),X0) = iProver_top
% 43.37/6.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.37/6.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_10205]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_143571,plain,
% 43.37/6.00      ( v2_tops_1(k3_subset_1(u1_struct_0(X0),u1_struct_0(X0)),X0) = iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_22863,c_2947,c_2978,c_3935,c_10206]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_143579,plain,
% 43.37/6.00      ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17593,c_143571]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_32,plain,
% 43.37/6.00      ( l1_pre_topc(sK0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8144,plain,
% 43.37/6.00      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_2]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8145,plain,
% 43.37/6.00      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_8144]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8147,plain,
% 43.37/6.00      ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_8145]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8054,plain,
% 43.37/6.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(X1))
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X0),X1) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8543,plain,
% 43.37/6.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_8054]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8544,plain,
% 43.37/6.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0))) = iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_8543]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8546,plain,
% 43.37/6.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_8544]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7547,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 43.37/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8878,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_7971,c_7547]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8896,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_8878,c_7971]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9207,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_8896,c_32]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9208,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_9207]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9215,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_9208,c_7549]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7550,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7545,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 43.37/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8516,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_7971,c_7545]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9065,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_8516,c_32]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9066,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_9065]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9074,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_7550,c_9066]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7553,plain,
% 43.37/6.00      ( X0 = X1
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9234,plain,
% 43.37/6.00      ( k2_pre_topc(sK0,X0) = X0
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,X0),X0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_9074,c_7553]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_9558,plain,
% 43.37/6.00      ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0)
% 43.37/6.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_9215,c_9234]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10165,plain,
% 43.37/6.00      ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_9558,c_8147,c_8546]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7544,plain,
% 43.37/6.00      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 43.37/6.00      | v1_tops_1(X1,X0) = iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10168,plain,
% 43.37/6.00      ( v1_tops_1(k2_struct_0(sK0),sK0) = iProver_top
% 43.37/6.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_10165,c_7544]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_10190,plain,
% 43.37/6.00      ( v1_tops_1(k2_struct_0(sK0),sK0) = iProver_top
% 43.37/6.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_10168,c_7971]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21561,plain,
% 43.37/6.00      ( v2_tops_1(X0,sK0) = iProver_top
% 43.37/6.00      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17593,c_16889]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21566,plain,
% 43.37/6.00      ( v2_tops_1(X0,sK0) = iProver_top
% 43.37/6.00      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_21561,c_17593]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22207,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 43.37/6.00      | v2_tops_1(X0,sK0) = iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_21566,c_32]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22208,plain,
% 43.37/6.00      ( v2_tops_1(X0,sK0) = iProver_top
% 43.37/6.00      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_22207]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22866,plain,
% 43.37/6.00      ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) = iProver_top
% 43.37/6.00      | v1_tops_1(k2_struct_0(sK0),sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_22701,c_22208]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_42070,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0)))
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_29584]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_42071,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0))) = iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_42070]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_42073,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_42071]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_146028,plain,
% 43.37/6.00      ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) = iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_143579,c_32,c_8147,c_8546,c_10190,c_22866,c_42073]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16880,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_27,plain,
% 43.37/6.00      ( ~ v2_tops_1(X0,X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 43.37/6.00      inference(cnf_transformation,[],[f86]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16884,plain,
% 43.37/6.00      ( k1_tops_1(X0,X1) = k1_xboole_0
% 43.37/6.00      | v2_tops_1(X1,X0) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20041,plain,
% 43.37/6.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 43.37/6.00      | v2_tops_1(X0,sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17593,c_16884]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20715,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | v2_tops_1(X0,sK0) != iProver_top
% 43.37/6.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_20041,c_32]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20716,plain,
% 43.37/6.00      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 43.37/6.00      | v2_tops_1(X0,sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_20715]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_23982,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k1_xboole_0
% 43.37/6.00      | v2_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16880,c_20716]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_146033,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) = k1_xboole_0
% 43.37/6.00      | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_146028,c_23982]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_148557,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) = k1_xboole_0 ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_146033,c_8147]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16898,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(X0,X2)
% 43.37/6.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f85]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16886,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X2) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 43.37/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16882,plain,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_23,plain,
% 43.37/6.00      ( ~ v3_tops_1(X0,X1)
% 43.37/6.00      | v2_tops_1(k2_pre_topc(X1,X0),X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f82]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16475,plain,
% 43.37/6.00      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 43.37/6.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 43.37/6.00      | ~ arAF0_v3_tops_1_0_1(X1)
% 43.37/6.00      | ~ l1_pre_topc(X0)
% 43.37/6.00      | ~ iProver_ARSWP_105 ),
% 43.37/6.00      inference(arg_filter_abstr,[status(unp)],[c_23]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16868,plain,
% 43.37/6.00      ( v2_tops_1(k2_pre_topc(X0,X1),X0) = iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.37/6.00      | arAF0_v3_tops_1_0_1(X1) != iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top
% 43.37/6.00      | iProver_ARSWP_105 != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_16475]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17569,plain,
% 43.37/6.00      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 43.37/6.00      | arAF0_v3_tops_1_0_1(sK1) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top
% 43.37/6.00      | iProver_ARSWP_105 != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16882,c_16868]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_33,plain,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_29,negated_conjecture,
% 43.37/6.00      ( v3_tops_1(sK1,sK0) ),
% 43.37/6.00      inference(cnf_transformation,[],[f90]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_34,plain,
% 43.37/6.00      ( v3_tops_1(sK1,sK0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_1320,plain,
% 43.37/6.00      ( ~ v3_tops_1(sK1,sK0)
% 43.37/6.00      | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 43.37/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_23]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_1321,plain,
% 43.37/6.00      ( v3_tops_1(sK1,sK0) != iProver_top
% 43.37/6.00      | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 43.37/6.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18048,plain,
% 43.37/6.00      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_17569,c_32,c_33,c_34,c_1321]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16895,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 43.37/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18966,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17593,c_16895]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19013,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_18966,c_17593]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20507,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_19013,c_32,c_8896]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20508,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_20507]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20727,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_xboole_0
% 43.37/6.00      | v2_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_20508,c_20716]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_35856,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
% 43.37/6.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_18048,c_20727]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7691,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_14]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17453,plain,
% 43.37/6.00      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 43.37/6.00      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ l1_pre_topc(sK0)
% 43.37/6.00      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_27]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_35924,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_35856,c_31,c_30,c_29,c_1320,c_7691,c_17453]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18056,plain,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(demodulation,[status(thm)],[c_17593,c_16882]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16900,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X2) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X2) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21677,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X2) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(X1,X2),X3) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(X1,X0),X3) = iProver_top
% 43.37/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16886,c_16900]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_77471,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17593,c_21677]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_77478,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_77471,c_17593]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_78653,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_77478,c_32]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_78654,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_78653]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_78665,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_18056,c_78654]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_78742,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
% 43.37/6.00      | r1_tarski(sK1,X0) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16886,c_78665]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_78864,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
% 43.37/6.00      | r1_tarski(sK1,X0) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_78742,c_17593]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_8506,plain,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 43.37/6.00      inference(demodulation,[status(thm)],[c_7971,c_7542]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_111339,plain,
% 43.37/6.00      ( r1_tarski(sK1,X0) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_78864,c_32,c_8506]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_111340,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top
% 43.37/6.00      | r1_tarski(sK1,X0) != iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_111339]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_111349,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
% 43.37/6.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_35924,c_111340]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_73,plain,
% 43.37/6.00      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_15]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_79,plain,
% 43.37/6.00      ( ~ l1_struct_0(sK0) | u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_13]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7660,plain,
% 43.37/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_7659]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7692,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 43.37/6.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_7691]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7701,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | r1_tarski(X0,u1_struct_0(X1)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_12]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7784,plain,
% 43.37/6.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_7701]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7785,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_7784]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17638,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | r1_tarski(X2,k2_struct_0(X3))
% 43.37/6.00      | X2 != X0
% 43.37/6.00      | k2_struct_0(X3) != X1 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_570]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18138,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 43.37/6.00      | r1_tarski(X2,k2_struct_0(X1))
% 43.37/6.00      | X2 != X0
% 43.37/6.00      | k2_struct_0(X1) != k2_struct_0(X1) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_17638]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18139,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 43.37/6.00      | r1_tarski(X2,k2_struct_0(X1))
% 43.37/6.00      | X2 != X0 ),
% 43.37/6.00      inference(equality_resolution_simp,[status(thm)],[c_18138]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18922,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X1))
% 43.37/6.00      | X0 != k2_struct_0(X1) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_18139]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19513,plain,
% 43.37/6.00      ( r1_tarski(u1_struct_0(X0),k2_struct_0(X0))
% 43.37/6.00      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X0))
% 43.37/6.00      | u1_struct_0(X0) != k2_struct_0(X0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_18922]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19514,plain,
% 43.37/6.00      ( u1_struct_0(X0) != k2_struct_0(X0)
% 43.37/6.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) = iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_19513]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19516,plain,
% 43.37/6.00      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 43.37/6.00      | r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) = iProver_top
% 43.37/6.00      | r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_19514]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_27858,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | ~ r1_tarski(X1,k2_struct_0(X2))
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(X2)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_31871,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(X1))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X1)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_27858]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_45336,plain,
% 43.37/6.00      ( ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0))
% 43.37/6.00      | ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_31871]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_45337,plain,
% 43.37/6.00      ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) = iProver_top
% 43.37/6.00      | r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_45336]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_28318,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X1)))
% 43.37/6.00      | ~ r1_tarski(X0,k2_struct_0(X1)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_81644,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
% 43.37/6.00      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_28318]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_81653,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_81644]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_113597,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_111349,c_31,c_32,c_33,c_73,c_79,c_7660,c_7692,c_7785,
% 43.37/6.00                 c_8147,c_19516,c_45337,c_81653]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_113598,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_113597]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_113608,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16898,c_113598]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_45430,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_struct_0(sK0))
% 43.37/6.00      | ~ r1_tarski(X0,sK1)
% 43.37/6.00      | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_27858]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_45431,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_struct_0(sK0)) = iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_45430]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_118345,plain,
% 43.37/6.00      ( r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_113608,c_8504,c_45431]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_118362,plain,
% 43.37/6.00      ( r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_118345,c_16900]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16902,plain,
% 43.37/6.00      ( X0 = X1
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_120824,plain,
% 43.37/6.00      ( k1_tops_1(sK0,X0) = X1
% 43.37/6.00      | r1_tarski(X1,k1_tops_1(sK0,X0)) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_118362,c_16902]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_126120,plain,
% 43.37/6.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X1,X0) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X1)) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16886,c_120824]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_126481,plain,
% 43.37/6.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_126120,c_17593]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_4278,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK1) | r1_tarski(X0,sK1) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_4279,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_4278]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_78739,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16901,c_78665]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_113609,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top
% 43.37/6.00      | r1_tarski(sK1,sK1) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_18056,c_113598]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_5732,plain,
% 43.37/6.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_5731]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_114207,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_113609,c_5732]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_114219,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_114207,c_16900]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_114777,plain,
% 43.37/6.00      ( k1_tops_1(sK0,sK1) = X0
% 43.37/6.00      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_114219,c_16902]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_28,negated_conjecture,
% 43.37/6.00      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 43.37/6.00      inference(cnf_transformation,[],[f91]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21,plain,
% 43.37/6.00      ( ~ v2_tops_1(X0,X1)
% 43.37/6.00      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1) ),
% 43.37/6.00      inference(cnf_transformation,[],[f80]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_3813,plain,
% 43.37/6.00      ( ~ v2_tops_1(sK1,sK0)
% 43.37/6.00      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 43.37/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_21]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_26,plain,
% 43.37/6.00      ( v2_tops_1(X0,X1)
% 43.37/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 43.37/6.00      inference(cnf_transformation,[],[f87]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_4162,plain,
% 43.37/6.00      ( v2_tops_1(sK1,sK0)
% 43.37/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ l1_pre_topc(sK0)
% 43.37/6.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_26]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_6249,plain,
% 43.37/6.00      ( k1_tops_1(sK0,sK1) != X0
% 43.37/6.00      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 43.37/6.00      | k1_xboole_0 != X0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_569]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20412,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 43.37/6.00      | ~ r1_tarski(k1_xboole_0,X0)
% 43.37/6.00      | k1_xboole_0 = X0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_0]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20413,plain,
% 43.37/6.00      ( k1_xboole_0 = X0
% 43.37/6.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_20412]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22792,plain,
% 43.37/6.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_22791]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_23237,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | r1_tarski(X2,k1_xboole_0)
% 43.37/6.00      | X2 != X0
% 43.37/6.00      | k1_xboole_0 != X1 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_570]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_24577,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 43.37/6.00      | r1_tarski(X1,k1_xboole_0)
% 43.37/6.00      | X1 != X0
% 43.37/6.00      | k1_xboole_0 != k1_xboole_0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_23237]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_24578,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(X1,k1_xboole_0) | X1 != X0 ),
% 43.37/6.00      inference(equality_resolution_simp,[status(thm)],[c_24577]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_24914,plain,
% 43.37/6.00      ( r1_tarski(X0,k1_xboole_0)
% 43.37/6.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 43.37/6.00      | X0 != k1_xboole_0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_24578]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25601,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0)
% 43.37/6.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 43.37/6.00      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k1_xboole_0 ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_24914]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25602,plain,
% 43.37/6.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k1_xboole_0
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0) = iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_25601]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17470,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_25]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25855,plain,
% 43.37/6.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 43.37/6.00      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 43.37/6.00      | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_17470]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25856,plain,
% 43.37/6.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
% 43.37/6.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_25855]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_23229,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | ~ r1_tarski(X1,k1_xboole_0)
% 43.37/6.00      | r1_tarski(X0,k1_xboole_0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25892,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 43.37/6.00      | r1_tarski(X0,k1_xboole_0)
% 43.37/6.00      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_23229]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_25893,plain,
% 43.37/6.00      ( r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_xboole_0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_25892]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21782,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | ~ r1_tarski(X1,k1_tops_1(X2,X3))
% 43.37/6.00      | r1_tarski(X0,k1_tops_1(X2,X3)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_26316,plain,
% 43.37/6.00      ( r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 43.37/6.00      | ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 43.37/6.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_21782]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_26317,plain,
% 43.37/6.00      ( r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
% 43.37/6.00      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_26316]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_118071,plain,
% 43.37/6.00      ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_114777,c_31,c_32,c_30,c_33,c_29,c_28,c_1320,c_3813,c_4162,
% 43.37/6.00                 c_6249,c_7660,c_7691,c_7692,c_17453,c_20413,c_22792,c_25602,
% 43.37/6.00                 c_25856,c_25893,c_26317]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_118085,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_78739,c_118071]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_127271,plain,
% 43.37/6.00      ( r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_126481,c_4279,c_118085]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_127272,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_127271]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_127281,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_16898,c_127272]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_18863,plain,
% 43.37/6.00      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~ l1_pre_topc(sK0) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_16,c_30]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19048,plain,
% 43.37/6.00      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_18863,c_31,c_30,c_7659]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19060,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_pre_topc(sK0,sK1)) | ~ r1_tarski(X0,sK1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_19048,c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19203,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 43.37/6.00      | ~ r1_tarski(X1,sK1) ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_19060,c_3]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_19204,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) = iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_19203]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_81685,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(sK0))
% 43.37/6.00      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_27858]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_81686,plain,
% 43.37/6.00      ( r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(sK0)) = iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_81685]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_130339,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X1,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_127281,c_31,c_32,c_33,c_73,c_79,c_7692,c_7785,c_8147,
% 43.37/6.00                 c_19204,c_19516,c_45337,c_81686]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_148569,plain,
% 43.37/6.00      ( r1_tarski(X0,sK1) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) != iProver_top
% 43.37/6.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_148557,c_130339]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_148915,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,sK1)
% 43.37/6.00      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0)
% 43.37/6.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 43.37/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_148569]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16897,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.37/6.00      | r1_tarski(X0,X1) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_20513,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_20508,c_16897]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_17,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.37/6.00      | ~ l1_pre_topc(X1)
% 43.37/6.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 43.37/6.00      inference(cnf_transformation,[],[f77]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16892,plain,
% 43.37/6.00      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 43.37/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21390,plain,
% 43.37/6.00      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_17593,c_16892]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21394,plain,
% 43.37/6.00      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.37/6.00      inference(light_normalisation,[status(thm)],[c_21390,c_17593]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21864,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 43.37/6.00      inference(global_propositional_subsumption,[status(thm)],[c_21394,c_32]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21865,plain,
% 43.37/6.00      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 43.37/6.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_21864]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_21874,plain,
% 43.37/6.00      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_18056,c_21865]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_7,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.37/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.37/6.00      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 43.37/6.00      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 43.37/6.00      inference(cnf_transformation,[],[f67]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_272,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.37/6.00      | ~ r1_tarski(X2,X1)
% 43.37/6.00      | ~ r1_tarski(X2,k3_subset_1(X1,X0))
% 43.37/6.00      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 43.37/6.00      inference(bin_hyper_res,[status(thm)],[c_7,c_217]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_435,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.37/6.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_436,plain,
% 43.37/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_435]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_490,plain,
% 43.37/6.00      ( ~ r1_tarski(X0,X1)
% 43.37/6.00      | ~ r1_tarski(X2,X1)
% 43.37/6.00      | ~ r1_tarski(X2,k3_subset_1(X1,X0))
% 43.37/6.00      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 43.37/6.00      inference(bin_hyper_res,[status(thm)],[c_272,c_436]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_16871,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X2,X1) != iProver_top
% 43.37/6.00      | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top
% 43.37/6.00      | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_22861,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(X1,X1),X1) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(X1,X1),k3_subset_1(X1,X0)) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_22701,c_16871]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_135620,plain,
% 43.37/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(X1,X0),X2) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(X1,X1),X1) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(X1,X1),X2) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_22861,c_16900]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_155692,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) != iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_21874,c_135620]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_27852,plain,
% 43.37/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X1)))
% 43.37/6.00      | r1_tarski(X0,k2_struct_0(X1)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_12]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_28314,plain,
% 43.37/6.00      ( ~ m1_subset_1(k3_subset_1(k2_struct_0(X0),X1),k1_zfmisc_1(k2_struct_0(X0)))
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(X0),X1),k2_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_27852]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_42115,plain,
% 43.37/6.00      ( ~ m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0)))
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k2_struct_0(X0)) ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_28314]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_42116,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(X0),k2_struct_0(X0)),k2_struct_0(X0)) = iProver_top ),
% 43.37/6.00      inference(predicate_to_equality,[status(thm)],[c_42115]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_42118,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) = iProver_top ),
% 43.37/6.00      inference(instantiation,[status(thm)],[c_42116]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_156831,plain,
% 43.37/6.00      ( r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_155692,c_8147,c_42073,c_42118]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_156832,plain,
% 43.37/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 43.37/6.00      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top ),
% 43.37/6.00      inference(renaming,[status(thm)],[c_156831]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_156840,plain,
% 43.37/6.00      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 43.37/6.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = iProver_top ),
% 43.37/6.00      inference(superposition,[status(thm)],[c_20513,c_156832]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_156868,plain,
% 43.37/6.00      ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
% 43.37/6.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 43.37/6.00      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) ),
% 43.37/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_156840]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_157031,plain,
% 43.37/6.00      ( X0 != sK1 ),
% 43.37/6.00      inference(global_propositional_subsumption,
% 43.37/6.00                [status(thm)],
% 43.37/6.00                [c_156551,c_31,c_30,c_3779,c_5702,c_5731,c_8513,c_22791,
% 43.37/6.00                 c_45413,c_56407,c_148915,c_156868]) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_568,plain,( X0 = X0 ),theory(equality) ).
% 43.37/6.00  
% 43.37/6.00  cnf(c_157423,plain,
% 43.37/6.00      ( $false ),
% 43.37/6.00      inference(resolution,[status(thm)],[c_157031,c_568]) ).
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.37/6.00  
% 43.37/6.00  ------                               Statistics
% 43.37/6.00  
% 43.37/6.00  ------ Selected
% 43.37/6.00  
% 43.37/6.00  total_time:                             5.409
% 43.37/6.00  
%------------------------------------------------------------------------------
