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
% DateTime   : Thu Dec  3 12:15:18 EST 2020

% Result     : Theorem 39.72s
% Output     : CNFRefutation 39.72s
% Verified   : 
% Statistics : Number of formulae       :  214 (1053 expanded)
%              Number of clauses        :  140 ( 395 expanded)
%              Number of leaves         :   21 ( 225 expanded)
%              Depth                    :   18
%              Number of atoms          :  561 (3304 expanded)
%              Number of equality atoms :  211 ( 438 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
        & v3_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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

fof(f56,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f55,f54])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1363,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1353,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_1354,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1755,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0)))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1354])).

cnf(c_2663,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1755])).

cnf(c_2806,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,X0))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_2663])).

cnf(c_3657,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_1363,c_2806])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_248,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_302,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_248])).

cnf(c_1360,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_1356,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1369,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1369])).

cnf(c_8703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_4548])).

cnf(c_12355,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_8703])).

cnf(c_14795,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3657,c_12355])).

cnf(c_14811,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14795,c_3657])).

cnf(c_33,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1404,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1405,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2089,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_2090,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2089])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1367,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1368,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1366,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3163,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1366])).

cnf(c_9033,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1367,c_3163])).

cnf(c_9048,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9033,c_1367])).

cnf(c_27,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_466,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_467,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_23,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(k2_pre_topc(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_453,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_454,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_456,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_31,c_30])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | k2_pre_topc(sK0,sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_467,c_456])).

cnf(c_588,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_1351,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_1919,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_30,c_588,c_1404])).

cnf(c_1365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9149,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_8703])).

cnf(c_9308,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1919,c_9149])).

cnf(c_1690,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_23217,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_23220,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23217])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1355,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_3060,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_1355])).

cnf(c_1364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3049,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1364])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_304,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_248])).

cnf(c_1358,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_6078,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3049,c_1358])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_248])).

cnf(c_706,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_706])).

cnf(c_748,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_307,c_707])).

cnf(c_1348,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_104,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_785,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_2044,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_104,c_785])).

cnf(c_6682,plain,
    ( r1_tarski(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6078,c_2044])).

cnf(c_1584,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
    | r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1977,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_1978,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_1536,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_2372,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_2374,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2372])).

cnf(c_2099,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_20403,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_20411,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20403])).

cnf(c_110446,plain,
    ( r1_tarski(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6682,c_33,c_1978,c_2374,c_20411])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_301,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_248])).

cnf(c_1361,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_7796,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_3049,c_1361])).

cnf(c_110452,plain,
    ( r1_tarski(X0,k4_xboole_0(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_110446,c_7796])).

cnf(c_110461,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_110452])).

cnf(c_12363,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1354])).

cnf(c_13024,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_3049,c_12363])).

cnf(c_8235,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_7796,c_6078])).

cnf(c_13035,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_13024,c_7796,c_8235])).

cnf(c_110501,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_110461,c_13035])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1370,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3050,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1364])).

cnf(c_4550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3050,c_1369])).

cnf(c_43813,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_4550])).

cnf(c_44217,plain,
    ( k3_subset_1(X0,k2_pre_topc(sK0,sK1)) = k4_xboole_0(X0,k2_pre_topc(sK0,sK1))
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43813,c_1361])).

cnf(c_44447,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1370,c_44217])).

cnf(c_44218,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43813,c_1358])).

cnf(c_44515,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1370,c_44218])).

cnf(c_44522,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_44515,c_44447])).

cnf(c_110502,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_110501,c_44447,c_44522])).

cnf(c_125658,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14811,c_33,c_1405,c_2090,c_9048,c_9308,c_23220,c_110502])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3161,plain,
    ( r1_tarski(X0,k4_xboole_0(X0,X1)) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1368])).

cnf(c_1507,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1355])).

cnf(c_4552,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1369])).

cnf(c_5299,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k4_xboole_0(X0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_1366])).

cnf(c_26,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_481,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_482,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_21,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_427,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_428,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(X0,sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_31])).

cnf(c_433,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(renaming,[status(thm)],[c_432])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[status(thm)],[c_482,c_433])).

cnf(c_1352,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_2453,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1352])).

cnf(c_14982,plain,
    ( r1_tarski(sK1,k4_xboole_0(X0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5299,c_33,c_2453])).

cnf(c_14988,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3161,c_14982])).

cnf(c_125685,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_125658,c_14988])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.72/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.72/5.50  
% 39.72/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.72/5.50  
% 39.72/5.50  ------  iProver source info
% 39.72/5.50  
% 39.72/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.72/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.72/5.50  git: non_committed_changes: false
% 39.72/5.50  git: last_make_outside_of_git: false
% 39.72/5.50  
% 39.72/5.50  ------ 
% 39.72/5.50  
% 39.72/5.50  ------ Input Options
% 39.72/5.50  
% 39.72/5.50  --out_options                           all
% 39.72/5.50  --tptp_safe_out                         true
% 39.72/5.50  --problem_path                          ""
% 39.72/5.50  --include_path                          ""
% 39.72/5.50  --clausifier                            res/vclausify_rel
% 39.72/5.50  --clausifier_options                    ""
% 39.72/5.50  --stdin                                 false
% 39.72/5.50  --stats_out                             all
% 39.72/5.50  
% 39.72/5.50  ------ General Options
% 39.72/5.50  
% 39.72/5.50  --fof                                   false
% 39.72/5.50  --time_out_real                         305.
% 39.72/5.50  --time_out_virtual                      -1.
% 39.72/5.50  --symbol_type_check                     false
% 39.72/5.50  --clausify_out                          false
% 39.72/5.50  --sig_cnt_out                           false
% 39.72/5.50  --trig_cnt_out                          false
% 39.72/5.50  --trig_cnt_out_tolerance                1.
% 39.72/5.50  --trig_cnt_out_sk_spl                   false
% 39.72/5.50  --abstr_cl_out                          false
% 39.72/5.50  
% 39.72/5.50  ------ Global Options
% 39.72/5.50  
% 39.72/5.50  --schedule                              default
% 39.72/5.50  --add_important_lit                     false
% 39.72/5.50  --prop_solver_per_cl                    1000
% 39.72/5.50  --min_unsat_core                        false
% 39.72/5.50  --soft_assumptions                      false
% 39.72/5.50  --soft_lemma_size                       3
% 39.72/5.50  --prop_impl_unit_size                   0
% 39.72/5.50  --prop_impl_unit                        []
% 39.72/5.50  --share_sel_clauses                     true
% 39.72/5.50  --reset_solvers                         false
% 39.72/5.50  --bc_imp_inh                            [conj_cone]
% 39.72/5.50  --conj_cone_tolerance                   3.
% 39.72/5.50  --extra_neg_conj                        none
% 39.72/5.50  --large_theory_mode                     true
% 39.72/5.50  --prolific_symb_bound                   200
% 39.72/5.50  --lt_threshold                          2000
% 39.72/5.50  --clause_weak_htbl                      true
% 39.72/5.50  --gc_record_bc_elim                     false
% 39.72/5.50  
% 39.72/5.50  ------ Preprocessing Options
% 39.72/5.50  
% 39.72/5.50  --preprocessing_flag                    true
% 39.72/5.50  --time_out_prep_mult                    0.1
% 39.72/5.50  --splitting_mode                        input
% 39.72/5.50  --splitting_grd                         true
% 39.72/5.50  --splitting_cvd                         false
% 39.72/5.50  --splitting_cvd_svl                     false
% 39.72/5.50  --splitting_nvd                         32
% 39.72/5.50  --sub_typing                            true
% 39.72/5.50  --prep_gs_sim                           true
% 39.72/5.50  --prep_unflatten                        true
% 39.72/5.50  --prep_res_sim                          true
% 39.72/5.50  --prep_upred                            true
% 39.72/5.50  --prep_sem_filter                       exhaustive
% 39.72/5.50  --prep_sem_filter_out                   false
% 39.72/5.50  --pred_elim                             true
% 39.72/5.50  --res_sim_input                         true
% 39.72/5.50  --eq_ax_congr_red                       true
% 39.72/5.50  --pure_diseq_elim                       true
% 39.72/5.50  --brand_transform                       false
% 39.72/5.50  --non_eq_to_eq                          false
% 39.72/5.50  --prep_def_merge                        true
% 39.72/5.50  --prep_def_merge_prop_impl              false
% 39.72/5.50  --prep_def_merge_mbd                    true
% 39.72/5.50  --prep_def_merge_tr_red                 false
% 39.72/5.50  --prep_def_merge_tr_cl                  false
% 39.72/5.50  --smt_preprocessing                     true
% 39.72/5.50  --smt_ac_axioms                         fast
% 39.72/5.50  --preprocessed_out                      false
% 39.72/5.50  --preprocessed_stats                    false
% 39.72/5.50  
% 39.72/5.50  ------ Abstraction refinement Options
% 39.72/5.50  
% 39.72/5.50  --abstr_ref                             []
% 39.72/5.50  --abstr_ref_prep                        false
% 39.72/5.50  --abstr_ref_until_sat                   false
% 39.72/5.50  --abstr_ref_sig_restrict                funpre
% 39.72/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.72/5.50  --abstr_ref_under                       []
% 39.72/5.50  
% 39.72/5.50  ------ SAT Options
% 39.72/5.50  
% 39.72/5.50  --sat_mode                              false
% 39.72/5.50  --sat_fm_restart_options                ""
% 39.72/5.50  --sat_gr_def                            false
% 39.72/5.50  --sat_epr_types                         true
% 39.72/5.50  --sat_non_cyclic_types                  false
% 39.72/5.50  --sat_finite_models                     false
% 39.72/5.50  --sat_fm_lemmas                         false
% 39.72/5.50  --sat_fm_prep                           false
% 39.72/5.50  --sat_fm_uc_incr                        true
% 39.72/5.50  --sat_out_model                         small
% 39.72/5.50  --sat_out_clauses                       false
% 39.72/5.50  
% 39.72/5.50  ------ QBF Options
% 39.72/5.50  
% 39.72/5.50  --qbf_mode                              false
% 39.72/5.50  --qbf_elim_univ                         false
% 39.72/5.50  --qbf_dom_inst                          none
% 39.72/5.50  --qbf_dom_pre_inst                      false
% 39.72/5.50  --qbf_sk_in                             false
% 39.72/5.50  --qbf_pred_elim                         true
% 39.72/5.50  --qbf_split                             512
% 39.72/5.50  
% 39.72/5.50  ------ BMC1 Options
% 39.72/5.50  
% 39.72/5.50  --bmc1_incremental                      false
% 39.72/5.50  --bmc1_axioms                           reachable_all
% 39.72/5.50  --bmc1_min_bound                        0
% 39.72/5.50  --bmc1_max_bound                        -1
% 39.72/5.50  --bmc1_max_bound_default                -1
% 39.72/5.50  --bmc1_symbol_reachability              true
% 39.72/5.50  --bmc1_property_lemmas                  false
% 39.72/5.50  --bmc1_k_induction                      false
% 39.72/5.50  --bmc1_non_equiv_states                 false
% 39.72/5.50  --bmc1_deadlock                         false
% 39.72/5.50  --bmc1_ucm                              false
% 39.72/5.50  --bmc1_add_unsat_core                   none
% 39.72/5.50  --bmc1_unsat_core_children              false
% 39.72/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.72/5.50  --bmc1_out_stat                         full
% 39.72/5.50  --bmc1_ground_init                      false
% 39.72/5.50  --bmc1_pre_inst_next_state              false
% 39.72/5.50  --bmc1_pre_inst_state                   false
% 39.72/5.50  --bmc1_pre_inst_reach_state             false
% 39.72/5.50  --bmc1_out_unsat_core                   false
% 39.72/5.50  --bmc1_aig_witness_out                  false
% 39.72/5.50  --bmc1_verbose                          false
% 39.72/5.50  --bmc1_dump_clauses_tptp                false
% 39.72/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.72/5.50  --bmc1_dump_file                        -
% 39.72/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.72/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.72/5.50  --bmc1_ucm_extend_mode                  1
% 39.72/5.50  --bmc1_ucm_init_mode                    2
% 39.72/5.50  --bmc1_ucm_cone_mode                    none
% 39.72/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.72/5.50  --bmc1_ucm_relax_model                  4
% 39.72/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.72/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.72/5.50  --bmc1_ucm_layered_model                none
% 39.72/5.50  --bmc1_ucm_max_lemma_size               10
% 39.72/5.50  
% 39.72/5.50  ------ AIG Options
% 39.72/5.50  
% 39.72/5.50  --aig_mode                              false
% 39.72/5.50  
% 39.72/5.50  ------ Instantiation Options
% 39.72/5.50  
% 39.72/5.50  --instantiation_flag                    true
% 39.72/5.50  --inst_sos_flag                         true
% 39.72/5.50  --inst_sos_phase                        true
% 39.72/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.72/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.72/5.50  --inst_lit_sel_side                     num_symb
% 39.72/5.50  --inst_solver_per_active                1400
% 39.72/5.50  --inst_solver_calls_frac                1.
% 39.72/5.50  --inst_passive_queue_type               priority_queues
% 39.72/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.72/5.50  --inst_passive_queues_freq              [25;2]
% 39.72/5.50  --inst_dismatching                      true
% 39.72/5.50  --inst_eager_unprocessed_to_passive     true
% 39.72/5.50  --inst_prop_sim_given                   true
% 39.72/5.50  --inst_prop_sim_new                     false
% 39.72/5.50  --inst_subs_new                         false
% 39.72/5.50  --inst_eq_res_simp                      false
% 39.72/5.50  --inst_subs_given                       false
% 39.72/5.50  --inst_orphan_elimination               true
% 39.72/5.50  --inst_learning_loop_flag               true
% 39.72/5.50  --inst_learning_start                   3000
% 39.72/5.50  --inst_learning_factor                  2
% 39.72/5.50  --inst_start_prop_sim_after_learn       3
% 39.72/5.50  --inst_sel_renew                        solver
% 39.72/5.50  --inst_lit_activity_flag                true
% 39.72/5.50  --inst_restr_to_given                   false
% 39.72/5.50  --inst_activity_threshold               500
% 39.72/5.50  --inst_out_proof                        true
% 39.72/5.50  
% 39.72/5.50  ------ Resolution Options
% 39.72/5.50  
% 39.72/5.50  --resolution_flag                       true
% 39.72/5.50  --res_lit_sel                           adaptive
% 39.72/5.50  --res_lit_sel_side                      none
% 39.72/5.50  --res_ordering                          kbo
% 39.72/5.50  --res_to_prop_solver                    active
% 39.72/5.50  --res_prop_simpl_new                    false
% 39.72/5.50  --res_prop_simpl_given                  true
% 39.72/5.50  --res_passive_queue_type                priority_queues
% 39.72/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.72/5.50  --res_passive_queues_freq               [15;5]
% 39.72/5.50  --res_forward_subs                      full
% 39.72/5.50  --res_backward_subs                     full
% 39.72/5.50  --res_forward_subs_resolution           true
% 39.72/5.50  --res_backward_subs_resolution          true
% 39.72/5.50  --res_orphan_elimination                true
% 39.72/5.50  --res_time_limit                        2.
% 39.72/5.50  --res_out_proof                         true
% 39.72/5.50  
% 39.72/5.50  ------ Superposition Options
% 39.72/5.50  
% 39.72/5.50  --superposition_flag                    true
% 39.72/5.50  --sup_passive_queue_type                priority_queues
% 39.72/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.72/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.72/5.50  --demod_completeness_check              fast
% 39.72/5.50  --demod_use_ground                      true
% 39.72/5.50  --sup_to_prop_solver                    passive
% 39.72/5.50  --sup_prop_simpl_new                    true
% 39.72/5.50  --sup_prop_simpl_given                  true
% 39.72/5.50  --sup_fun_splitting                     true
% 39.72/5.50  --sup_smt_interval                      50000
% 39.72/5.50  
% 39.72/5.50  ------ Superposition Simplification Setup
% 39.72/5.50  
% 39.72/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.72/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.72/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.72/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.72/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.72/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.72/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.72/5.50  --sup_immed_triv                        [TrivRules]
% 39.72/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.72/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.72/5.50  --sup_immed_bw_main                     []
% 39.72/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.72/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.72/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.72/5.50  --sup_input_bw                          []
% 39.72/5.50  
% 39.72/5.50  ------ Combination Options
% 39.72/5.50  
% 39.72/5.50  --comb_res_mult                         3
% 39.72/5.50  --comb_sup_mult                         2
% 39.72/5.50  --comb_inst_mult                        10
% 39.72/5.50  
% 39.72/5.50  ------ Debug Options
% 39.72/5.50  
% 39.72/5.50  --dbg_backtrace                         false
% 39.72/5.50  --dbg_dump_prop_clauses                 false
% 39.72/5.50  --dbg_dump_prop_clauses_file            -
% 39.72/5.50  --dbg_out_stat                          false
% 39.72/5.50  ------ Parsing...
% 39.72/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.72/5.50  
% 39.72/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 39.72/5.50  
% 39.72/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.72/5.50  
% 39.72/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.72/5.50  ------ Proving...
% 39.72/5.50  ------ Problem Properties 
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  clauses                                 25
% 39.72/5.50  conjectures                             1
% 39.72/5.50  EPR                                     3
% 39.72/5.50  Horn                                    25
% 39.72/5.50  unary                                   4
% 39.72/5.50  binary                                  15
% 39.72/5.50  lits                                    55
% 39.72/5.50  lits eq                                 12
% 39.72/5.50  fd_pure                                 0
% 39.72/5.50  fd_pseudo                               0
% 39.72/5.50  fd_cond                                 1
% 39.72/5.50  fd_pseudo_cond                          1
% 39.72/5.50  AC symbols                              0
% 39.72/5.50  
% 39.72/5.50  ------ Schedule dynamic 5 is on 
% 39.72/5.50  
% 39.72/5.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  ------ 
% 39.72/5.50  Current options:
% 39.72/5.50  ------ 
% 39.72/5.50  
% 39.72/5.50  ------ Input Options
% 39.72/5.50  
% 39.72/5.50  --out_options                           all
% 39.72/5.50  --tptp_safe_out                         true
% 39.72/5.50  --problem_path                          ""
% 39.72/5.50  --include_path                          ""
% 39.72/5.50  --clausifier                            res/vclausify_rel
% 39.72/5.50  --clausifier_options                    ""
% 39.72/5.50  --stdin                                 false
% 39.72/5.50  --stats_out                             all
% 39.72/5.50  
% 39.72/5.50  ------ General Options
% 39.72/5.50  
% 39.72/5.50  --fof                                   false
% 39.72/5.50  --time_out_real                         305.
% 39.72/5.50  --time_out_virtual                      -1.
% 39.72/5.50  --symbol_type_check                     false
% 39.72/5.50  --clausify_out                          false
% 39.72/5.50  --sig_cnt_out                           false
% 39.72/5.50  --trig_cnt_out                          false
% 39.72/5.50  --trig_cnt_out_tolerance                1.
% 39.72/5.50  --trig_cnt_out_sk_spl                   false
% 39.72/5.50  --abstr_cl_out                          false
% 39.72/5.50  
% 39.72/5.50  ------ Global Options
% 39.72/5.50  
% 39.72/5.50  --schedule                              default
% 39.72/5.50  --add_important_lit                     false
% 39.72/5.50  --prop_solver_per_cl                    1000
% 39.72/5.50  --min_unsat_core                        false
% 39.72/5.50  --soft_assumptions                      false
% 39.72/5.50  --soft_lemma_size                       3
% 39.72/5.50  --prop_impl_unit_size                   0
% 39.72/5.50  --prop_impl_unit                        []
% 39.72/5.50  --share_sel_clauses                     true
% 39.72/5.50  --reset_solvers                         false
% 39.72/5.50  --bc_imp_inh                            [conj_cone]
% 39.72/5.50  --conj_cone_tolerance                   3.
% 39.72/5.50  --extra_neg_conj                        none
% 39.72/5.50  --large_theory_mode                     true
% 39.72/5.50  --prolific_symb_bound                   200
% 39.72/5.50  --lt_threshold                          2000
% 39.72/5.50  --clause_weak_htbl                      true
% 39.72/5.50  --gc_record_bc_elim                     false
% 39.72/5.50  
% 39.72/5.50  ------ Preprocessing Options
% 39.72/5.50  
% 39.72/5.50  --preprocessing_flag                    true
% 39.72/5.50  --time_out_prep_mult                    0.1
% 39.72/5.50  --splitting_mode                        input
% 39.72/5.50  --splitting_grd                         true
% 39.72/5.50  --splitting_cvd                         false
% 39.72/5.50  --splitting_cvd_svl                     false
% 39.72/5.50  --splitting_nvd                         32
% 39.72/5.50  --sub_typing                            true
% 39.72/5.50  --prep_gs_sim                           true
% 39.72/5.50  --prep_unflatten                        true
% 39.72/5.50  --prep_res_sim                          true
% 39.72/5.50  --prep_upred                            true
% 39.72/5.50  --prep_sem_filter                       exhaustive
% 39.72/5.50  --prep_sem_filter_out                   false
% 39.72/5.50  --pred_elim                             true
% 39.72/5.50  --res_sim_input                         true
% 39.72/5.50  --eq_ax_congr_red                       true
% 39.72/5.50  --pure_diseq_elim                       true
% 39.72/5.50  --brand_transform                       false
% 39.72/5.50  --non_eq_to_eq                          false
% 39.72/5.50  --prep_def_merge                        true
% 39.72/5.50  --prep_def_merge_prop_impl              false
% 39.72/5.50  --prep_def_merge_mbd                    true
% 39.72/5.50  --prep_def_merge_tr_red                 false
% 39.72/5.50  --prep_def_merge_tr_cl                  false
% 39.72/5.50  --smt_preprocessing                     true
% 39.72/5.50  --smt_ac_axioms                         fast
% 39.72/5.50  --preprocessed_out                      false
% 39.72/5.50  --preprocessed_stats                    false
% 39.72/5.50  
% 39.72/5.50  ------ Abstraction refinement Options
% 39.72/5.50  
% 39.72/5.50  --abstr_ref                             []
% 39.72/5.50  --abstr_ref_prep                        false
% 39.72/5.50  --abstr_ref_until_sat                   false
% 39.72/5.50  --abstr_ref_sig_restrict                funpre
% 39.72/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.72/5.50  --abstr_ref_under                       []
% 39.72/5.50  
% 39.72/5.50  ------ SAT Options
% 39.72/5.50  
% 39.72/5.50  --sat_mode                              false
% 39.72/5.50  --sat_fm_restart_options                ""
% 39.72/5.50  --sat_gr_def                            false
% 39.72/5.50  --sat_epr_types                         true
% 39.72/5.50  --sat_non_cyclic_types                  false
% 39.72/5.50  --sat_finite_models                     false
% 39.72/5.50  --sat_fm_lemmas                         false
% 39.72/5.50  --sat_fm_prep                           false
% 39.72/5.50  --sat_fm_uc_incr                        true
% 39.72/5.50  --sat_out_model                         small
% 39.72/5.50  --sat_out_clauses                       false
% 39.72/5.50  
% 39.72/5.50  ------ QBF Options
% 39.72/5.50  
% 39.72/5.50  --qbf_mode                              false
% 39.72/5.50  --qbf_elim_univ                         false
% 39.72/5.50  --qbf_dom_inst                          none
% 39.72/5.50  --qbf_dom_pre_inst                      false
% 39.72/5.50  --qbf_sk_in                             false
% 39.72/5.50  --qbf_pred_elim                         true
% 39.72/5.50  --qbf_split                             512
% 39.72/5.50  
% 39.72/5.50  ------ BMC1 Options
% 39.72/5.50  
% 39.72/5.50  --bmc1_incremental                      false
% 39.72/5.50  --bmc1_axioms                           reachable_all
% 39.72/5.50  --bmc1_min_bound                        0
% 39.72/5.50  --bmc1_max_bound                        -1
% 39.72/5.50  --bmc1_max_bound_default                -1
% 39.72/5.50  --bmc1_symbol_reachability              true
% 39.72/5.50  --bmc1_property_lemmas                  false
% 39.72/5.50  --bmc1_k_induction                      false
% 39.72/5.50  --bmc1_non_equiv_states                 false
% 39.72/5.50  --bmc1_deadlock                         false
% 39.72/5.50  --bmc1_ucm                              false
% 39.72/5.50  --bmc1_add_unsat_core                   none
% 39.72/5.50  --bmc1_unsat_core_children              false
% 39.72/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.72/5.50  --bmc1_out_stat                         full
% 39.72/5.50  --bmc1_ground_init                      false
% 39.72/5.50  --bmc1_pre_inst_next_state              false
% 39.72/5.50  --bmc1_pre_inst_state                   false
% 39.72/5.50  --bmc1_pre_inst_reach_state             false
% 39.72/5.50  --bmc1_out_unsat_core                   false
% 39.72/5.50  --bmc1_aig_witness_out                  false
% 39.72/5.50  --bmc1_verbose                          false
% 39.72/5.50  --bmc1_dump_clauses_tptp                false
% 39.72/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.72/5.50  --bmc1_dump_file                        -
% 39.72/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.72/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.72/5.50  --bmc1_ucm_extend_mode                  1
% 39.72/5.50  --bmc1_ucm_init_mode                    2
% 39.72/5.50  --bmc1_ucm_cone_mode                    none
% 39.72/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.72/5.50  --bmc1_ucm_relax_model                  4
% 39.72/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.72/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.72/5.50  --bmc1_ucm_layered_model                none
% 39.72/5.50  --bmc1_ucm_max_lemma_size               10
% 39.72/5.50  
% 39.72/5.50  ------ AIG Options
% 39.72/5.50  
% 39.72/5.50  --aig_mode                              false
% 39.72/5.50  
% 39.72/5.50  ------ Instantiation Options
% 39.72/5.50  
% 39.72/5.50  --instantiation_flag                    true
% 39.72/5.50  --inst_sos_flag                         true
% 39.72/5.50  --inst_sos_phase                        true
% 39.72/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.72/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.72/5.50  --inst_lit_sel_side                     none
% 39.72/5.50  --inst_solver_per_active                1400
% 39.72/5.50  --inst_solver_calls_frac                1.
% 39.72/5.50  --inst_passive_queue_type               priority_queues
% 39.72/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.72/5.50  --inst_passive_queues_freq              [25;2]
% 39.72/5.50  --inst_dismatching                      true
% 39.72/5.50  --inst_eager_unprocessed_to_passive     true
% 39.72/5.50  --inst_prop_sim_given                   true
% 39.72/5.50  --inst_prop_sim_new                     false
% 39.72/5.50  --inst_subs_new                         false
% 39.72/5.50  --inst_eq_res_simp                      false
% 39.72/5.50  --inst_subs_given                       false
% 39.72/5.50  --inst_orphan_elimination               true
% 39.72/5.50  --inst_learning_loop_flag               true
% 39.72/5.50  --inst_learning_start                   3000
% 39.72/5.50  --inst_learning_factor                  2
% 39.72/5.50  --inst_start_prop_sim_after_learn       3
% 39.72/5.50  --inst_sel_renew                        solver
% 39.72/5.50  --inst_lit_activity_flag                true
% 39.72/5.50  --inst_restr_to_given                   false
% 39.72/5.50  --inst_activity_threshold               500
% 39.72/5.50  --inst_out_proof                        true
% 39.72/5.50  
% 39.72/5.50  ------ Resolution Options
% 39.72/5.50  
% 39.72/5.50  --resolution_flag                       false
% 39.72/5.50  --res_lit_sel                           adaptive
% 39.72/5.50  --res_lit_sel_side                      none
% 39.72/5.50  --res_ordering                          kbo
% 39.72/5.50  --res_to_prop_solver                    active
% 39.72/5.50  --res_prop_simpl_new                    false
% 39.72/5.50  --res_prop_simpl_given                  true
% 39.72/5.50  --res_passive_queue_type                priority_queues
% 39.72/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.72/5.50  --res_passive_queues_freq               [15;5]
% 39.72/5.50  --res_forward_subs                      full
% 39.72/5.50  --res_backward_subs                     full
% 39.72/5.50  --res_forward_subs_resolution           true
% 39.72/5.50  --res_backward_subs_resolution          true
% 39.72/5.50  --res_orphan_elimination                true
% 39.72/5.50  --res_time_limit                        2.
% 39.72/5.50  --res_out_proof                         true
% 39.72/5.50  
% 39.72/5.50  ------ Superposition Options
% 39.72/5.50  
% 39.72/5.50  --superposition_flag                    true
% 39.72/5.50  --sup_passive_queue_type                priority_queues
% 39.72/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.72/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.72/5.50  --demod_completeness_check              fast
% 39.72/5.50  --demod_use_ground                      true
% 39.72/5.50  --sup_to_prop_solver                    passive
% 39.72/5.50  --sup_prop_simpl_new                    true
% 39.72/5.50  --sup_prop_simpl_given                  true
% 39.72/5.50  --sup_fun_splitting                     true
% 39.72/5.50  --sup_smt_interval                      50000
% 39.72/5.50  
% 39.72/5.50  ------ Superposition Simplification Setup
% 39.72/5.50  
% 39.72/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.72/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.72/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.72/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.72/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.72/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.72/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.72/5.50  --sup_immed_triv                        [TrivRules]
% 39.72/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.72/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.72/5.50  --sup_immed_bw_main                     []
% 39.72/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.72/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.72/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.72/5.50  --sup_input_bw                          []
% 39.72/5.50  
% 39.72/5.50  ------ Combination Options
% 39.72/5.50  
% 39.72/5.50  --comb_res_mult                         3
% 39.72/5.50  --comb_sup_mult                         2
% 39.72/5.50  --comb_inst_mult                        10
% 39.72/5.50  
% 39.72/5.50  ------ Debug Options
% 39.72/5.50  
% 39.72/5.50  --dbg_backtrace                         false
% 39.72/5.50  --dbg_dump_prop_clauses                 false
% 39.72/5.50  --dbg_dump_prop_clauses_file            -
% 39.72/5.50  --dbg_out_stat                          false
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  ------ Proving...
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  % SZS status Theorem for theBenchmark.p
% 39.72/5.50  
% 39.72/5.50   Resolution empty clause
% 39.72/5.50  
% 39.72/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.72/5.50  
% 39.72/5.50  fof(f23,conjecture,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f24,negated_conjecture,(
% 39.72/5.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 39.72/5.50    inference(negated_conjecture,[],[f23])).
% 39.72/5.50  
% 39.72/5.50  fof(f45,plain,(
% 39.72/5.50    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f24])).
% 39.72/5.50  
% 39.72/5.50  fof(f46,plain,(
% 39.72/5.50    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 39.72/5.50    inference(flattening,[],[f45])).
% 39.72/5.50  
% 39.72/5.50  fof(f55,plain,(
% 39.72/5.50    ( ! [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0) & v3_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.72/5.50    introduced(choice_axiom,[])).
% 39.72/5.50  
% 39.72/5.50  fof(f54,plain,(
% 39.72/5.50    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 39.72/5.50    introduced(choice_axiom,[])).
% 39.72/5.50  
% 39.72/5.50  fof(f56,plain,(
% 39.72/5.50    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 39.72/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f55,f54])).
% 39.72/5.50  
% 39.72/5.50  fof(f87,plain,(
% 39.72/5.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.72/5.50    inference(cnf_transformation,[],[f56])).
% 39.72/5.50  
% 39.72/5.50  fof(f16,axiom,(
% 39.72/5.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f36,plain,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.72/5.50    inference(ennf_transformation,[],[f16])).
% 39.72/5.50  
% 39.72/5.50  fof(f37,plain,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(flattening,[],[f36])).
% 39.72/5.50  
% 39.72/5.50  fof(f76,plain,(
% 39.72/5.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f37])).
% 39.72/5.50  
% 39.72/5.50  fof(f86,plain,(
% 39.72/5.50    l1_pre_topc(sK0)),
% 39.72/5.50    inference(cnf_transformation,[],[f56])).
% 39.72/5.50  
% 39.72/5.50  fof(f17,axiom,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f38,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f17])).
% 39.72/5.50  
% 39.72/5.50  fof(f77,plain,(
% 39.72/5.50    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f38])).
% 39.72/5.50  
% 39.72/5.50  fof(f10,axiom,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f31,plain,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.72/5.50    inference(ennf_transformation,[],[f10])).
% 39.72/5.50  
% 39.72/5.50  fof(f68,plain,(
% 39.72/5.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.72/5.50    inference(cnf_transformation,[],[f31])).
% 39.72/5.50  
% 39.72/5.50  fof(f15,axiom,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f50,plain,(
% 39.72/5.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.72/5.50    inference(nnf_transformation,[],[f15])).
% 39.72/5.50  
% 39.72/5.50  fof(f75,plain,(
% 39.72/5.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f50])).
% 39.72/5.50  
% 39.72/5.50  fof(f21,axiom,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f42,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f21])).
% 39.72/5.50  
% 39.72/5.50  fof(f43,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(flattening,[],[f42])).
% 39.72/5.50  
% 39.72/5.50  fof(f83,plain,(
% 39.72/5.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f43])).
% 39.72/5.50  
% 39.72/5.50  fof(f2,axiom,(
% 39.72/5.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f25,plain,(
% 39.72/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 39.72/5.50    inference(ennf_transformation,[],[f2])).
% 39.72/5.50  
% 39.72/5.50  fof(f26,plain,(
% 39.72/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 39.72/5.50    inference(flattening,[],[f25])).
% 39.72/5.50  
% 39.72/5.50  fof(f60,plain,(
% 39.72/5.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f26])).
% 39.72/5.50  
% 39.72/5.50  fof(f74,plain,(
% 39.72/5.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.72/5.50    inference(cnf_transformation,[],[f50])).
% 39.72/5.50  
% 39.72/5.50  fof(f4,axiom,(
% 39.72/5.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f62,plain,(
% 39.72/5.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f4])).
% 39.72/5.50  
% 39.72/5.50  fof(f3,axiom,(
% 39.72/5.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f27,plain,(
% 39.72/5.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 39.72/5.50    inference(ennf_transformation,[],[f3])).
% 39.72/5.50  
% 39.72/5.50  fof(f61,plain,(
% 39.72/5.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f27])).
% 39.72/5.50  
% 39.72/5.50  fof(f5,axiom,(
% 39.72/5.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f28,plain,(
% 39.72/5.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 39.72/5.50    inference(ennf_transformation,[],[f5])).
% 39.72/5.50  
% 39.72/5.50  fof(f63,plain,(
% 39.72/5.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 39.72/5.50    inference(cnf_transformation,[],[f28])).
% 39.72/5.50  
% 39.72/5.50  fof(f22,axiom,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f44,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f22])).
% 39.72/5.50  
% 39.72/5.50  fof(f53,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(nnf_transformation,[],[f44])).
% 39.72/5.50  
% 39.72/5.50  fof(f84,plain,(
% 39.72/5.50    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f53])).
% 39.72/5.50  
% 39.72/5.50  fof(f19,axiom,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f40,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f19])).
% 39.72/5.50  
% 39.72/5.50  fof(f52,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(nnf_transformation,[],[f40])).
% 39.72/5.50  
% 39.72/5.50  fof(f80,plain,(
% 39.72/5.50    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f52])).
% 39.72/5.50  
% 39.72/5.50  fof(f88,plain,(
% 39.72/5.50    v3_tops_1(sK1,sK0)),
% 39.72/5.50    inference(cnf_transformation,[],[f56])).
% 39.72/5.50  
% 39.72/5.50  fof(f20,axiom,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f41,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f20])).
% 39.72/5.50  
% 39.72/5.50  fof(f82,plain,(
% 39.72/5.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f41])).
% 39.72/5.50  
% 39.72/5.50  fof(f12,axiom,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f33,plain,(
% 39.72/5.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.72/5.50    inference(ennf_transformation,[],[f12])).
% 39.72/5.50  
% 39.72/5.50  fof(f70,plain,(
% 39.72/5.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.72/5.50    inference(cnf_transformation,[],[f33])).
% 39.72/5.50  
% 39.72/5.50  fof(f14,axiom,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f35,plain,(
% 39.72/5.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.72/5.50    inference(ennf_transformation,[],[f14])).
% 39.72/5.50  
% 39.72/5.50  fof(f49,plain,(
% 39.72/5.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.72/5.50    inference(nnf_transformation,[],[f35])).
% 39.72/5.50  
% 39.72/5.50  fof(f72,plain,(
% 39.72/5.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.72/5.50    inference(cnf_transformation,[],[f49])).
% 39.72/5.50  
% 39.72/5.50  fof(f9,axiom,(
% 39.72/5.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f30,plain,(
% 39.72/5.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.72/5.50    inference(ennf_transformation,[],[f9])).
% 39.72/5.50  
% 39.72/5.50  fof(f67,plain,(
% 39.72/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.72/5.50    inference(cnf_transformation,[],[f30])).
% 39.72/5.50  
% 39.72/5.50  fof(f1,axiom,(
% 39.72/5.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f47,plain,(
% 39.72/5.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.72/5.50    inference(nnf_transformation,[],[f1])).
% 39.72/5.50  
% 39.72/5.50  fof(f48,plain,(
% 39.72/5.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.72/5.50    inference(flattening,[],[f47])).
% 39.72/5.50  
% 39.72/5.50  fof(f57,plain,(
% 39.72/5.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.72/5.50    inference(cnf_transformation,[],[f48])).
% 39.72/5.50  
% 39.72/5.50  fof(f92,plain,(
% 39.72/5.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.72/5.50    inference(equality_resolution,[],[f57])).
% 39.72/5.50  
% 39.72/5.50  fof(f6,axiom,(
% 39.72/5.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f64,plain,(
% 39.72/5.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.72/5.50    inference(cnf_transformation,[],[f6])).
% 39.72/5.50  
% 39.72/5.50  fof(f85,plain,(
% 39.72/5.50    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f53])).
% 39.72/5.50  
% 39.72/5.50  fof(f18,axiom,(
% 39.72/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 39.72/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.72/5.50  
% 39.72/5.50  fof(f39,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(ennf_transformation,[],[f18])).
% 39.72/5.50  
% 39.72/5.50  fof(f51,plain,(
% 39.72/5.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.72/5.50    inference(nnf_transformation,[],[f39])).
% 39.72/5.50  
% 39.72/5.50  fof(f78,plain,(
% 39.72/5.50    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.72/5.50    inference(cnf_transformation,[],[f51])).
% 39.72/5.50  
% 39.72/5.50  fof(f89,plain,(
% 39.72/5.50    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 39.72/5.50    inference(cnf_transformation,[],[f56])).
% 39.72/5.50  
% 39.72/5.50  cnf(c_30,negated_conjecture,
% 39.72/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.72/5.50      inference(cnf_transformation,[],[f87]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1363,plain,
% 39.72/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_18,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ l1_pre_topc(X1) ),
% 39.72/5.50      inference(cnf_transformation,[],[f76]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_31,negated_conjecture,
% 39.72/5.50      ( l1_pre_topc(sK0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f86]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_538,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_539,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_538]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1353,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_19,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ l1_pre_topc(X1)
% 39.72/5.50      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f77]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_526,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_527,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_526]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1354,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 39.72/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1755,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0)))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 39.72/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1353,c_1354]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2663,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))
% 39.72/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1353,c_1755]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2806,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,X0))))
% 39.72/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1353,c_2663]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3657,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))))) = k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))) ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1363,c_2806]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_10,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.72/5.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 39.72/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_16,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.72/5.50      inference(cnf_transformation,[],[f75]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_247,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 39.72/5.50      inference(prop_impl,[status(thm)],[c_16]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_248,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.72/5.50      inference(renaming,[status(thm)],[c_247]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_302,plain,
% 39.72/5.50      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~ r1_tarski(X1,X0) ),
% 39.72/5.50      inference(bin_hyper_res,[status(thm)],[c_10,c_248]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1360,plain,
% 39.72/5.50      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 39.72/5.50      | r1_tarski(X1,X0) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_25,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ r1_tarski(X0,X2)
% 39.72/5.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 39.72/5.50      | ~ l1_pre_topc(X1) ),
% 39.72/5.50      inference(cnf_transformation,[],[f83]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_496,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ r1_tarski(X0,X2)
% 39.72/5.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_497,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ r1_tarski(X0,X1)
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_496]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1356,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 39.72/5.50      inference(cnf_transformation,[],[f60]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1369,plain,
% 39.72/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X2) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_4548,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X1),X2) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),X2) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1356,c_1369]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_8703,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 39.72/5.50      | r1_tarski(sK1,X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1363,c_4548]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_12355,plain,
% 39.72/5.50      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)),X1) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1360,c_8703]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_14795,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),X0) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))))) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3657,c_12355]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_14811,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),X0) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))) != iProver_top ),
% 39.72/5.50      inference(light_normalisation,[status(thm)],[c_14795,c_3657]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_33,plain,
% 39.72/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1404,plain,
% 39.72/5.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_539]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1405,plain,
% 39.72/5.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.72/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_17,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.72/5.50      inference(cnf_transformation,[],[f74]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1509,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_17]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2089,plain,
% 39.72/5.50      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_1509]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2090,plain,
% 39.72/5.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_2089]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_5,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f62]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1367,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_4,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 39.72/5.50      inference(cnf_transformation,[],[f61]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1368,plain,
% 39.72/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_6,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 39.72/5.50      inference(cnf_transformation,[],[f63]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1366,plain,
% 39.72/5.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3163,plain,
% 39.72/5.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 39.72/5.50      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1368,c_1366]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_9033,plain,
% 39.72/5.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1367,c_3163]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_9048,plain,
% 39.72/5.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_9033,c_1367]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_27,plain,
% 39.72/5.50      ( ~ v2_tops_1(X0,X1)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ l1_pre_topc(X1)
% 39.72/5.50      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 39.72/5.50      inference(cnf_transformation,[],[f84]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_466,plain,
% 39.72/5.50      ( ~ v2_tops_1(X0,X1)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | k1_tops_1(X1,X0) = k1_xboole_0
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_467,plain,
% 39.72/5.50      ( ~ v2_tops_1(X0,sK0)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_466]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_23,plain,
% 39.72/5.50      ( ~ v3_tops_1(X0,X1)
% 39.72/5.50      | v2_tops_1(k2_pre_topc(X1,X0),X1)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ l1_pre_topc(X1) ),
% 39.72/5.50      inference(cnf_transformation,[],[f80]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_29,negated_conjecture,
% 39.72/5.50      ( v3_tops_1(sK1,sK0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f88]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_453,plain,
% 39.72/5.50      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 39.72/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 39.72/5.50      | ~ l1_pre_topc(X0)
% 39.72/5.50      | sK1 != X1
% 39.72/5.50      | sK0 != X0 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_454,plain,
% 39.72/5.50      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 39.72/5.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ l1_pre_topc(sK0) ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_453]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_456,plain,
% 39.72/5.50      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 39.72/5.50      inference(global_propositional_subsumption,
% 39.72/5.50                [status(thm)],
% 39.72/5.50                [c_454,c_31,c_30]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_587,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k1_tops_1(sK0,X0) = k1_xboole_0
% 39.72/5.50      | k2_pre_topc(sK0,sK1) != X0
% 39.72/5.50      | sK0 != sK0 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_467,c_456]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_588,plain,
% 39.72/5.50      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_587]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1351,plain,
% 39.72/5.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
% 39.72/5.50      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1919,plain,
% 39.72/5.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 39.72/5.50      inference(global_propositional_subsumption,
% 39.72/5.50                [status(thm)],
% 39.72/5.50                [c_1351,c_30,c_588,c_1404]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1365,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.72/5.50      | r1_tarski(X0,X1) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_9149,plain,
% 39.72/5.50      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 39.72/5.50      | r1_tarski(sK1,X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1365,c_8703]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_9308,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
% 39.72/5.50      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1919,c_9149]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1690,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_5]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_23217,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_1690]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_23220,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_23217]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_24,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 39.72/5.50      | ~ l1_pre_topc(X1) ),
% 39.72/5.50      inference(cnf_transformation,[],[f82]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_514,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_515,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_514]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1355,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3060,plain,
% 39.72/5.50      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1365,c_1355]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1364,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X1) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3049,plain,
% 39.72/5.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1363,c_1364]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_12,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.72/5.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 39.72/5.50      inference(cnf_transformation,[],[f70]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_304,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 39.72/5.50      inference(bin_hyper_res,[status(thm)],[c_12,c_248]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1358,plain,
% 39.72/5.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 39.72/5.50      | r1_tarski(X1,X0) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_6078,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3049,c_1358]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_15,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.72/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.72/5.50      | ~ r1_tarski(X2,X0)
% 39.72/5.50      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 39.72/5.50      inference(cnf_transformation,[],[f72]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_307,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.72/5.50      | ~ r1_tarski(X2,X1)
% 39.72/5.50      | ~ r1_tarski(X0,X2)
% 39.72/5.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 39.72/5.50      inference(bin_hyper_res,[status(thm)],[c_15,c_248]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_706,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 39.72/5.50      inference(prop_impl,[status(thm)],[c_16]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_707,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.72/5.50      inference(renaming,[status(thm)],[c_706]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_748,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1)
% 39.72/5.50      | ~ r1_tarski(X0,X2)
% 39.72/5.50      | ~ r1_tarski(X2,X1)
% 39.72/5.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 39.72/5.50      inference(bin_hyper_res,[status(thm)],[c_307,c_707]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1348,plain,
% 39.72/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X2) != iProver_top
% 39.72/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.72/5.50      | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_104,plain,
% 39.72/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X2) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_785,plain,
% 39.72/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(X0,X2) != iProver_top
% 39.72/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.72/5.50      | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2044,plain,
% 39.72/5.50      ( r1_tarski(X0,X1) != iProver_top
% 39.72/5.50      | r1_tarski(X1,X2) != iProver_top
% 39.72/5.50      | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0)) = iProver_top ),
% 39.72/5.50      inference(global_propositional_subsumption,
% 39.72/5.50                [status(thm)],
% 39.72/5.50                [c_1348,c_104,c_785]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_6682,plain,
% 39.72/5.50      ( r1_tarski(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 39.72/5.50      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_6078,c_2044]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1584,plain,
% 39.72/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) | r1_tarski(sK1,X0) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_17]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1977,plain,
% 39.72/5.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_1584]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1978,plain,
% 39.72/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_1977]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1536,plain,
% 39.72/5.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_302]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2372,plain,
% 39.72/5.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_1536]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2374,plain,
% 39.72/5.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 39.72/5.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_2372]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2099,plain,
% 39.72/5.50      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_1509]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_20403,plain,
% 39.72/5.50      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 39.72/5.50      inference(instantiation,[status(thm)],[c_2099]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_20411,plain,
% 39.72/5.50      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_20403]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_110446,plain,
% 39.72/5.50      ( r1_tarski(X0,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
% 39.72/5.50      inference(global_propositional_subsumption,
% 39.72/5.50                [status(thm)],
% 39.72/5.50                [c_6682,c_33,c_1978,c_2374,c_20411]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_9,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.72/5.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f67]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_301,plain,
% 39.72/5.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 39.72/5.50      inference(bin_hyper_res,[status(thm)],[c_9,c_248]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1361,plain,
% 39.72/5.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 39.72/5.50      | r1_tarski(X1,X0) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_7796,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3049,c_1361]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_110452,plain,
% 39.72/5.50      ( r1_tarski(X0,k4_xboole_0(u1_struct_0(sK0),sK1)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = iProver_top ),
% 39.72/5.50      inference(light_normalisation,[status(thm)],[c_110446,c_7796]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_110461,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3060,c_110452]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_12363,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 39.72/5.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1360,c_1354]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_13024,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3049,c_12363]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_8235,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 39.72/5.50      inference(demodulation,[status(thm)],[c_7796,c_6078]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_13035,plain,
% 39.72/5.50      ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 39.72/5.50      inference(light_normalisation,[status(thm)],[c_13024,c_7796,c_8235]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_110501,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = iProver_top ),
% 39.72/5.50      inference(light_normalisation,[status(thm)],[c_110461,c_13035]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f92]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1370,plain,
% 39.72/5.50      ( r1_tarski(X0,X0) = iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3050,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1353,c_1364]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_4550,plain,
% 39.72/5.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.72/5.50      | r1_tarski(k2_pre_topc(sK0,X0),X1) = iProver_top
% 39.72/5.50      | r1_tarski(u1_struct_0(sK0),X1) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3050,c_1369]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_43813,plain,
% 39.72/5.50      ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
% 39.72/5.50      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1363,c_4550]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_44217,plain,
% 39.72/5.50      ( k3_subset_1(X0,k2_pre_topc(sK0,sK1)) = k4_xboole_0(X0,k2_pre_topc(sK0,sK1))
% 39.72/5.50      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_43813,c_1361]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_44447,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1370,c_44217]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_44218,plain,
% 39.72/5.50      ( k3_subset_1(X0,k3_subset_1(X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 39.72/5.50      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_43813,c_1358]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_44515,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1370,c_44218]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_44522,plain,
% 39.72/5.50      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.72/5.50      inference(light_normalisation,[status(thm)],[c_44515,c_44447]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_110502,plain,
% 39.72/5.50      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) != iProver_top
% 39.72/5.50      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 39.72/5.50      inference(demodulation,[status(thm)],[c_110501,c_44447,c_44522]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_125658,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top ),
% 39.72/5.50      inference(global_propositional_subsumption,
% 39.72/5.50                [status(thm)],
% 39.72/5.50                [c_14811,c_33,c_1405,c_2090,c_9048,c_9308,c_23220,c_110502]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_7,plain,
% 39.72/5.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.72/5.50      inference(cnf_transformation,[],[f64]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_3161,plain,
% 39.72/5.50      ( r1_tarski(X0,k4_xboole_0(X0,X1)) = iProver_top
% 39.72/5.50      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_7,c_1368]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1507,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1363,c_1355]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_4552,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 39.72/5.50      | r1_tarski(sK1,X0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_1507,c_1369]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_5299,plain,
% 39.72/5.50      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 39.72/5.50      | r1_tarski(sK1,k4_xboole_0(X0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_4552,c_1366]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_26,plain,
% 39.72/5.50      ( v2_tops_1(X0,X1)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ l1_pre_topc(X1)
% 39.72/5.50      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 39.72/5.50      inference(cnf_transformation,[],[f85]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_481,plain,
% 39.72/5.50      ( v2_tops_1(X0,X1)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | k1_tops_1(X1,X0) != k1_xboole_0
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_482,plain,
% 39.72/5.50      ( v2_tops_1(X0,sK0)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_481]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_21,plain,
% 39.72/5.50      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 39.72/5.50      | ~ v2_tops_1(X1,X0)
% 39.72/5.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 39.72/5.50      | ~ l1_pre_topc(X0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f78]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_28,negated_conjecture,
% 39.72/5.50      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 39.72/5.50      inference(cnf_transformation,[],[f89]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_427,plain,
% 39.72/5.50      ( ~ v2_tops_1(X0,X1)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.72/5.50      | ~ l1_pre_topc(X1)
% 39.72/5.50      | k3_subset_1(u1_struct_0(X1),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
% 39.72/5.50      | sK0 != X1 ),
% 39.72/5.50      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_428,plain,
% 39.72/5.50      ( ~ v2_tops_1(X0,sK0)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ l1_pre_topc(sK0)
% 39.72/5.50      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 39.72/5.50      inference(unflattening,[status(thm)],[c_427]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_432,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | ~ v2_tops_1(X0,sK0)
% 39.72/5.50      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 39.72/5.50      inference(global_propositional_subsumption,[status(thm)],[c_428,c_31]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_433,plain,
% 39.72/5.50      ( ~ v2_tops_1(X0,sK0)
% 39.72/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 39.72/5.50      inference(renaming,[status(thm)],[c_432]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_573,plain,
% 39.72/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.72/5.50      | k1_tops_1(sK0,X0) != k1_xboole_0
% 39.72/5.50      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1) ),
% 39.72/5.50      inference(resolution,[status(thm)],[c_482,c_433]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_1352,plain,
% 39.72/5.50      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 39.72/5.50      | k3_subset_1(u1_struct_0(sK0),X0) != k3_subset_1(u1_struct_0(sK0),sK1)
% 39.72/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_2453,plain,
% 39.72/5.50      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 39.72/5.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.72/5.50      inference(equality_resolution,[status(thm)],[c_1352]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_14982,plain,
% 39.72/5.50      ( r1_tarski(sK1,k4_xboole_0(X0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 39.72/5.50      inference(global_propositional_subsumption,
% 39.72/5.50                [status(thm)],
% 39.72/5.50                [c_5299,c_33,c_2453]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_14988,plain,
% 39.72/5.50      ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) != iProver_top ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_3161,c_14982]) ).
% 39.72/5.50  
% 39.72/5.50  cnf(c_125685,plain,
% 39.72/5.50      ( $false ),
% 39.72/5.50      inference(superposition,[status(thm)],[c_125658,c_14988]) ).
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.72/5.50  
% 39.72/5.50  ------                               Statistics
% 39.72/5.50  
% 39.72/5.50  ------ General
% 39.72/5.50  
% 39.72/5.50  abstr_ref_over_cycles:                  0
% 39.72/5.50  abstr_ref_under_cycles:                 0
% 39.72/5.50  gc_basic_clause_elim:                   0
% 39.72/5.50  forced_gc_time:                         0
% 39.72/5.50  parsing_time:                           0.011
% 39.72/5.50  unif_index_cands_time:                  0.
% 39.72/5.50  unif_index_add_time:                    0.
% 39.72/5.50  orderings_time:                         0.
% 39.72/5.50  out_proof_time:                         0.031
% 39.72/5.50  total_time:                             4.739
% 39.72/5.50  num_of_symbols:                         47
% 39.72/5.50  num_of_terms:                           200342
% 39.72/5.50  
% 39.72/5.50  ------ Preprocessing
% 39.72/5.50  
% 39.72/5.50  num_of_splits:                          0
% 39.72/5.50  num_of_split_atoms:                     0
% 39.72/5.50  num_of_reused_defs:                     0
% 39.72/5.50  num_eq_ax_congr_red:                    16
% 39.72/5.50  num_of_sem_filtered_clauses:            1
% 39.72/5.50  num_of_subtypes:                        0
% 39.72/5.50  monotx_restored_types:                  0
% 39.72/5.50  sat_num_of_epr_types:                   0
% 39.72/5.50  sat_num_of_non_cyclic_types:            0
% 39.72/5.50  sat_guarded_non_collapsed_types:        0
% 39.72/5.50  num_pure_diseq_elim:                    0
% 39.72/5.50  simp_replaced_by:                       0
% 39.72/5.50  res_preprocessed:                       127
% 39.72/5.50  prep_upred:                             0
% 39.72/5.50  prep_unflattend:                        11
% 39.72/5.50  smt_new_axioms:                         0
% 39.72/5.50  pred_elim_cands:                        2
% 39.72/5.50  pred_elim:                              4
% 39.72/5.50  pred_elim_cl:                           6
% 39.72/5.50  pred_elim_cycles:                       6
% 39.72/5.50  merged_defs:                            8
% 39.72/5.50  merged_defs_ncl:                        0
% 39.72/5.50  bin_hyper_res:                          18
% 39.72/5.50  prep_cycles:                            4
% 39.72/5.50  pred_elim_time:                         0.005
% 39.72/5.50  splitting_time:                         0.
% 39.72/5.50  sem_filter_time:                        0.
% 39.72/5.50  monotx_time:                            0.
% 39.72/5.50  subtype_inf_time:                       0.
% 39.72/5.50  
% 39.72/5.50  ------ Problem properties
% 39.72/5.50  
% 39.72/5.50  clauses:                                25
% 39.72/5.50  conjectures:                            1
% 39.72/5.50  epr:                                    3
% 39.72/5.50  horn:                                   25
% 39.72/5.50  ground:                                 3
% 39.72/5.50  unary:                                  4
% 39.72/5.50  binary:                                 15
% 39.72/5.50  lits:                                   55
% 39.72/5.50  lits_eq:                                12
% 39.72/5.50  fd_pure:                                0
% 39.72/5.50  fd_pseudo:                              0
% 39.72/5.50  fd_cond:                                1
% 39.72/5.50  fd_pseudo_cond:                         1
% 39.72/5.50  ac_symbols:                             0
% 39.72/5.50  
% 39.72/5.50  ------ Propositional Solver
% 39.72/5.50  
% 39.72/5.50  prop_solver_calls:                      62
% 39.72/5.50  prop_fast_solver_calls:                 3220
% 39.72/5.50  smt_solver_calls:                       0
% 39.72/5.50  smt_fast_solver_calls:                  0
% 39.72/5.50  prop_num_of_clauses:                    61596
% 39.72/5.50  prop_preprocess_simplified:             71911
% 39.72/5.50  prop_fo_subsumed:                       221
% 39.72/5.50  prop_solver_time:                       0.
% 39.72/5.50  smt_solver_time:                        0.
% 39.72/5.50  smt_fast_solver_time:                   0.
% 39.72/5.50  prop_fast_solver_time:                  0.
% 39.72/5.50  prop_unsat_core_time:                   0.
% 39.72/5.50  
% 39.72/5.50  ------ QBF
% 39.72/5.50  
% 39.72/5.50  qbf_q_res:                              0
% 39.72/5.50  qbf_num_tautologies:                    0
% 39.72/5.50  qbf_prep_cycles:                        0
% 39.72/5.50  
% 39.72/5.50  ------ BMC1
% 39.72/5.50  
% 39.72/5.50  bmc1_current_bound:                     -1
% 39.72/5.50  bmc1_last_solved_bound:                 -1
% 39.72/5.50  bmc1_unsat_core_size:                   -1
% 39.72/5.50  bmc1_unsat_core_parents_size:           -1
% 39.72/5.50  bmc1_merge_next_fun:                    0
% 39.72/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.72/5.50  
% 39.72/5.50  ------ Instantiation
% 39.72/5.50  
% 39.72/5.50  inst_num_of_clauses:                    3388
% 39.72/5.50  inst_num_in_passive:                    677
% 39.72/5.50  inst_num_in_active:                     3865
% 39.72/5.50  inst_num_in_unprocessed:                1654
% 39.72/5.50  inst_num_of_loops:                      4089
% 39.72/5.50  inst_num_of_learning_restarts:          1
% 39.72/5.50  inst_num_moves_active_passive:          224
% 39.72/5.50  inst_lit_activity:                      0
% 39.72/5.50  inst_lit_activity_moves:                3
% 39.72/5.50  inst_num_tautologies:                   0
% 39.72/5.50  inst_num_prop_implied:                  0
% 39.72/5.50  inst_num_existing_simplified:           0
% 39.72/5.50  inst_num_eq_res_simplified:             0
% 39.72/5.50  inst_num_child_elim:                    0
% 39.72/5.50  inst_num_of_dismatching_blockings:      14134
% 39.72/5.50  inst_num_of_non_proper_insts:           15261
% 39.72/5.50  inst_num_of_duplicates:                 0
% 39.72/5.50  inst_inst_num_from_inst_to_res:         0
% 39.72/5.50  inst_dismatching_checking_time:         0.
% 39.72/5.50  
% 39.72/5.50  ------ Resolution
% 39.72/5.50  
% 39.72/5.50  res_num_of_clauses:                     35
% 39.72/5.50  res_num_in_passive:                     35
% 39.72/5.50  res_num_in_active:                      0
% 39.72/5.50  res_num_of_loops:                       131
% 39.72/5.50  res_forward_subset_subsumed:            409
% 39.72/5.50  res_backward_subset_subsumed:           0
% 39.72/5.50  res_forward_subsumed:                   0
% 39.72/5.50  res_backward_subsumed:                  0
% 39.72/5.50  res_forward_subsumption_resolution:     0
% 39.72/5.50  res_backward_subsumption_resolution:    0
% 39.72/5.50  res_clause_to_clause_subsumption:       65234
% 39.72/5.50  res_orphan_elimination:                 0
% 39.72/5.50  res_tautology_del:                      1127
% 39.72/5.50  res_num_eq_res_simplified:              0
% 39.72/5.50  res_num_sel_changes:                    0
% 39.72/5.50  res_moves_from_active_to_pass:          0
% 39.72/5.50  
% 39.72/5.50  ------ Superposition
% 39.72/5.50  
% 39.72/5.50  sup_time_total:                         0.
% 39.72/5.50  sup_time_generating:                    0.
% 39.72/5.50  sup_time_sim_full:                      0.
% 39.72/5.50  sup_time_sim_immed:                     0.
% 39.72/5.50  
% 39.72/5.50  sup_num_of_clauses:                     8831
% 39.72/5.50  sup_num_in_active:                      728
% 39.72/5.50  sup_num_in_passive:                     8103
% 39.72/5.50  sup_num_of_loops:                       816
% 39.72/5.50  sup_fw_superposition:                   9497
% 39.72/5.50  sup_bw_superposition:                   7011
% 39.72/5.50  sup_immediate_simplified:               8001
% 39.72/5.50  sup_given_eliminated:                   3
% 39.72/5.50  comparisons_done:                       0
% 39.72/5.50  comparisons_avoided:                    0
% 39.72/5.50  
% 39.72/5.50  ------ Simplifications
% 39.72/5.50  
% 39.72/5.50  
% 39.72/5.50  sim_fw_subset_subsumed:                 1435
% 39.72/5.50  sim_bw_subset_subsumed:                 332
% 39.72/5.50  sim_fw_subsumed:                        1645
% 39.72/5.50  sim_bw_subsumed:                        310
% 39.72/5.50  sim_fw_subsumption_res:                 0
% 39.72/5.50  sim_bw_subsumption_res:                 0
% 39.72/5.50  sim_tautology_del:                      91
% 39.72/5.50  sim_eq_tautology_del:                   1618
% 39.72/5.50  sim_eq_res_simp:                        1
% 39.72/5.50  sim_fw_demodulated:                     3655
% 39.72/5.50  sim_bw_demodulated:                     124
% 39.72/5.50  sim_light_normalised:                   2531
% 39.72/5.50  sim_joinable_taut:                      0
% 39.72/5.50  sim_joinable_simp:                      0
% 39.72/5.50  sim_ac_normalised:                      0
% 39.72/5.50  sim_smt_subsumption:                    0
% 39.72/5.50  
%------------------------------------------------------------------------------
