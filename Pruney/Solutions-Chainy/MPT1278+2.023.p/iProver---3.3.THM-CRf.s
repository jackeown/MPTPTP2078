%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:36 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  194 (1209 expanded)
%              Number of clauses        :  121 ( 396 expanded)
%              Number of leaves         :   22 ( 286 expanded)
%              Depth                    :   27
%              Number of atoms          :  582 (5323 expanded)
%              Number of equality atoms :  207 (1167 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK2
        & v3_tops_1(sK2,X0)
        & v3_pre_topc(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK1)
          & v3_pre_topc(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( k1_xboole_0 != sK2
    & v3_tops_1(sK2,sK1)
    & v3_pre_topc(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f53,f52])).

fof(f81,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    v3_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1370,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1372,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1893,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1370,c_1372])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_391,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_392,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_30])).

cnf(c_397,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_438,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != k1_tops_1(sK1,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_397])).

cnf(c_439,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_30])).

cnf(c_444,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
    inference(renaming,[status(thm)],[c_443])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | k2_pre_topc(X1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X2) != k1_tops_1(sK1,X3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_444])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_30])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_1365,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_2347,plain,
    ( k1_tops_1(sK1,X0) != k1_xboole_0
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK1),k1_xboole_0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1365])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1368,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_1363,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1579,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1368,c_1363])).

cnf(c_24,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_621,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_622,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_25,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,negated_conjecture,
    ( v3_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_357,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_358,plain,
    ( v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_360,plain,
    ( v2_tops_1(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_30,c_29])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_622,c_360])).

cnf(c_839,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_841,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_839,c_29])).

cnf(c_1580,plain,
    ( k1_tops_1(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1579,c_841])).

cnf(c_23,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_636,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_637,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_18,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_663,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_664,plain,
    ( ~ v2_tops_1(X0,sK1)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_16,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_693,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_694,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_752,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X1) = k2_struct_0(sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_664,c_694])).

cnf(c_753,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_765,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_753,c_7])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_637,c_765])).

cnf(c_1361,plain,
    ( k1_tops_1(sK1,X0) != k1_xboole_0
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_1595,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k2_struct_0(sK1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1580,c_1361])).

cnf(c_817,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k1_xboole_0) != k1_xboole_0
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_1478,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1722,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1595,c_817,c_1478,c_1580])).

cnf(c_2351,plain,
    ( k1_tops_1(sK1,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2347,c_1722])).

cnf(c_1479,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_1486,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2359,plain,
    ( k1_tops_1(sK1,k1_xboole_0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_4612,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2351,c_1479,c_1486,c_1580,c_2359])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1376,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_1366,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_1947,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1376,c_1366])).

cnf(c_1373,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X0),X0)
    | k2_subset_1(X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1371,plain,
    ( k2_subset_1(X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1380,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1371,c_5])).

cnf(c_2344,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1380])).

cnf(c_3864,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_2344])).

cnf(c_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3983,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3864,c_79])).

cnf(c_3989,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1947,c_3983])).

cnf(c_4614,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_4612,c_3989])).

cnf(c_1894,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1368,c_1372])).

cnf(c_28,negated_conjecture,
    ( v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_417,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_418,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_30])).

cnf(c_423,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | k2_pre_topc(X1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X2) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_423])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_30])).

cnf(c_1364,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_2011,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k3_subset_1(u1_struct_0(sK1),sK2)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_1364])).

cnf(c_830,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_765,c_360])).

cnf(c_831,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_833,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_831,c_29])).

cnf(c_2012,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2011,c_833])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1682,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1683,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(c_2053,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2012,c_34,c_1683])).

cnf(c_2055,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2053,c_1894])).

cnf(c_4634,plain,
    ( k3_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4614,c_2055])).

cnf(c_1954,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_1372])).

cnf(c_3461,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,X1)))) = k3_subset_1(X0,k3_subset_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_1954])).

cnf(c_3993,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)))) = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1370,c_3461])).

cnf(c_4001,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3993,c_1893,c_3989])).

cnf(c_4641,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4634,c_4001])).

cnf(c_1067,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1406,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_1407,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1066,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1087,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4641,c_1407,c_1087,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.34/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.00  
% 3.34/1.00  ------  iProver source info
% 3.34/1.00  
% 3.34/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.00  git: non_committed_changes: false
% 3.34/1.00  git: last_make_outside_of_git: false
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    ""
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         true
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     num_symb
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       true
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     true
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.34/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_input_bw                          []
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  ------ Parsing...
% 3.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.00  ------ Proving...
% 3.34/1.00  ------ Problem Properties 
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  clauses                                 21
% 3.34/1.00  conjectures                             2
% 3.34/1.00  EPR                                     3
% 3.34/1.00  Horn                                    20
% 3.34/1.00  unary                                   9
% 3.34/1.00  binary                                  5
% 3.34/1.00  lits                                    41
% 3.34/1.00  lits eq                                 15
% 3.34/1.00  fd_pure                                 0
% 3.34/1.00  fd_pseudo                               0
% 3.34/1.00  fd_cond                                 0
% 3.34/1.00  fd_pseudo_cond                          1
% 3.34/1.00  AC symbols                              0
% 3.34/1.00  
% 3.34/1.00  ------ Schedule dynamic 5 is on 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  Current options:
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    ""
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         true
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     none
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       false
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     true
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.34/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_input_bw                          []
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ Proving...
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS status Theorem for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  fof(f9,axiom,(
% 3.34/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f66,plain,(
% 3.34/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f9])).
% 3.34/1.00  
% 3.34/1.00  fof(f7,axiom,(
% 3.34/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f25,plain,(
% 3.34/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f7])).
% 3.34/1.00  
% 3.34/1.00  fof(f63,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f25])).
% 3.34/1.00  
% 3.34/1.00  fof(f11,axiom,(
% 3.34/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f29,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f11])).
% 3.34/1.00  
% 3.34/1.00  fof(f30,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(flattening,[],[f29])).
% 3.34/1.00  
% 3.34/1.00  fof(f68,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f30])).
% 3.34/1.00  
% 3.34/1.00  fof(f16,axiom,(
% 3.34/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f37,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f16])).
% 3.34/1.00  
% 3.34/1.00  fof(f50,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(nnf_transformation,[],[f37])).
% 3.34/1.00  
% 3.34/1.00  fof(f77,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f50])).
% 3.34/1.00  
% 3.34/1.00  fof(f14,axiom,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f33,plain,(
% 3.34/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f14])).
% 3.34/1.00  
% 3.34/1.00  fof(f34,plain,(
% 3.34/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.34/1.00    inference(flattening,[],[f33])).
% 3.34/1.00  
% 3.34/1.00  fof(f74,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f34])).
% 3.34/1.00  
% 3.34/1.00  fof(f19,conjecture,(
% 3.34/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f20,negated_conjecture,(
% 3.34/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 3.34/1.00    inference(negated_conjecture,[],[f19])).
% 3.34/1.00  
% 3.34/1.00  fof(f41,plain,(
% 3.34/1.00    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f20])).
% 3.34/1.00  
% 3.34/1.00  fof(f42,plain,(
% 3.34/1.00    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.34/1.00    inference(flattening,[],[f41])).
% 3.34/1.00  
% 3.34/1.00  fof(f53,plain,(
% 3.34/1.00    ( ! [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_tops_1(sK2,X0) & v3_pre_topc(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f52,plain,(
% 3.34/1.00    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK1) & v3_pre_topc(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f54,plain,(
% 3.34/1.00    (k1_xboole_0 != sK2 & v3_tops_1(sK2,sK1) & v3_pre_topc(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f53,f52])).
% 3.34/1.00  
% 3.34/1.00  fof(f81,plain,(
% 3.34/1.00    v2_pre_topc(sK1)),
% 3.34/1.00    inference(cnf_transformation,[],[f54])).
% 3.34/1.00  
% 3.34/1.00  fof(f82,plain,(
% 3.34/1.00    l1_pre_topc(sK1)),
% 3.34/1.00    inference(cnf_transformation,[],[f54])).
% 3.34/1.00  
% 3.34/1.00  fof(f83,plain,(
% 3.34/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.34/1.00    inference(cnf_transformation,[],[f54])).
% 3.34/1.00  
% 3.34/1.00  fof(f15,axiom,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f35,plain,(
% 3.34/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f15])).
% 3.34/1.00  
% 3.34/1.00  fof(f36,plain,(
% 3.34/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(flattening,[],[f35])).
% 3.34/1.00  
% 3.34/1.00  fof(f75,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f36])).
% 3.34/1.00  
% 3.34/1.00  fof(f17,axiom,(
% 3.34/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f38,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f17])).
% 3.34/1.00  
% 3.34/1.00  fof(f51,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(nnf_transformation,[],[f38])).
% 3.34/1.00  
% 3.34/1.00  fof(f78,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f51])).
% 3.34/1.00  
% 3.34/1.00  fof(f18,axiom,(
% 3.34/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f39,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f18])).
% 3.34/1.00  
% 3.34/1.00  fof(f40,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(flattening,[],[f39])).
% 3.34/1.00  
% 3.34/1.00  fof(f80,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f40])).
% 3.34/1.00  
% 3.34/1.00  fof(f85,plain,(
% 3.34/1.00    v3_tops_1(sK2,sK1)),
% 3.34/1.00    inference(cnf_transformation,[],[f54])).
% 3.34/1.00  
% 3.34/1.00  fof(f79,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f51])).
% 3.34/1.00  
% 3.34/1.00  fof(f13,axiom,(
% 3.34/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f32,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f13])).
% 3.34/1.00  
% 3.34/1.00  fof(f49,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(nnf_transformation,[],[f32])).
% 3.34/1.00  
% 3.34/1.00  fof(f72,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f49])).
% 3.34/1.00  
% 3.34/1.00  fof(f12,axiom,(
% 3.34/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f31,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f12])).
% 3.34/1.00  
% 3.34/1.00  fof(f48,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.34/1.00    inference(nnf_transformation,[],[f31])).
% 3.34/1.00  
% 3.34/1.00  fof(f70,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f48])).
% 3.34/1.00  
% 3.34/1.00  fof(f6,axiom,(
% 3.34/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f24,plain,(
% 3.34/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f6])).
% 3.34/1.00  
% 3.34/1.00  fof(f62,plain,(
% 3.34/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f24])).
% 3.34/1.00  
% 3.34/1.00  fof(f2,axiom,(
% 3.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f23,plain,(
% 3.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f2])).
% 3.34/1.00  
% 3.34/1.00  fof(f43,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.00    inference(nnf_transformation,[],[f23])).
% 3.34/1.00  
% 3.34/1.00  fof(f44,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.00    inference(rectify,[],[f43])).
% 3.34/1.00  
% 3.34/1.00  fof(f45,plain,(
% 3.34/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f46,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 3.34/1.00  
% 3.34/1.00  fof(f57,plain,(
% 3.34/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f1,axiom,(
% 3.34/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f21,plain,(
% 3.34/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.34/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.34/1.00  
% 3.34/1.00  fof(f22,plain,(
% 3.34/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f21])).
% 3.34/1.00  
% 3.34/1.00  fof(f55,plain,(
% 3.34/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f22])).
% 3.34/1.00  
% 3.34/1.00  fof(f3,axiom,(
% 3.34/1.00    v1_xboole_0(k1_xboole_0)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f59,plain,(
% 3.34/1.00    v1_xboole_0(k1_xboole_0)),
% 3.34/1.00    inference(cnf_transformation,[],[f3])).
% 3.34/1.00  
% 3.34/1.00  fof(f8,axiom,(
% 3.34/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f26,plain,(
% 3.34/1.00    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f8])).
% 3.34/1.00  
% 3.34/1.00  fof(f47,plain,(
% 3.34/1.00    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/1.00    inference(nnf_transformation,[],[f26])).
% 3.34/1.00  
% 3.34/1.00  fof(f64,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f47])).
% 3.34/1.00  
% 3.34/1.00  fof(f4,axiom,(
% 3.34/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f60,plain,(
% 3.34/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.34/1.00    inference(cnf_transformation,[],[f4])).
% 3.34/1.00  
% 3.34/1.00  fof(f84,plain,(
% 3.34/1.00    v3_pre_topc(sK2,sK1)),
% 3.34/1.00    inference(cnf_transformation,[],[f54])).
% 3.34/1.00  
% 3.34/1.00  fof(f86,plain,(
% 3.34/1.00    k1_xboole_0 != sK2),
% 3.34/1.00    inference(cnf_transformation,[],[f54])).
% 3.34/1.00  
% 3.34/1.00  cnf(c_11,plain,
% 3.34/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1370,plain,
% 3.34/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_8,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1372,plain,
% 3.34/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.34/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1893,plain,
% 3.34/1.00      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1370,c_1372]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_14,plain,
% 3.34/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_21,plain,
% 3.34/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.34/1.00      | v4_pre_topc(X1,X0)
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.34/1.00      | ~ l1_pre_topc(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_19,plain,
% 3.34/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.34/1.00      | ~ l1_pre_topc(X0)
% 3.34/1.00      | ~ v2_pre_topc(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_31,negated_conjecture,
% 3.34/1.00      ( v2_pre_topc(sK1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_391,plain,
% 3.34/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.34/1.00      | ~ l1_pre_topc(X0)
% 3.34/1.00      | sK1 != X0 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_392,plain,
% 3.34/1.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(sK1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_30,negated_conjecture,
% 3.34/1.00      ( l1_pre_topc(sK1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_396,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_392,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_397,plain,
% 3.34/1.00      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_396]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_438,plain,
% 3.34/1.00      ( v4_pre_topc(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(X1),X0) != k1_tops_1(sK1,X2)
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_397]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_439,plain,
% 3.34/1.00      ( v4_pre_topc(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(sK1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_438]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_443,plain,
% 3.34/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | v4_pre_topc(X0,sK1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_439,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_444,plain,
% 3.34/1.00      ( v4_pre_topc(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_443]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_565,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | X2 != X0
% 3.34/1.00      | k2_pre_topc(X1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X2) != k1_tops_1(sK1,X3)
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_444]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_566,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(sK1)
% 3.34/1.00      | k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_570,plain,
% 3.34/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_566,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_571,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1) ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_570]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1365,plain,
% 3.34/1.00      ( k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != k1_tops_1(sK1,X1)
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.34/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2347,plain,
% 3.34/1.00      ( k1_tops_1(sK1,X0) != k1_xboole_0
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK1),k1_xboole_0)
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1893,c_1365]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_29,negated_conjecture,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.34/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1368,plain,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_20,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_651,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_652,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_651]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1363,plain,
% 3.34/1.00      ( k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1579,plain,
% 3.34/1.00      ( k1_tops_1(sK1,k1_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1368,c_1363]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_24,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_621,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_622,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0 ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_621]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_25,plain,
% 3.34/1.00      ( ~ v3_tops_1(X0,X1)
% 3.34/1.00      | v2_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_27,negated_conjecture,
% 3.34/1.00      ( v3_tops_1(sK2,sK1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_357,plain,
% 3.34/1.00      ( v2_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | sK1 != X1
% 3.34/1.00      | sK2 != X0 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_358,plain,
% 3.34/1.00      ( v2_tops_1(sK2,sK1)
% 3.34/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(sK1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_360,plain,
% 3.34/1.00      ( v2_tops_1(sK2,sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_358,c_30,c_29]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_838,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0
% 3.34/1.00      | sK1 != sK1
% 3.34/1.00      | sK2 != X0 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_622,c_360]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_839,plain,
% 3.34/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_838]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_841,plain,
% 3.34/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_839,c_29]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1580,plain,
% 3.34/1.00      ( k1_tops_1(sK1,k1_xboole_0) = k1_xboole_0 ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_1579,c_841]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_23,plain,
% 3.34/1.00      ( v2_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_636,plain,
% 3.34/1.00      ( v2_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_637,plain,
% 3.34/1.00      ( v2_tops_1(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0 ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_636]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_18,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,X1)
% 3.34/1.00      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_663,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,X1)
% 3.34/1.00      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_664,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,sK1)
% 3.34/1.00      | v1_tops_1(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_663]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_16,plain,
% 3.34/1.00      ( ~ v1_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_693,plain,
% 3.34/1.00      ( ~ v1_tops_1(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_694,plain,
% 3.34/1.00      ( ~ v1_tops_1(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_693]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_752,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,X1) = k2_struct_0(sK1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != X1
% 3.34/1.00      | sK1 != sK1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_664,c_694]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_753,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_752]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_7,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_765,plain,
% 3.34/1.00      ( ~ v2_tops_1(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_753,c_7]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_815,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(resolution,[status(thm)],[c_637,c_765]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1361,plain,
% 3.34/1.00      ( k1_tops_1(sK1,X0) != k1_xboole_0
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1595,plain,
% 3.34/1.00      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k2_struct_0(sK1)
% 3.34/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1580,c_1361]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_817,plain,
% 3.34/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k1_tops_1(sK1,k1_xboole_0) != k1_xboole_0
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_815]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1478,plain,
% 3.34/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1722,plain,
% 3.34/1.00      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),k1_xboole_0)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_1595,c_817,c_1478,c_1580]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2351,plain,
% 3.34/1.00      ( k1_tops_1(sK1,X0) != k1_xboole_0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1)
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_2347,c_1722]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1479,plain,
% 3.34/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1483,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1484,plain,
% 3.34/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1486,plain,
% 3.34/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.34/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1484]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2359,plain,
% 3.34/1.00      ( k1_tops_1(sK1,k1_xboole_0) != k1_xboole_0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1)
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.34/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_2351]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4612,plain,
% 3.34/1.00      ( k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2351,c_1479,c_1486,c_1580,c_2359]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2,plain,
% 3.34/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1376,plain,
% 3.34/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.34/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_0,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4,plain,
% 3.34/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_346,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_347,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_346]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1366,plain,
% 3.34/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1947,plain,
% 3.34/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1376,c_1366]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1373,plain,
% 3.34/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_10,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.00      | ~ r1_tarski(k3_subset_1(X1,X0),X0)
% 3.34/1.00      | k2_subset_1(X1) = X0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1371,plain,
% 3.34/1.00      ( k2_subset_1(X0) = X1
% 3.34/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.34/1.00      | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5,plain,
% 3.34/1.00      ( k2_subset_1(X0) = X0 ),
% 3.34/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1380,plain,
% 3.34/1.00      ( X0 = X1
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/1.00      | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_1371,c_5]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2344,plain,
% 3.34/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0
% 3.34/1.00      | m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
% 3.34/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1893,c_1380]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3864,plain,
% 3.34/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0
% 3.34/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 3.34/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1373,c_2344]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_79,plain,
% 3.34/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3983,plain,
% 3.34/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0
% 3.34/1.00      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) != iProver_top ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_3864,c_79]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3989,plain,
% 3.34/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1947,c_3983]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4614,plain,
% 3.34/1.00      ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_4612,c_3989]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1894,plain,
% 3.34/1.00      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1368,c_1372]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_28,negated_conjecture,
% 3.34/1.00      ( v3_pre_topc(sK2,sK1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_417,plain,
% 3.34/1.00      ( v4_pre_topc(X0,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(X1),X0) != sK2
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_418,plain,
% 3.34/1.00      ( v4_pre_topc(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(sK1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_422,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | v4_pre_topc(X0,sK1)
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_418,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_423,plain,
% 3.34/1.00      ( v4_pre_topc(X0,sK1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_422]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_589,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(X1)
% 3.34/1.00      | X2 != X0
% 3.34/1.00      | k2_pre_topc(X1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X2) != sK2
% 3.34/1.00      | sK1 != X1 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_423]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_590,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ l1_pre_topc(sK1)
% 3.34/1.00      | k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_589]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_594,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_590,c_30]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1364,plain,
% 3.34/1.00      ( k2_pre_topc(sK1,X0) = X0
% 3.34/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 3.34/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2011,plain,
% 3.34/1.00      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k3_subset_1(u1_struct_0(sK1),sK2)
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1894,c_1364]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_830,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.34/1.00      | sK1 != sK1
% 3.34/1.00      | sK2 != X0 ),
% 3.34/1.00      inference(resolution_lifted,[status(thm)],[c_765,c_360]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_831,plain,
% 3.34/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(unflattening,[status(thm)],[c_830]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_833,plain,
% 3.34/1.00      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_831,c_29]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2012,plain,
% 3.34/1.00      ( k3_subset_1(u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
% 3.34/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_2011,c_833]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_34,plain,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1682,plain,
% 3.34/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.34/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1483]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1683,plain,
% 3.34/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1682]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2053,plain,
% 3.34/1.00      ( k3_subset_1(u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2012,c_34,c_1683]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2055,plain,
% 3.34/1.00      ( k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1)) = sK2 ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_2053,c_1894]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4634,plain,
% 3.34/1.00      ( k3_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) = sK2 ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_4614,c_2055]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1954,plain,
% 3.34/1.00      ( k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,X1)
% 3.34/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1373,c_1372]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3461,plain,
% 3.34/1.00      ( k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,X1)))) = k3_subset_1(X0,k3_subset_1(X0,X1))
% 3.34/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1373,c_1954]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3993,plain,
% 3.34/1.00      ( k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)))) = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1370,c_3461]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4001,plain,
% 3.34/1.00      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_3993,c_1893,c_3989]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4641,plain,
% 3.34/1.00      ( sK2 = k1_xboole_0 ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_4634,c_4001]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1067,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1406,plain,
% 3.34/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1067]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1407,plain,
% 3.34/1.00      ( sK2 != k1_xboole_0
% 3.34/1.00      | k1_xboole_0 = sK2
% 3.34/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1406]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1066,plain,( X0 = X0 ),theory(equality) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1087,plain,
% 3.34/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1066]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_26,negated_conjecture,
% 3.34/1.00      ( k1_xboole_0 != sK2 ),
% 3.34/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(contradiction,plain,
% 3.34/1.00      ( $false ),
% 3.34/1.00      inference(minisat,[status(thm)],[c_4641,c_1407,c_1087,c_26]) ).
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  ------                               Statistics
% 3.34/1.00  
% 3.34/1.00  ------ General
% 3.34/1.00  
% 3.34/1.00  abstr_ref_over_cycles:                  0
% 3.34/1.00  abstr_ref_under_cycles:                 0
% 3.34/1.00  gc_basic_clause_elim:                   0
% 3.34/1.00  forced_gc_time:                         0
% 3.34/1.00  parsing_time:                           0.014
% 3.34/1.00  unif_index_cands_time:                  0.
% 3.34/1.00  unif_index_add_time:                    0.
% 3.34/1.00  orderings_time:                         0.
% 3.34/1.00  out_proof_time:                         0.012
% 3.34/1.00  total_time:                             0.218
% 3.34/1.00  num_of_symbols:                         53
% 3.34/1.00  num_of_terms:                           4501
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing
% 3.34/1.00  
% 3.34/1.00  num_of_splits:                          0
% 3.34/1.00  num_of_split_atoms:                     0
% 3.34/1.00  num_of_reused_defs:                     0
% 3.34/1.00  num_eq_ax_congr_red:                    19
% 3.34/1.00  num_of_sem_filtered_clauses:            1
% 3.34/1.00  num_of_subtypes:                        0
% 3.34/1.00  monotx_restored_types:                  0
% 3.34/1.00  sat_num_of_epr_types:                   0
% 3.34/1.00  sat_num_of_non_cyclic_types:            0
% 3.34/1.00  sat_guarded_non_collapsed_types:        0
% 3.34/1.00  num_pure_diseq_elim:                    0
% 3.34/1.00  simp_replaced_by:                       0
% 3.34/1.00  res_preprocessed:                       118
% 3.34/1.00  prep_upred:                             0
% 3.34/1.00  prep_unflattend:                        38
% 3.34/1.00  smt_new_axioms:                         0
% 3.34/1.00  pred_elim_cands:                        3
% 3.34/1.00  pred_elim:                              8
% 3.34/1.00  pred_elim_cl:                           11
% 3.34/1.00  pred_elim_cycles:                       11
% 3.34/1.00  merged_defs:                            0
% 3.34/1.00  merged_defs_ncl:                        0
% 3.34/1.00  bin_hyper_res:                          0
% 3.34/1.00  prep_cycles:                            4
% 3.34/1.00  pred_elim_time:                         0.012
% 3.34/1.00  splitting_time:                         0.
% 3.34/1.00  sem_filter_time:                        0.
% 3.34/1.00  monotx_time:                            0.001
% 3.34/1.00  subtype_inf_time:                       0.
% 3.34/1.00  
% 3.34/1.00  ------ Problem properties
% 3.34/1.00  
% 3.34/1.00  clauses:                                21
% 3.34/1.00  conjectures:                            2
% 3.34/1.00  epr:                                    3
% 3.34/1.00  horn:                                   20
% 3.34/1.00  ground:                                 4
% 3.34/1.00  unary:                                  9
% 3.34/1.00  binary:                                 5
% 3.34/1.00  lits:                                   41
% 3.34/1.00  lits_eq:                                15
% 3.34/1.00  fd_pure:                                0
% 3.34/1.00  fd_pseudo:                              0
% 3.34/1.00  fd_cond:                                0
% 3.34/1.00  fd_pseudo_cond:                         1
% 3.34/1.00  ac_symbols:                             0
% 3.34/1.00  
% 3.34/1.00  ------ Propositional Solver
% 3.34/1.00  
% 3.34/1.00  prop_solver_calls:                      31
% 3.34/1.00  prop_fast_solver_calls:                 886
% 3.34/1.00  smt_solver_calls:                       0
% 3.34/1.00  smt_fast_solver_calls:                  0
% 3.34/1.00  prop_num_of_clauses:                    1813
% 3.34/1.00  prop_preprocess_simplified:             5136
% 3.34/1.00  prop_fo_subsumed:                       35
% 3.34/1.00  prop_solver_time:                       0.
% 3.34/1.00  smt_solver_time:                        0.
% 3.34/1.00  smt_fast_solver_time:                   0.
% 3.34/1.00  prop_fast_solver_time:                  0.
% 3.34/1.00  prop_unsat_core_time:                   0.
% 3.34/1.00  
% 3.34/1.00  ------ QBF
% 3.34/1.00  
% 3.34/1.00  qbf_q_res:                              0
% 3.34/1.00  qbf_num_tautologies:                    0
% 3.34/1.00  qbf_prep_cycles:                        0
% 3.34/1.00  
% 3.34/1.00  ------ BMC1
% 3.34/1.00  
% 3.34/1.00  bmc1_current_bound:                     -1
% 3.34/1.00  bmc1_last_solved_bound:                 -1
% 3.34/1.00  bmc1_unsat_core_size:                   -1
% 3.34/1.00  bmc1_unsat_core_parents_size:           -1
% 3.34/1.00  bmc1_merge_next_fun:                    0
% 3.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation
% 3.34/1.00  
% 3.34/1.00  inst_num_of_clauses:                    609
% 3.34/1.00  inst_num_in_passive:                    80
% 3.34/1.00  inst_num_in_active:                     332
% 3.34/1.00  inst_num_in_unprocessed:                197
% 3.34/1.00  inst_num_of_loops:                      390
% 3.34/1.00  inst_num_of_learning_restarts:          0
% 3.34/1.00  inst_num_moves_active_passive:          53
% 3.34/1.00  inst_lit_activity:                      0
% 3.34/1.00  inst_lit_activity_moves:                0
% 3.34/1.00  inst_num_tautologies:                   0
% 3.34/1.00  inst_num_prop_implied:                  0
% 3.34/1.00  inst_num_existing_simplified:           0
% 3.34/1.00  inst_num_eq_res_simplified:             0
% 3.34/1.00  inst_num_child_elim:                    0
% 3.34/1.00  inst_num_of_dismatching_blockings:      322
% 3.34/1.00  inst_num_of_non_proper_insts:           784
% 3.34/1.00  inst_num_of_duplicates:                 0
% 3.34/1.00  inst_inst_num_from_inst_to_res:         0
% 3.34/1.00  inst_dismatching_checking_time:         0.
% 3.34/1.00  
% 3.34/1.00  ------ Resolution
% 3.34/1.00  
% 3.34/1.00  res_num_of_clauses:                     0
% 3.34/1.00  res_num_in_passive:                     0
% 3.34/1.00  res_num_in_active:                      0
% 3.34/1.00  res_num_of_loops:                       122
% 3.34/1.00  res_forward_subset_subsumed:            96
% 3.34/1.00  res_backward_subset_subsumed:           0
% 3.34/1.00  res_forward_subsumed:                   0
% 3.34/1.00  res_backward_subsumed:                  0
% 3.34/1.00  res_forward_subsumption_resolution:     2
% 3.34/1.00  res_backward_subsumption_resolution:    0
% 3.34/1.00  res_clause_to_clause_subsumption:       409
% 3.34/1.00  res_orphan_elimination:                 0
% 3.34/1.00  res_tautology_del:                      96
% 3.34/1.00  res_num_eq_res_simplified:              0
% 3.34/1.00  res_num_sel_changes:                    0
% 3.34/1.00  res_moves_from_active_to_pass:          0
% 3.34/1.00  
% 3.34/1.00  ------ Superposition
% 3.34/1.00  
% 3.34/1.00  sup_time_total:                         0.
% 3.34/1.00  sup_time_generating:                    0.
% 3.34/1.00  sup_time_sim_full:                      0.
% 3.34/1.00  sup_time_sim_immed:                     0.
% 3.34/1.00  
% 3.34/1.00  sup_num_of_clauses:                     87
% 3.34/1.00  sup_num_in_active:                      46
% 3.34/1.00  sup_num_in_passive:                     41
% 3.34/1.00  sup_num_of_loops:                       76
% 3.34/1.00  sup_fw_superposition:                   63
% 3.34/1.00  sup_bw_superposition:                   67
% 3.34/1.00  sup_immediate_simplified:               60
% 3.34/1.00  sup_given_eliminated:                   0
% 3.34/1.00  comparisons_done:                       0
% 3.34/1.00  comparisons_avoided:                    3
% 3.34/1.00  
% 3.34/1.00  ------ Simplifications
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  sim_fw_subset_subsumed:                 16
% 3.34/1.00  sim_bw_subset_subsumed:                 5
% 3.34/1.00  sim_fw_subsumed:                        7
% 3.34/1.00  sim_bw_subsumed:                        1
% 3.34/1.00  sim_fw_subsumption_res:                 0
% 3.34/1.00  sim_bw_subsumption_res:                 0
% 3.34/1.00  sim_tautology_del:                      1
% 3.34/1.00  sim_eq_tautology_del:                   17
% 3.34/1.00  sim_eq_res_simp:                        2
% 3.34/1.00  sim_fw_demodulated:                     22
% 3.34/1.00  sim_bw_demodulated:                     28
% 3.34/1.00  sim_light_normalised:                   27
% 3.34/1.00  sim_joinable_taut:                      0
% 3.34/1.00  sim_joinable_simp:                      0
% 3.34/1.00  sim_ac_normalised:                      0
% 3.34/1.00  sim_smt_subsumption:                    0
% 3.34/1.00  
%------------------------------------------------------------------------------
