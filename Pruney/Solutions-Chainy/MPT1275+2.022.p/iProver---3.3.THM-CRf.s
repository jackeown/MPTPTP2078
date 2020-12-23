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
% DateTime   : Thu Dec  3 12:15:26 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 666 expanded)
%              Number of clauses        :   84 ( 229 expanded)
%              Number of leaves         :   17 ( 128 expanded)
%              Depth                    :   17
%              Number of atoms          :  421 (2710 expanded)
%              Number of equality atoms :  161 ( 783 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1005,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_168,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_169])).

cnf(c_987,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_2050,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1005,c_987])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_210,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_169])).

cnf(c_986,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3601,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_1001])).

cnf(c_4540,plain,
    ( r1_tarski(X0,X0) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_3601])).

cnf(c_79,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8850,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4540,c_79])).

cnf(c_8858,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_8850,c_987])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_169])).

cnf(c_985,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_1949,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1005,c_985])).

cnf(c_3075,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2050,c_1949])).

cnf(c_8903,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8858,c_3075])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1004,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8928,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8903,c_1004])).

cnf(c_9222,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8928,c_79,c_4540])).

cnf(c_9228,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_9222,c_8903])).

cnf(c_9250,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_9228])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_989,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1580,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_1001])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_169])).

cnf(c_984,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_3490,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1580,c_984])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_999,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2634,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_999])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1296,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_2931,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2634,c_24,c_23,c_1296])).

cnf(c_15,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_997,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2250,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_997])).

cnf(c_21,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v3_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1658,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1660,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_19,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_993,plain,
    ( v3_tops_1(X0,X1) = iProver_top
    | v2_tops_1(X0,X1) != iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1486,plain,
    ( v3_tops_1(sK1,sK0) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_993])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_81,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_16,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1258,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1259,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_1261,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_448,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_1785,plain,
    ( v3_tops_1(sK1,sK0)
    | r1_tarski(X0,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_448,c_21])).

cnf(c_1786,plain,
    ( v3_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_1788,plain,
    ( v3_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1786])).

cnf(c_1899,plain,
    ( v3_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1486,c_25,c_26,c_27,c_81,c_1261,c_1788])).

cnf(c_18,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1992,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2776,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2250,c_24,c_25,c_23,c_26,c_27,c_21,c_29,c_81,c_1261,c_1486,c_1660,c_1788,c_1992])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1000,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2393,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_1000])).

cnf(c_1246,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1248,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_2781,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2393,c_24,c_23,c_22,c_1248])).

cnf(c_2933,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2931,c_2776,c_2781])).

cnf(c_3923,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3490,c_2933])).

cnf(c_992,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v3_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4281,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1
    | v3_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3923,c_992])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9250,c_4281,c_1899])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:22:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/0.98  
% 3.74/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.98  
% 3.74/0.98  ------  iProver source info
% 3.74/0.98  
% 3.74/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.98  git: non_committed_changes: false
% 3.74/0.98  git: last_make_outside_of_git: false
% 3.74/0.98  
% 3.74/0.98  ------ 
% 3.74/0.98  ------ Parsing...
% 3.74/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.98  
% 3.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.98  ------ Proving...
% 3.74/0.98  ------ Problem Properties 
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  clauses                                 24
% 3.74/0.98  conjectures                             5
% 3.74/0.98  EPR                                     4
% 3.74/0.98  Horn                                    23
% 3.74/0.98  unary                                   6
% 3.74/0.98  binary                                  9
% 3.74/0.98  lits                                    59
% 3.74/0.98  lits eq                                 12
% 3.74/0.98  fd_pure                                 0
% 3.74/0.98  fd_pseudo                               0
% 3.74/0.98  fd_cond                                 1
% 3.74/0.98  fd_pseudo_cond                          1
% 3.74/0.98  AC symbols                              0
% 3.74/0.98  
% 3.74/0.98  ------ Input Options Time Limit: Unbounded
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  ------ 
% 3.74/0.98  Current options:
% 3.74/0.98  ------ 
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  ------ Proving...
% 3.74/0.98  
% 3.74/0.98  
% 3.74/0.98  % SZS status Theorem for theBenchmark.p
% 3.74/0.98  
% 3.74/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.98  
% 3.74/0.98  fof(f1,axiom,(
% 3.74/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f35,plain,(
% 3.74/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/0.98    inference(nnf_transformation,[],[f1])).
% 3.74/0.98  
% 3.74/0.98  fof(f36,plain,(
% 3.74/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/0.98    inference(flattening,[],[f35])).
% 3.74/0.98  
% 3.74/0.98  fof(f45,plain,(
% 3.74/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.74/0.98    inference(cnf_transformation,[],[f36])).
% 3.74/0.98  
% 3.74/0.98  fof(f71,plain,(
% 3.74/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.74/0.98    inference(equality_resolution,[],[f45])).
% 3.74/0.98  
% 3.74/0.98  fof(f4,axiom,(
% 3.74/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f20,plain,(
% 3.74/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.74/0.98    inference(ennf_transformation,[],[f4])).
% 3.74/0.98  
% 3.74/0.98  fof(f50,plain,(
% 3.74/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.98    inference(cnf_transformation,[],[f20])).
% 3.74/0.98  
% 3.74/0.98  fof(f9,axiom,(
% 3.74/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f37,plain,(
% 3.74/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.74/0.98    inference(nnf_transformation,[],[f9])).
% 3.74/0.98  
% 3.74/0.98  fof(f56,plain,(
% 3.74/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f37])).
% 3.74/0.98  
% 3.74/0.98  fof(f6,axiom,(
% 3.74/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f21,plain,(
% 3.74/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.74/0.98    inference(ennf_transformation,[],[f6])).
% 3.74/0.98  
% 3.74/0.98  fof(f52,plain,(
% 3.74/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.98    inference(cnf_transformation,[],[f21])).
% 3.74/0.98  
% 3.74/0.98  fof(f55,plain,(
% 3.74/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.74/0.98    inference(cnf_transformation,[],[f37])).
% 3.74/0.98  
% 3.74/0.98  fof(f7,axiom,(
% 3.74/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f22,plain,(
% 3.74/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.74/0.98    inference(ennf_transformation,[],[f7])).
% 3.74/0.98  
% 3.74/0.98  fof(f53,plain,(
% 3.74/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.98    inference(cnf_transformation,[],[f22])).
% 3.74/0.98  
% 3.74/0.98  fof(f2,axiom,(
% 3.74/0.98    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f19,plain,(
% 3.74/0.98    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.74/0.98    inference(ennf_transformation,[],[f2])).
% 3.74/0.98  
% 3.74/0.98  fof(f48,plain,(
% 3.74/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.74/0.98    inference(cnf_transformation,[],[f19])).
% 3.74/0.98  
% 3.74/0.98  fof(f16,conjecture,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f17,negated_conjecture,(
% 3.74/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.74/0.98    inference(negated_conjecture,[],[f16])).
% 3.74/0.98  
% 3.74/0.98  fof(f33,plain,(
% 3.74/0.98    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f17])).
% 3.74/0.98  
% 3.74/0.98  fof(f34,plain,(
% 3.74/0.98    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.74/0.98    inference(flattening,[],[f33])).
% 3.74/0.98  
% 3.74/0.98  fof(f40,plain,(
% 3.74/0.98    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.74/0.98    inference(nnf_transformation,[],[f34])).
% 3.74/0.98  
% 3.74/0.98  fof(f41,plain,(
% 3.74/0.98    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.74/0.98    inference(flattening,[],[f40])).
% 3.74/0.98  
% 3.74/0.98  fof(f43,plain,(
% 3.74/0.98    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.74/0.98    introduced(choice_axiom,[])).
% 3.74/0.98  
% 3.74/0.98  fof(f42,plain,(
% 3.74/0.98    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.74/0.98    introduced(choice_axiom,[])).
% 3.74/0.98  
% 3.74/0.98  fof(f44,plain,(
% 3.74/0.98    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.74/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 3.74/0.98  
% 3.74/0.98  fof(f66,plain,(
% 3.74/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.74/0.98    inference(cnf_transformation,[],[f44])).
% 3.74/0.98  
% 3.74/0.98  fof(f8,axiom,(
% 3.74/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f23,plain,(
% 3.74/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.74/0.98    inference(ennf_transformation,[],[f8])).
% 3.74/0.98  
% 3.74/0.98  fof(f54,plain,(
% 3.74/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.98    inference(cnf_transformation,[],[f23])).
% 3.74/0.98  
% 3.74/0.98  fof(f11,axiom,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f26,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f11])).
% 3.74/0.98  
% 3.74/0.98  fof(f58,plain,(
% 3.74/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f26])).
% 3.74/0.98  
% 3.74/0.98  fof(f65,plain,(
% 3.74/0.98    l1_pre_topc(sK0)),
% 3.74/0.98    inference(cnf_transformation,[],[f44])).
% 3.74/0.98  
% 3.74/0.98  fof(f12,axiom,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f27,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f12])).
% 3.74/0.98  
% 3.74/0.98  fof(f38,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(nnf_transformation,[],[f27])).
% 3.74/0.98  
% 3.74/0.98  fof(f59,plain,(
% 3.74/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f38])).
% 3.74/0.98  
% 3.74/0.98  fof(f68,plain,(
% 3.74/0.98    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 3.74/0.98    inference(cnf_transformation,[],[f44])).
% 3.74/0.98  
% 3.74/0.98  fof(f69,plain,(
% 3.74/0.98    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 3.74/0.98    inference(cnf_transformation,[],[f44])).
% 3.74/0.98  
% 3.74/0.98  fof(f15,axiom,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f31,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f15])).
% 3.74/0.98  
% 3.74/0.98  fof(f32,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(flattening,[],[f31])).
% 3.74/0.98  
% 3.74/0.98  fof(f64,plain,(
% 3.74/0.98    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f32])).
% 3.74/0.98  
% 3.74/0.98  fof(f67,plain,(
% 3.74/0.98    v4_pre_topc(sK1,sK0)),
% 3.74/0.98    inference(cnf_transformation,[],[f44])).
% 3.74/0.98  
% 3.74/0.98  fof(f13,axiom,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f28,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f13])).
% 3.74/0.98  
% 3.74/0.98  fof(f39,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(nnf_transformation,[],[f28])).
% 3.74/0.98  
% 3.74/0.98  fof(f62,plain,(
% 3.74/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f39])).
% 3.74/0.98  
% 3.74/0.98  fof(f14,axiom,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f29,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f14])).
% 3.74/0.98  
% 3.74/0.98  fof(f30,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(flattening,[],[f29])).
% 3.74/0.98  
% 3.74/0.98  fof(f63,plain,(
% 3.74/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f30])).
% 3.74/0.98  
% 3.74/0.98  fof(f10,axiom,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.98  
% 3.74/0.98  fof(f18,plain,(
% 3.74/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.74/0.98    inference(pure_predicate_removal,[],[f10])).
% 3.74/0.98  
% 3.74/0.98  fof(f24,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(ennf_transformation,[],[f18])).
% 3.74/0.98  
% 3.74/0.98  fof(f25,plain,(
% 3.74/0.98    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.98    inference(flattening,[],[f24])).
% 3.74/0.98  
% 3.74/0.98  fof(f57,plain,(
% 3.74/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.98    inference(cnf_transformation,[],[f25])).
% 3.74/0.98  
% 3.74/0.98  cnf(c_2,plain,
% 3.74/0.98      ( r1_tarski(X0,X0) ),
% 3.74/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1005,plain,
% 3.74/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_5,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.74/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_10,plain,
% 3.74/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.74/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_168,plain,
% 3.74/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.74/0.98      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_169,plain,
% 3.74/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.74/0.98      inference(renaming,[status(thm)],[c_168]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_209,plain,
% 3.74/0.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.74/0.98      inference(bin_hyper_res,[status(thm)],[c_5,c_169]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_987,plain,
% 3.74/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.74/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_2050,plain,
% 3.74/0.98      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_1005,c_987]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_7,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.74/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_210,plain,
% 3.74/0.98      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 3.74/0.98      | ~ r1_tarski(X1,X0) ),
% 3.74/0.98      inference(bin_hyper_res,[status(thm)],[c_7,c_169]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_986,plain,
% 3.74/0.98      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 3.74/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_11,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.74/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1001,plain,
% 3.74/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.74/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_3601,plain,
% 3.74/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.74/0.98      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_986,c_1001]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_4540,plain,
% 3.74/0.98      ( r1_tarski(X0,X0) != iProver_top
% 3.74/0.98      | r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_2050,c_3601]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_79,plain,
% 3.74/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_8850,plain,
% 3.74/0.98      ( r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
% 3.74/0.98      inference(global_propositional_subsumption,
% 3.74/0.98                [status(thm)],
% 3.74/0.98                [c_4540,c_79]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_8858,plain,
% 3.74/0.98      ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_8850,c_987]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_8,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.74/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_211,plain,
% 3.74/0.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.74/0.98      inference(bin_hyper_res,[status(thm)],[c_8,c_169]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_985,plain,
% 3.74/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.74/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1949,plain,
% 3.74/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_1005,c_985]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_3075,plain,
% 3.74/0.98      ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.74/0.98      inference(demodulation,[status(thm)],[c_2050,c_1949]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_8903,plain,
% 3.74/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.74/0.98      inference(light_normalisation,[status(thm)],[c_8858,c_3075]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_3,plain,
% 3.74/0.98      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 3.74/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1004,plain,
% 3.74/0.98      ( k1_xboole_0 = X0
% 3.74/0.98      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_8928,plain,
% 3.74/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 3.74/0.98      | r1_tarski(k4_xboole_0(X0,X0),X0) != iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_8903,c_1004]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_9222,plain,
% 3.74/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.74/0.98      inference(global_propositional_subsumption,
% 3.74/0.98                [status(thm)],
% 3.74/0.98                [c_8928,c_79,c_4540]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_9228,plain,
% 3.74/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.74/0.98      inference(demodulation,[status(thm)],[c_9222,c_8903]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_9250,plain,
% 3.74/0.98      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_9228]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_23,negated_conjecture,
% 3.74/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.74/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_989,plain,
% 3.74/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1580,plain,
% 3.74/0.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_989,c_1001]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_9,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.74/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_212,plain,
% 3.74/0.98      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.74/0.98      inference(bin_hyper_res,[status(thm)],[c_9,c_169]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_984,plain,
% 3.74/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.74/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_3490,plain,
% 3.74/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_1580,c_984]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_13,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.98      | ~ l1_pre_topc(X1)
% 3.74/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.74/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_999,plain,
% 3.74/0.98      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.74/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.74/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_2634,plain,
% 3.74/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.74/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_989,c_999]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_24,negated_conjecture,
% 3.74/0.98      ( l1_pre_topc(sK0) ),
% 3.74/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1294,plain,
% 3.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.98      | ~ l1_pre_topc(sK0)
% 3.74/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1296,plain,
% 3.74/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.98      | ~ l1_pre_topc(sK0)
% 3.74/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_1294]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_2931,plain,
% 3.74/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.74/0.98      inference(global_propositional_subsumption,
% 3.74/0.98                [status(thm)],
% 3.74/0.98                [c_2634,c_24,c_23,c_1296]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_15,plain,
% 3.74/0.98      ( ~ v2_tops_1(X0,X1)
% 3.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.98      | ~ l1_pre_topc(X1)
% 3.74/0.98      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.74/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_997,plain,
% 3.74/0.98      ( k1_tops_1(X0,X1) = k1_xboole_0
% 3.74/0.98      | v2_tops_1(X1,X0) != iProver_top
% 3.74/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.74/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_2250,plain,
% 3.74/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.74/0.98      | v2_tops_1(sK1,sK0) != iProver_top
% 3.74/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_989,c_997]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_21,negated_conjecture,
% 3.74/0.98      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.74/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_20,negated_conjecture,
% 3.74/0.98      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.74/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_29,plain,
% 3.74/0.98      ( k2_tops_1(sK0,sK1) != sK1 | v3_tops_1(sK1,sK0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1658,plain,
% 3.74/0.98      ( ~ v2_tops_1(X0,sK0)
% 3.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.98      | ~ l1_pre_topc(sK0)
% 3.74/0.98      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1660,plain,
% 3.74/0.98      ( ~ v2_tops_1(sK1,sK0)
% 3.74/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.98      | ~ l1_pre_topc(sK0)
% 3.74/0.98      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_1658]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_19,plain,
% 3.74/0.98      ( v3_tops_1(X0,X1)
% 3.74/0.98      | ~ v2_tops_1(X0,X1)
% 3.74/0.98      | ~ v4_pre_topc(X0,X1)
% 3.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.98      | ~ l1_pre_topc(X1) ),
% 3.74/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_993,plain,
% 3.74/0.98      ( v3_tops_1(X0,X1) = iProver_top
% 3.74/0.98      | v2_tops_1(X0,X1) != iProver_top
% 3.74/0.98      | v4_pre_topc(X0,X1) != iProver_top
% 3.74/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.74/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1486,plain,
% 3.74/0.98      ( v3_tops_1(sK1,sK0) = iProver_top
% 3.74/0.98      | v2_tops_1(sK1,sK0) != iProver_top
% 3.74/0.98      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.74/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.98      inference(superposition,[status(thm)],[c_989,c_993]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_25,plain,
% 3.74/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_26,plain,
% 3.74/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_22,negated_conjecture,
% 3.74/0.98      ( v4_pre_topc(sK1,sK0) ),
% 3.74/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_27,plain,
% 3.74/0.98      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_81,plain,
% 3.74/0.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_79]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_16,plain,
% 3.74/0.98      ( v2_tops_1(X0,X1)
% 3.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.98      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.74/0.98      | ~ l1_pre_topc(X1) ),
% 3.74/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1258,plain,
% 3.74/0.98      ( v2_tops_1(X0,sK0)
% 3.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.98      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
% 3.74/0.98      | ~ l1_pre_topc(sK0) ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1259,plain,
% 3.74/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.74/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.74/0.98      | r1_tarski(X0,k2_tops_1(sK0,X0)) != iProver_top
% 3.74/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.98      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_1261,plain,
% 3.74/0.98      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.74/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.74/0.98      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top
% 3.74/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.98      inference(instantiation,[status(thm)],[c_1259]) ).
% 3.74/0.98  
% 3.74/0.98  cnf(c_448,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 3.74/0.99      theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1785,plain,
% 3.74/0.99      ( v3_tops_1(sK1,sK0)
% 3.74/0.99      | r1_tarski(X0,k2_tops_1(sK0,sK1))
% 3.74/0.99      | ~ r1_tarski(X0,sK1) ),
% 3.74/0.99      inference(resolution,[status(thm)],[c_448,c_21]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1786,plain,
% 3.74/0.99      ( v3_tops_1(sK1,sK0) = iProver_top
% 3.74/0.99      | r1_tarski(X0,k2_tops_1(sK0,sK1)) = iProver_top
% 3.74/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1788,plain,
% 3.74/0.99      ( v3_tops_1(sK1,sK0) = iProver_top
% 3.74/0.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 3.74/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1786]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1899,plain,
% 3.74/0.99      ( v3_tops_1(sK1,sK0) = iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_1486,c_25,c_26,c_27,c_81,c_1261,c_1788]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_18,plain,
% 3.74/0.99      ( ~ v3_tops_1(X0,X1)
% 3.74/0.99      | v2_tops_1(X0,X1)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.99      | ~ l1_pre_topc(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1992,plain,
% 3.74/0.99      ( ~ v3_tops_1(sK1,sK0)
% 3.74/0.99      | v2_tops_1(sK1,sK0)
% 3.74/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.99      | ~ l1_pre_topc(sK0) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2776,plain,
% 3.74/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_2250,c_24,c_25,c_23,c_26,c_27,c_21,c_29,c_81,c_1261,
% 3.74/0.99                 c_1486,c_1660,c_1788,c_1992]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12,plain,
% 3.74/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.99      | ~ l1_pre_topc(X1)
% 3.74/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1000,plain,
% 3.74/0.99      ( k2_pre_topc(X0,X1) = X1
% 3.74/0.99      | v4_pre_topc(X1,X0) != iProver_top
% 3.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.74/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2393,plain,
% 3.74/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.74/0.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.74/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_989,c_1000]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1246,plain,
% 3.74/0.99      ( ~ v4_pre_topc(X0,sK0)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.99      | ~ l1_pre_topc(sK0)
% 3.74/0.99      | k2_pre_topc(sK0,X0) = X0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1248,plain,
% 3.74/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 3.74/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.99      | ~ l1_pre_topc(sK0)
% 3.74/0.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1246]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2781,plain,
% 3.74/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_2393,c_24,c_23,c_22,c_1248]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2933,plain,
% 3.74/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 3.74/0.99      inference(light_normalisation,[status(thm)],[c_2931,c_2776,c_2781]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3923,plain,
% 3.74/0.99      ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_3490,c_2933]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_992,plain,
% 3.74/0.99      ( k2_tops_1(sK0,sK1) != sK1 | v3_tops_1(sK1,sK0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4281,plain,
% 3.74/0.99      ( k4_xboole_0(sK1,k1_xboole_0) != sK1
% 3.74/0.99      | v3_tops_1(sK1,sK0) != iProver_top ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_3923,c_992]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(contradiction,plain,
% 3.74/0.99      ( $false ),
% 3.74/0.99      inference(minisat,[status(thm)],[c_9250,c_4281,c_1899]) ).
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  ------                               Statistics
% 3.74/0.99  
% 3.74/0.99  ------ Selected
% 3.74/0.99  
% 3.74/0.99  total_time:                             0.424
% 3.74/0.99  
%------------------------------------------------------------------------------
