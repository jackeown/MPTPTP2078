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
% DateTime   : Thu Dec  3 12:15:33 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 708 expanded)
%              Number of clauses        :  112 ( 221 expanded)
%              Number of leaves         :   23 ( 177 expanded)
%              Depth                    :   26
%              Number of atoms          :  493 (3118 expanded)
%              Number of equality atoms :  153 ( 631 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK1
        & v3_tops_1(sK1,X0)
        & v3_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f45,f44])).

fof(f73,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
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
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_349,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_350,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_352,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_25,c_24])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_352])).

cnf(c_409,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_411,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_25])).

cnf(c_860,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1644,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_860])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1036,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_2138,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1644,c_25,c_24,c_409,c_1036])).

cnf(c_861,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_866,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1744,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_861,c_866])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_862,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1743,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_862,c_866])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1752,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1743,c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_266,plain,
    ( v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_267,plain,
    ( v3_tops_1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_279,plain,
    ( v3_tops_1(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_267,c_8])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_290,plain,
    ( v3_tops_1(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_26])).

cnf(c_291,plain,
    ( v3_tops_1(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_293,plain,
    ( v3_tops_1(k1_xboole_0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_25])).

cnf(c_360,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_293])).

cnf(c_361,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_25])).

cnf(c_364,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_371,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_364,c_8])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_371])).

cnf(c_423,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_425,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_25])).

cnf(c_859,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_941,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_959,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_1156,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_25,c_423,c_941,c_959])).

cnf(c_18,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_374,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_375,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_25,c_24])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_377])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_446,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_25,c_24])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_496,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_497,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_301,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_302,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_25])).

cnf(c_307,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_466,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_467,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_535,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_307,c_467])).

cnf(c_536,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = X1
    | k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_497,c_536])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_568,c_6])).

cnf(c_857,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_1030,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_857])).

cnf(c_1031,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1030,c_446])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_943,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_1087,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_29,c_943])).

cnf(c_1159,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1156,c_1087])).

cnf(c_1763,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1752,c_1159])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_524,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_467])).

cnf(c_525,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_527,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_24])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_497,c_527])).

cnf(c_558,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_858,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_1942,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1744,c_858])).

cnf(c_1950,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_864])).

cnf(c_2085,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1942,c_29,c_1950])).

cnf(c_2140,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2138,c_1744,c_1763,c_2085])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_863,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1513,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_861,c_863])).

cnf(c_1941,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1744,c_1513])).

cnf(c_2145,plain,
    ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2140,c_1941])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_865,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_881,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_865,c_3])).

cnf(c_1745,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_881,c_866])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_884,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_2])).

cnf(c_1747,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1745,c_884])).

cnf(c_2150,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2145,c_1747])).

cnf(c_673,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_972,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_973,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_672,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_691,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2150,c_973,c_691,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.67/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.98  
% 2.67/0.98  ------  iProver source info
% 2.67/0.98  
% 2.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.98  git: non_committed_changes: false
% 2.67/0.98  git: last_make_outside_of_git: false
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     num_symb
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       true
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  ------ Parsing...
% 2.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.98  ------ Proving...
% 2.67/0.98  ------ Problem Properties 
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  clauses                                 16
% 2.67/0.98  conjectures                             2
% 2.67/0.98  EPR                                     1
% 2.67/0.98  Horn                                    16
% 2.67/0.98  unary                                   9
% 2.67/0.98  binary                                  6
% 2.67/0.98  lits                                    24
% 2.67/0.98  lits eq                                 12
% 2.67/0.98  fd_pure                                 0
% 2.67/0.98  fd_pseudo                               0
% 2.67/0.98  fd_cond                                 0
% 2.67/0.98  fd_pseudo_cond                          0
% 2.67/0.98  AC symbols                              0
% 2.67/0.98  
% 2.67/0.98  ------ Schedule dynamic 5 is on 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  Current options:
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     none
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       false
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ Proving...
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  % SZS status Theorem for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  fof(f8,axiom,(
% 2.67/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f24,plain,(
% 2.67/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f8])).
% 2.67/0.98  
% 2.67/0.98  fof(f54,plain,(
% 2.67/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f24])).
% 2.67/0.98  
% 2.67/0.98  fof(f14,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f30,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f14])).
% 2.67/0.98  
% 2.67/0.98  fof(f41,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(nnf_transformation,[],[f30])).
% 2.67/0.98  
% 2.67/0.98  fof(f60,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f41])).
% 2.67/0.98  
% 2.67/0.98  fof(f18,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f35,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f18])).
% 2.67/0.98  
% 2.67/0.98  fof(f36,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f35])).
% 2.67/0.98  
% 2.67/0.98  fof(f67,plain,(
% 2.67/0.98    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f36])).
% 2.67/0.98  
% 2.67/0.98  fof(f20,conjecture,(
% 2.67/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f21,negated_conjecture,(
% 2.67/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 2.67/0.98    inference(negated_conjecture,[],[f20])).
% 2.67/0.98  
% 2.67/0.98  fof(f39,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f21])).
% 2.67/0.98  
% 2.67/0.98  fof(f40,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f39])).
% 2.67/0.98  
% 2.67/0.98  fof(f45,plain,(
% 2.67/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,X0) & v3_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f44,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f46,plain,(
% 2.67/0.98    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f45,f44])).
% 2.67/0.98  
% 2.67/0.98  fof(f73,plain,(
% 2.67/0.98    v3_tops_1(sK1,sK0)),
% 2.67/0.98    inference(cnf_transformation,[],[f46])).
% 2.67/0.98  
% 2.67/0.98  fof(f70,plain,(
% 2.67/0.98    l1_pre_topc(sK0)),
% 2.67/0.98    inference(cnf_transformation,[],[f46])).
% 2.67/0.98  
% 2.67/0.98  fof(f71,plain,(
% 2.67/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.67/0.98    inference(cnf_transformation,[],[f46])).
% 2.67/0.98  
% 2.67/0.98  fof(f6,axiom,(
% 2.67/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f23,plain,(
% 2.67/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f6])).
% 2.67/0.98  
% 2.67/0.98  fof(f52,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f23])).
% 2.67/0.98  
% 2.67/0.98  fof(f10,axiom,(
% 2.67/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f56,plain,(
% 2.67/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f10])).
% 2.67/0.98  
% 2.67/0.98  fof(f3,axiom,(
% 2.67/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f49,plain,(
% 2.67/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.67/0.98    inference(cnf_transformation,[],[f3])).
% 2.67/0.98  
% 2.67/0.98  fof(f1,axiom,(
% 2.67/0.98    v1_xboole_0(k1_xboole_0)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f47,plain,(
% 2.67/0.98    v1_xboole_0(k1_xboole_0)),
% 2.67/0.98    inference(cnf_transformation,[],[f1])).
% 2.67/0.98  
% 2.67/0.98  fof(f13,axiom,(
% 2.67/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_tops_1(X1,X0))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f28,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f13])).
% 2.67/0.98  
% 2.67/0.98  fof(f29,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f28])).
% 2.67/0.98  
% 2.67/0.98  fof(f59,plain,(
% 2.67/0.98    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f29])).
% 2.67/0.98  
% 2.67/0.98  fof(f69,plain,(
% 2.67/0.98    v2_pre_topc(sK0)),
% 2.67/0.98    inference(cnf_transformation,[],[f46])).
% 2.67/0.98  
% 2.67/0.98  fof(f17,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f34,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f17])).
% 2.67/0.98  
% 2.67/0.98  fof(f43,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(nnf_transformation,[],[f34])).
% 2.67/0.98  
% 2.67/0.98  fof(f65,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f43])).
% 2.67/0.98  
% 2.67/0.98  fof(f19,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f37,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f19])).
% 2.67/0.98  
% 2.67/0.98  fof(f38,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f37])).
% 2.67/0.98  
% 2.67/0.98  fof(f68,plain,(
% 2.67/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f38])).
% 2.67/0.98  
% 2.67/0.98  fof(f12,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f26,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f12])).
% 2.67/0.98  
% 2.67/0.98  fof(f27,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f26])).
% 2.67/0.98  
% 2.67/0.98  fof(f57,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f27])).
% 2.67/0.98  
% 2.67/0.98  fof(f15,axiom,(
% 2.67/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f31,plain,(
% 2.67/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f15])).
% 2.67/0.98  
% 2.67/0.98  fof(f32,plain,(
% 2.67/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/0.98    inference(flattening,[],[f31])).
% 2.67/0.98  
% 2.67/0.98  fof(f62,plain,(
% 2.67/0.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f32])).
% 2.67/0.98  
% 2.67/0.98  fof(f16,axiom,(
% 2.67/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f33,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f16])).
% 2.67/0.98  
% 2.67/0.98  fof(f42,plain,(
% 2.67/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.67/0.98    inference(nnf_transformation,[],[f33])).
% 2.67/0.98  
% 2.67/0.98  fof(f63,plain,(
% 2.67/0.98    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f72,plain,(
% 2.67/0.98    v3_pre_topc(sK1,sK0)),
% 2.67/0.98    inference(cnf_transformation,[],[f46])).
% 2.67/0.98  
% 2.67/0.98  fof(f9,axiom,(
% 2.67/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f25,plain,(
% 2.67/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.67/0.98    inference(ennf_transformation,[],[f9])).
% 2.67/0.98  
% 2.67/0.98  fof(f55,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f25])).
% 2.67/0.98  
% 2.67/0.98  fof(f7,axiom,(
% 2.67/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f53,plain,(
% 2.67/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f7])).
% 2.67/0.98  
% 2.67/0.98  fof(f5,axiom,(
% 2.67/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f51,plain,(
% 2.67/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.67/0.98    inference(cnf_transformation,[],[f5])).
% 2.67/0.98  
% 2.67/0.98  fof(f2,axiom,(
% 2.67/0.98    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f48,plain,(
% 2.67/0.98    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f2])).
% 2.67/0.98  
% 2.67/0.98  fof(f4,axiom,(
% 2.67/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f50,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f4])).
% 2.67/0.98  
% 2.67/0.98  fof(f75,plain,(
% 2.67/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.67/0.98    inference(definition_unfolding,[],[f48,f50])).
% 2.67/0.98  
% 2.67/0.98  fof(f74,plain,(
% 2.67/0.98    k1_xboole_0 != sK1),
% 2.67/0.98    inference(cnf_transformation,[],[f46])).
% 2.67/0.98  
% 2.67/0.98  cnf(c_6,plain,
% 2.67/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.67/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_864,plain,
% 2.67/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.67/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_13,plain,
% 2.67/0.98      ( ~ v1_tops_1(X0,X1)
% 2.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.98      | ~ l1_pre_topc(X1)
% 2.67/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_19,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.67/0.98      | ~ v3_tops_1(X1,X0)
% 2.67/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.98      | ~ l1_pre_topc(X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_22,negated_conjecture,
% 2.67/0.98      ( v3_tops_1(sK1,sK0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_349,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.67/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.98      | ~ l1_pre_topc(X0)
% 2.67/0.98      | sK0 != X0
% 2.67/0.98      | sK1 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_350,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 2.67/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | ~ l1_pre_topc(sK0) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_349]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_25,negated_conjecture,
% 2.67/0.98      ( l1_pre_topc(sK0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_24,negated_conjecture,
% 2.67/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_352,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_350,c_25,c_24]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_408,plain,
% 2.67/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.98      | ~ l1_pre_topc(X1)
% 2.67/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 2.67/0.98      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 2.67/0.98      | sK0 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_352]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_409,plain,
% 2.67/0.98      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | ~ l1_pre_topc(sK0)
% 2.67/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_408]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_411,plain,
% 2.67/0.98      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_409,c_25]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_860,plain,
% 2.67/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 2.67/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1644,plain,
% 2.67/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 2.67/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_864,c_860]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_956,plain,
% 2.67/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1036,plain,
% 2.67/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.98      inference(instantiation,[status(thm)],[c_956]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2138,plain,
% 2.67/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_1644,c_25,c_24,c_409,c_1036]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_861,plain,
% 2.67/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_4,plain,
% 2.67/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_866,plain,
% 2.67/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 2.67/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1744,plain,
% 2.67/0.98      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_861,c_866]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_8,plain,
% 2.67/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.67/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_862,plain,
% 2.67/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.67/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1743,plain,
% 2.67/0.98      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.67/0.98      inference(superposition,[status(thm)],[c_862,c_866]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2,plain,
% 2.67/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.67/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1752,plain,
% 2.67/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.67/0.98      inference(light_normalisation,[status(thm)],[c_1743,c_2]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_0,plain,
% 2.67/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_11,plain,
% 2.67/0.98      ( v3_tops_1(X0,X1)
% 2.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.98      | ~ l1_pre_topc(X1)
% 2.67/0.98      | ~ v2_pre_topc(X1)
% 2.67/0.98      | ~ v1_xboole_0(X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_266,plain,
% 2.67/0.98      ( v3_tops_1(X0,X1)
% 2.67/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.98      | ~ l1_pre_topc(X1)
% 2.67/0.98      | ~ v2_pre_topc(X1)
% 2.67/0.98      | k1_xboole_0 != X0 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_267,plain,
% 2.67/0.98      ( v3_tops_1(k1_xboole_0,X0)
% 2.67/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.98      | ~ l1_pre_topc(X0)
% 2.67/0.98      | ~ v2_pre_topc(X0) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_266]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_279,plain,
% 2.67/0.98      ( v3_tops_1(k1_xboole_0,X0)
% 2.67/0.98      | ~ l1_pre_topc(X0)
% 2.67/0.98      | ~ v2_pre_topc(X0) ),
% 2.67/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_267,c_8]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_26,negated_conjecture,
% 2.67/0.98      ( v2_pre_topc(sK0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_290,plain,
% 2.67/0.98      ( v3_tops_1(k1_xboole_0,X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_279,c_26]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_291,plain,
% 2.67/0.98      ( v3_tops_1(k1_xboole_0,sK0) | ~ l1_pre_topc(sK0) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_293,plain,
% 2.67/0.98      ( v3_tops_1(k1_xboole_0,sK0) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_291,c_25]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_360,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.67/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.98      | ~ l1_pre_topc(X0)
% 2.67/0.98      | sK0 != X0
% 2.67/0.98      | k1_xboole_0 != X1 ),
% 2.67/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_293]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_361,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
% 2.67/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | ~ l1_pre_topc(sK0) ),
% 2.67/0.98      inference(unflattening,[status(thm)],[c_360]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_363,plain,
% 2.67/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
% 2.67/0.98      inference(global_propositional_subsumption,
% 2.67/0.98                [status(thm)],
% 2.67/0.98                [c_361,c_25]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_364,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
% 2.67/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.98      inference(renaming,[status(thm)],[c_363]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_371,plain,
% 2.67/0.98      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
% 2.67/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_364,c_8]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_422,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 2.67/0.99      | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) != X0
% 2.67/0.99      | sK0 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_371]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_423,plain,
% 2.67/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ l1_pre_topc(sK0)
% 2.67/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_422]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_425,plain,
% 2.67/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_423,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_859,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0)
% 2.67/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_941,plain,
% 2.67/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_959,plain,
% 2.67/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_956]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1156,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_859,c_25,c_423,c_941,c_959]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_18,plain,
% 2.67/0.99      ( ~ v2_tops_1(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_20,plain,
% 2.67/0.99      ( v2_tops_1(X0,X1)
% 2.67/0.99      | ~ v3_tops_1(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_374,plain,
% 2.67/0.99      ( v2_tops_1(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | sK0 != X1
% 2.67/0.99      | sK1 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_375,plain,
% 2.67/0.99      ( v2_tops_1(sK1,sK0)
% 2.67/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ l1_pre_topc(sK0) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_377,plain,
% 2.67/0.99      ( v2_tops_1(sK1,sK0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_375,c_25,c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_443,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.67/0.99      | sK0 != X1
% 2.67/0.99      | sK1 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_377]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_444,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ l1_pre_topc(sK0)
% 2.67/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_446,plain,
% 2.67/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_444,c_25,c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_10,plain,
% 2.67/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1)
% 2.67/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_496,plain,
% 2.67/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | k2_pre_topc(X1,X0) = X0
% 2.67/0.99      | sK0 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_497,plain,
% 2.67/0.99      ( ~ v4_pre_topc(X0,sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,X0) = X0 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_14,plain,
% 2.67/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ l1_pre_topc(X0)
% 2.67/0.99      | ~ v2_pre_topc(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_301,plain,
% 2.67/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/0.99      | ~ l1_pre_topc(X0)
% 2.67/0.99      | sK0 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_302,plain,
% 2.67/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ l1_pre_topc(sK0) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_306,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_302,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_307,plain,
% 2.67/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_306]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_16,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.67/0.99      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | ~ l1_pre_topc(X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_466,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.67/0.99      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/0.99      | sK0 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_467,plain,
% 2.67/0.99      ( ~ v3_pre_topc(X0,sK0)
% 2.67/0.99      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_466]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_535,plain,
% 2.67/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k1_tops_1(sK0,X1) != X0
% 2.67/0.99      | sK0 != sK0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_307,c_467]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_536,plain,
% 2.67/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_567,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,X1) = X1
% 2.67/0.99      | k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) != X1
% 2.67/0.99      | sK0 != sK0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_497,c_536]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_568,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_567]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_580,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) ),
% 2.67/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_568,c_6]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_857,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0))
% 2.67/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.67/0.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1030,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
% 2.67/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.67/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_446,c_857]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1031,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
% 2.67/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.67/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_1030,c_446]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_29,plain,
% 2.67/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_943,plain,
% 2.67/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1087,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_1031,c_29,c_943]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1159,plain,
% 2.67/0.99      ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_1156,c_1087]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1763,plain,
% 2.67/0.99      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_1752,c_1159]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_23,negated_conjecture,
% 2.67/0.99      ( v3_pre_topc(sK1,sK0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_524,plain,
% 2.67/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | sK0 != sK0
% 2.67/0.99      | sK1 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_467]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_525,plain,
% 2.67/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 2.67/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_524]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_527,plain,
% 2.67/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_525,c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_557,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,X0) = X0
% 2.67/0.99      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 2.67/0.99      | sK0 != sK0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_497,c_527]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_558,plain,
% 2.67/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.67/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_858,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
% 2.67/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1942,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1)
% 2.67/0.99      | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_1744,c_858]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1950,plain,
% 2.67/0.99      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.67/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1744,c_864]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2085,plain,
% 2.67/0.99      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_1942,c_29,c_1950]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2140,plain,
% 2.67/0.99      ( k4_xboole_0(u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
% 2.67/0.99      inference(light_normalisation,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2138,c_1744,c_1763,c_2085]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_7,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_863,plain,
% 2.67/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.67/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1513,plain,
% 2.67/0.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_861,c_863]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1941,plain,
% 2.67/0.99      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_1744,c_1513]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2145,plain,
% 2.67/0.99      ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = sK1 ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2140,c_1941]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5,plain,
% 2.67/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_865,plain,
% 2.67/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3,plain,
% 2.67/0.99      ( k2_subset_1(X0) = X0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_881,plain,
% 2.67/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_865,c_3]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1745,plain,
% 2.67/0.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_881,c_866]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1,plain,
% 2.67/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_884,plain,
% 2.67/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_1,c_2]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1747,plain,
% 2.67/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_1745,c_884]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2150,plain,
% 2.67/0.99      ( sK1 = k1_xboole_0 ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2145,c_1747]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_673,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_972,plain,
% 2.67/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_673]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_973,plain,
% 2.67/0.99      ( sK1 != k1_xboole_0
% 2.67/0.99      | k1_xboole_0 = sK1
% 2.67/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_672,plain,( X0 = X0 ),theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_691,plain,
% 2.67/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_672]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_21,negated_conjecture,
% 2.67/0.99      ( k1_xboole_0 != sK1 ),
% 2.67/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(contradiction,plain,
% 2.67/0.99      ( $false ),
% 2.67/0.99      inference(minisat,[status(thm)],[c_2150,c_973,c_691,c_21]) ).
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  ------                               Statistics
% 2.67/0.99  
% 2.67/0.99  ------ General
% 2.67/0.99  
% 2.67/0.99  abstr_ref_over_cycles:                  0
% 2.67/0.99  abstr_ref_under_cycles:                 0
% 2.67/0.99  gc_basic_clause_elim:                   0
% 2.67/0.99  forced_gc_time:                         0
% 2.67/0.99  parsing_time:                           0.009
% 2.67/0.99  unif_index_cands_time:                  0.
% 2.67/0.99  unif_index_add_time:                    0.
% 2.67/0.99  orderings_time:                         0.
% 2.67/0.99  out_proof_time:                         0.013
% 2.67/0.99  total_time:                             0.106
% 2.67/0.99  num_of_symbols:                         51
% 2.67/0.99  num_of_terms:                           2127
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing
% 2.67/0.99  
% 2.67/0.99  num_of_splits:                          0
% 2.67/0.99  num_of_split_atoms:                     0
% 2.67/0.99  num_of_reused_defs:                     0
% 2.67/0.99  num_eq_ax_congr_red:                    15
% 2.67/0.99  num_of_sem_filtered_clauses:            1
% 2.67/0.99  num_of_subtypes:                        0
% 2.67/0.99  monotx_restored_types:                  0
% 2.67/0.99  sat_num_of_epr_types:                   0
% 2.67/0.99  sat_num_of_non_cyclic_types:            0
% 2.67/0.99  sat_guarded_non_collapsed_types:        0
% 2.67/0.99  num_pure_diseq_elim:                    0
% 2.67/0.99  simp_replaced_by:                       0
% 2.67/0.99  res_preprocessed:                       96
% 2.67/0.99  prep_upred:                             0
% 2.67/0.99  prep_unflattend:                        27
% 2.67/0.99  smt_new_axioms:                         0
% 2.67/0.99  pred_elim_cands:                        1
% 2.67/0.99  pred_elim:                              8
% 2.67/0.99  pred_elim_cl:                           11
% 2.67/0.99  pred_elim_cycles:                       10
% 2.67/0.99  merged_defs:                            0
% 2.67/0.99  merged_defs_ncl:                        0
% 2.67/0.99  bin_hyper_res:                          0
% 2.67/0.99  prep_cycles:                            4
% 2.67/0.99  pred_elim_time:                         0.006
% 2.67/0.99  splitting_time:                         0.
% 2.67/0.99  sem_filter_time:                        0.
% 2.67/0.99  monotx_time:                            0.
% 2.67/0.99  subtype_inf_time:                       0.
% 2.67/0.99  
% 2.67/0.99  ------ Problem properties
% 2.67/0.99  
% 2.67/0.99  clauses:                                16
% 2.67/0.99  conjectures:                            2
% 2.67/0.99  epr:                                    1
% 2.67/0.99  horn:                                   16
% 2.67/0.99  ground:                                 7
% 2.67/0.99  unary:                                  9
% 2.67/0.99  binary:                                 6
% 2.67/0.99  lits:                                   24
% 2.67/0.99  lits_eq:                                12
% 2.67/0.99  fd_pure:                                0
% 2.67/0.99  fd_pseudo:                              0
% 2.67/0.99  fd_cond:                                0
% 2.67/0.99  fd_pseudo_cond:                         0
% 2.67/0.99  ac_symbols:                             0
% 2.67/0.99  
% 2.67/0.99  ------ Propositional Solver
% 2.67/0.99  
% 2.67/0.99  prop_solver_calls:                      27
% 2.67/0.99  prop_fast_solver_calls:                 510
% 2.67/0.99  smt_solver_calls:                       0
% 2.67/0.99  smt_fast_solver_calls:                  0
% 2.67/0.99  prop_num_of_clauses:                    783
% 2.67/0.99  prop_preprocess_simplified:             2910
% 2.67/0.99  prop_fo_subsumed:                       21
% 2.67/0.99  prop_solver_time:                       0.
% 2.67/0.99  smt_solver_time:                        0.
% 2.67/0.99  smt_fast_solver_time:                   0.
% 2.67/0.99  prop_fast_solver_time:                  0.
% 2.67/0.99  prop_unsat_core_time:                   0.
% 2.67/0.99  
% 2.67/0.99  ------ QBF
% 2.67/0.99  
% 2.67/0.99  qbf_q_res:                              0
% 2.67/0.99  qbf_num_tautologies:                    0
% 2.67/0.99  qbf_prep_cycles:                        0
% 2.67/0.99  
% 2.67/0.99  ------ BMC1
% 2.67/0.99  
% 2.67/0.99  bmc1_current_bound:                     -1
% 2.67/0.99  bmc1_last_solved_bound:                 -1
% 2.67/0.99  bmc1_unsat_core_size:                   -1
% 2.67/0.99  bmc1_unsat_core_parents_size:           -1
% 2.67/0.99  bmc1_merge_next_fun:                    0
% 2.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation
% 2.67/0.99  
% 2.67/0.99  inst_num_of_clauses:                    245
% 2.67/0.99  inst_num_in_passive:                    48
% 2.67/0.99  inst_num_in_active:                     148
% 2.67/0.99  inst_num_in_unprocessed:                51
% 2.67/0.99  inst_num_of_loops:                      160
% 2.67/0.99  inst_num_of_learning_restarts:          0
% 2.67/0.99  inst_num_moves_active_passive:          9
% 2.67/0.99  inst_lit_activity:                      0
% 2.67/0.99  inst_lit_activity_moves:                0
% 2.67/0.99  inst_num_tautologies:                   0
% 2.67/0.99  inst_num_prop_implied:                  0
% 2.67/0.99  inst_num_existing_simplified:           0
% 2.67/0.99  inst_num_eq_res_simplified:             0
% 2.67/0.99  inst_num_child_elim:                    0
% 2.67/0.99  inst_num_of_dismatching_blockings:      130
% 2.67/0.99  inst_num_of_non_proper_insts:           222
% 2.67/0.99  inst_num_of_duplicates:                 0
% 2.67/0.99  inst_inst_num_from_inst_to_res:         0
% 2.67/0.99  inst_dismatching_checking_time:         0.
% 2.67/0.99  
% 2.67/0.99  ------ Resolution
% 2.67/0.99  
% 2.67/0.99  res_num_of_clauses:                     0
% 2.67/0.99  res_num_in_passive:                     0
% 2.67/0.99  res_num_in_active:                      0
% 2.67/0.99  res_num_of_loops:                       100
% 2.67/0.99  res_forward_subset_subsumed:            19
% 2.67/0.99  res_backward_subset_subsumed:           4
% 2.67/0.99  res_forward_subsumed:                   0
% 2.67/0.99  res_backward_subsumed:                  0
% 2.67/0.99  res_forward_subsumption_resolution:     5
% 2.67/0.99  res_backward_subsumption_resolution:    0
% 2.67/0.99  res_clause_to_clause_subsumption:       92
% 2.67/0.99  res_orphan_elimination:                 0
% 2.67/0.99  res_tautology_del:                      16
% 2.67/0.99  res_num_eq_res_simplified:              0
% 2.67/0.99  res_num_sel_changes:                    0
% 2.67/0.99  res_moves_from_active_to_pass:          0
% 2.67/0.99  
% 2.67/0.99  ------ Superposition
% 2.67/0.99  
% 2.67/0.99  sup_time_total:                         0.
% 2.67/0.99  sup_time_generating:                    0.
% 2.67/0.99  sup_time_sim_full:                      0.
% 2.67/0.99  sup_time_sim_immed:                     0.
% 2.67/0.99  
% 2.67/0.99  sup_num_of_clauses:                     24
% 2.67/0.99  sup_num_in_active:                      16
% 2.67/0.99  sup_num_in_passive:                     8
% 2.67/0.99  sup_num_of_loops:                       31
% 2.67/0.99  sup_fw_superposition:                   14
% 2.67/0.99  sup_bw_superposition:                   11
% 2.67/0.99  sup_immediate_simplified:               19
% 2.67/0.99  sup_given_eliminated:                   0
% 2.67/0.99  comparisons_done:                       0
% 2.67/0.99  comparisons_avoided:                    0
% 2.67/0.99  
% 2.67/0.99  ------ Simplifications
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  sim_fw_subset_subsumed:                 6
% 2.67/0.99  sim_bw_subset_subsumed:                 0
% 2.67/0.99  sim_fw_subsumed:                        6
% 2.67/0.99  sim_bw_subsumed:                        0
% 2.67/0.99  sim_fw_subsumption_res:                 0
% 2.67/0.99  sim_bw_subsumption_res:                 0
% 2.67/0.99  sim_tautology_del:                      0
% 2.67/0.99  sim_eq_tautology_del:                   2
% 2.67/0.99  sim_eq_res_simp:                        0
% 2.67/0.99  sim_fw_demodulated:                     1
% 2.67/0.99  sim_bw_demodulated:                     16
% 2.67/0.99  sim_light_normalised:                   10
% 2.67/0.99  sim_joinable_taut:                      0
% 2.67/0.99  sim_joinable_simp:                      0
% 2.67/0.99  sim_ac_normalised:                      0
% 2.67/0.99  sim_smt_subsumption:                    0
% 2.67/0.99  
%------------------------------------------------------------------------------
