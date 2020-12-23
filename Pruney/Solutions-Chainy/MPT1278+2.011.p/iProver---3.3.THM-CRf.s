%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:34 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 918 expanded)
%              Number of clauses        :  109 ( 316 expanded)
%              Number of leaves         :   22 ( 224 expanded)
%              Depth                    :   21
%              Number of atoms          :  471 (3512 expanded)
%              Number of equality atoms :  189 ( 896 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f48,f47])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f50,f52,f52])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1683,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_1676,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_1982,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1683,c_1676])).

cnf(c_21,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_523,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_524,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_23,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_25,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_291,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_292,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_294,plain,
    ( v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_28,c_27])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_524,c_294])).

cnf(c_832,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_834,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_27])).

cnf(c_1983,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1982,c_834])).

cnf(c_20,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_538,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_539,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_388,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = k2_struct_0(X3)
    | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_389,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_403,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_389,c_6])).

cnf(c_493,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_403,c_28])).

cnf(c_494,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_539,c_494])).

cnf(c_1674,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_3898,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_1674])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1687,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1687,c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1685,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2738,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1703,c_1685])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1688,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2748,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1703,c_1688])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2178,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2181,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2178,c_1])).

cnf(c_2750,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2748,c_2181])).

cnf(c_3535,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2738,c_2750])).

cnf(c_3916,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3898,c_3535])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_553,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_554,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1678,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_3541,plain,
    ( v3_pre_topc(k1_xboole_0,sK0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3535,c_1678])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_317,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_318,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_28])).

cnf(c_323,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_1682,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_1943,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1682])).

cnf(c_1944,plain,
    ( v3_pre_topc(k1_xboole_0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1943,c_834])).

cnf(c_4279,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_1944])).

cnf(c_1686,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_1686])).

cnf(c_3565,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_1703])).

cnf(c_4285,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4279,c_3565])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_595,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_596,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_1675,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_2648,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0)
    | v4_pre_topc(u1_struct_0(sK0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_1675])).

cnf(c_4287,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_4285,c_2648])).

cnf(c_9761,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3916,c_4287])).

cnf(c_9764,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9761,c_3565])).

cnf(c_3373,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1686,c_1675])).

cnf(c_4543,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_3373])).

cnf(c_5294,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_4543])).

cnf(c_2747,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1683,c_1688])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_294])).

cnf(c_840,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_842,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_840,c_27])).

cnf(c_2878,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2747,c_842])).

cnf(c_5313,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5294,c_2747,c_2878])).

cnf(c_32,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2901,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_1678])).

cnf(c_3369,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_1686])).

cnf(c_3631,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3369,c_32])).

cnf(c_3638,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3631,c_1675])).

cnf(c_3647,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3638,c_2878])).

cnf(c_5329,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5313,c_32,c_33,c_2901,c_3647])).

cnf(c_2737,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1683,c_1685])).

cnf(c_2875,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2747,c_2737])).

cnf(c_5342,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_5329,c_2875])).

cnf(c_9776,plain,
    ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_9764,c_5342])).

cnf(c_9817,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9776,c_2750])).

cnf(c_1347,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1937,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1938,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_1346,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1369,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9817,c_1938,c_1369,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:09:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.44/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/0.98  
% 3.44/0.98  ------  iProver source info
% 3.44/0.98  
% 3.44/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.44/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/0.98  git: non_committed_changes: false
% 3.44/0.98  git: last_make_outside_of_git: false
% 3.44/0.98  
% 3.44/0.98  ------ 
% 3.44/0.98  
% 3.44/0.98  ------ Input Options
% 3.44/0.98  
% 3.44/0.98  --out_options                           all
% 3.44/0.98  --tptp_safe_out                         true
% 3.44/0.98  --problem_path                          ""
% 3.44/0.98  --include_path                          ""
% 3.44/0.98  --clausifier                            res/vclausify_rel
% 3.44/0.98  --clausifier_options                    --mode clausify
% 3.44/0.98  --stdin                                 false
% 3.44/0.98  --stats_out                             all
% 3.44/0.98  
% 3.44/0.98  ------ General Options
% 3.44/0.98  
% 3.44/0.98  --fof                                   false
% 3.44/0.98  --time_out_real                         305.
% 3.44/0.98  --time_out_virtual                      -1.
% 3.44/0.98  --symbol_type_check                     false
% 3.44/0.98  --clausify_out                          false
% 3.44/0.98  --sig_cnt_out                           false
% 3.44/0.98  --trig_cnt_out                          false
% 3.44/0.98  --trig_cnt_out_tolerance                1.
% 3.44/0.98  --trig_cnt_out_sk_spl                   false
% 3.44/0.98  --abstr_cl_out                          false
% 3.44/0.98  
% 3.44/0.98  ------ Global Options
% 3.44/0.98  
% 3.44/0.98  --schedule                              default
% 3.44/0.98  --add_important_lit                     false
% 3.44/0.98  --prop_solver_per_cl                    1000
% 3.44/0.98  --min_unsat_core                        false
% 3.44/0.98  --soft_assumptions                      false
% 3.44/0.98  --soft_lemma_size                       3
% 3.44/0.98  --prop_impl_unit_size                   0
% 3.44/0.98  --prop_impl_unit                        []
% 3.44/0.98  --share_sel_clauses                     true
% 3.44/0.98  --reset_solvers                         false
% 3.44/0.98  --bc_imp_inh                            [conj_cone]
% 3.44/0.98  --conj_cone_tolerance                   3.
% 3.44/0.98  --extra_neg_conj                        none
% 3.44/0.98  --large_theory_mode                     true
% 3.44/0.98  --prolific_symb_bound                   200
% 3.44/0.98  --lt_threshold                          2000
% 3.44/0.98  --clause_weak_htbl                      true
% 3.44/0.98  --gc_record_bc_elim                     false
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing Options
% 3.44/0.98  
% 3.44/0.98  --preprocessing_flag                    true
% 3.44/0.98  --time_out_prep_mult                    0.1
% 3.44/0.98  --splitting_mode                        input
% 3.44/0.98  --splitting_grd                         true
% 3.44/0.98  --splitting_cvd                         false
% 3.44/0.98  --splitting_cvd_svl                     false
% 3.44/0.98  --splitting_nvd                         32
% 3.44/0.98  --sub_typing                            true
% 3.44/0.98  --prep_gs_sim                           true
% 3.44/0.98  --prep_unflatten                        true
% 3.44/0.98  --prep_res_sim                          true
% 3.44/0.98  --prep_upred                            true
% 3.44/0.98  --prep_sem_filter                       exhaustive
% 3.44/0.98  --prep_sem_filter_out                   false
% 3.44/0.98  --pred_elim                             true
% 3.44/0.98  --res_sim_input                         true
% 3.44/0.98  --eq_ax_congr_red                       true
% 3.44/0.98  --pure_diseq_elim                       true
% 3.44/0.98  --brand_transform                       false
% 3.44/0.98  --non_eq_to_eq                          false
% 3.44/0.98  --prep_def_merge                        true
% 3.44/0.98  --prep_def_merge_prop_impl              false
% 3.44/0.98  --prep_def_merge_mbd                    true
% 3.44/0.98  --prep_def_merge_tr_red                 false
% 3.44/0.98  --prep_def_merge_tr_cl                  false
% 3.44/0.98  --smt_preprocessing                     true
% 3.44/0.98  --smt_ac_axioms                         fast
% 3.44/0.98  --preprocessed_out                      false
% 3.44/0.98  --preprocessed_stats                    false
% 3.44/0.98  
% 3.44/0.98  ------ Abstraction refinement Options
% 3.44/0.98  
% 3.44/0.98  --abstr_ref                             []
% 3.44/0.98  --abstr_ref_prep                        false
% 3.44/0.98  --abstr_ref_until_sat                   false
% 3.44/0.98  --abstr_ref_sig_restrict                funpre
% 3.44/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/0.98  --abstr_ref_under                       []
% 3.44/0.98  
% 3.44/0.98  ------ SAT Options
% 3.44/0.98  
% 3.44/0.98  --sat_mode                              false
% 3.44/0.98  --sat_fm_restart_options                ""
% 3.44/0.98  --sat_gr_def                            false
% 3.44/0.98  --sat_epr_types                         true
% 3.44/0.98  --sat_non_cyclic_types                  false
% 3.44/0.98  --sat_finite_models                     false
% 3.44/0.98  --sat_fm_lemmas                         false
% 3.44/0.98  --sat_fm_prep                           false
% 3.44/0.98  --sat_fm_uc_incr                        true
% 3.44/0.98  --sat_out_model                         small
% 3.44/0.98  --sat_out_clauses                       false
% 3.44/0.98  
% 3.44/0.98  ------ QBF Options
% 3.44/0.98  
% 3.44/0.98  --qbf_mode                              false
% 3.44/0.98  --qbf_elim_univ                         false
% 3.44/0.98  --qbf_dom_inst                          none
% 3.44/0.98  --qbf_dom_pre_inst                      false
% 3.44/0.98  --qbf_sk_in                             false
% 3.44/0.98  --qbf_pred_elim                         true
% 3.44/0.98  --qbf_split                             512
% 3.44/0.98  
% 3.44/0.98  ------ BMC1 Options
% 3.44/0.98  
% 3.44/0.98  --bmc1_incremental                      false
% 3.44/0.98  --bmc1_axioms                           reachable_all
% 3.44/0.98  --bmc1_min_bound                        0
% 3.44/0.98  --bmc1_max_bound                        -1
% 3.44/0.98  --bmc1_max_bound_default                -1
% 3.44/0.98  --bmc1_symbol_reachability              true
% 3.44/0.98  --bmc1_property_lemmas                  false
% 3.44/0.98  --bmc1_k_induction                      false
% 3.44/0.98  --bmc1_non_equiv_states                 false
% 3.44/0.98  --bmc1_deadlock                         false
% 3.44/0.98  --bmc1_ucm                              false
% 3.44/0.98  --bmc1_add_unsat_core                   none
% 3.44/0.98  --bmc1_unsat_core_children              false
% 3.44/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/0.98  --bmc1_out_stat                         full
% 3.44/0.98  --bmc1_ground_init                      false
% 3.44/0.98  --bmc1_pre_inst_next_state              false
% 3.44/0.98  --bmc1_pre_inst_state                   false
% 3.44/0.98  --bmc1_pre_inst_reach_state             false
% 3.44/0.98  --bmc1_out_unsat_core                   false
% 3.44/0.98  --bmc1_aig_witness_out                  false
% 3.44/0.98  --bmc1_verbose                          false
% 3.44/0.98  --bmc1_dump_clauses_tptp                false
% 3.44/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.44/0.98  --bmc1_dump_file                        -
% 3.44/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.44/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.44/0.98  --bmc1_ucm_extend_mode                  1
% 3.44/0.98  --bmc1_ucm_init_mode                    2
% 3.44/0.98  --bmc1_ucm_cone_mode                    none
% 3.44/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.44/0.98  --bmc1_ucm_relax_model                  4
% 3.44/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.44/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/0.98  --bmc1_ucm_layered_model                none
% 3.44/0.98  --bmc1_ucm_max_lemma_size               10
% 3.44/0.98  
% 3.44/0.98  ------ AIG Options
% 3.44/0.98  
% 3.44/0.98  --aig_mode                              false
% 3.44/0.98  
% 3.44/0.98  ------ Instantiation Options
% 3.44/0.98  
% 3.44/0.98  --instantiation_flag                    true
% 3.44/0.98  --inst_sos_flag                         false
% 3.44/0.98  --inst_sos_phase                        true
% 3.44/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/0.98  --inst_lit_sel_side                     num_symb
% 3.44/0.98  --inst_solver_per_active                1400
% 3.44/0.98  --inst_solver_calls_frac                1.
% 3.44/0.98  --inst_passive_queue_type               priority_queues
% 3.44/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/0.98  --inst_passive_queues_freq              [25;2]
% 3.44/0.98  --inst_dismatching                      true
% 3.44/0.98  --inst_eager_unprocessed_to_passive     true
% 3.44/0.98  --inst_prop_sim_given                   true
% 3.44/0.98  --inst_prop_sim_new                     false
% 3.44/0.98  --inst_subs_new                         false
% 3.44/0.98  --inst_eq_res_simp                      false
% 3.44/0.98  --inst_subs_given                       false
% 3.44/0.98  --inst_orphan_elimination               true
% 3.44/0.98  --inst_learning_loop_flag               true
% 3.44/0.98  --inst_learning_start                   3000
% 3.44/0.98  --inst_learning_factor                  2
% 3.44/0.98  --inst_start_prop_sim_after_learn       3
% 3.44/0.98  --inst_sel_renew                        solver
% 3.44/0.98  --inst_lit_activity_flag                true
% 3.44/0.98  --inst_restr_to_given                   false
% 3.44/0.98  --inst_activity_threshold               500
% 3.44/0.98  --inst_out_proof                        true
% 3.44/0.98  
% 3.44/0.98  ------ Resolution Options
% 3.44/0.98  
% 3.44/0.98  --resolution_flag                       true
% 3.44/0.98  --res_lit_sel                           adaptive
% 3.44/0.98  --res_lit_sel_side                      none
% 3.44/0.98  --res_ordering                          kbo
% 3.44/0.98  --res_to_prop_solver                    active
% 3.44/0.98  --res_prop_simpl_new                    false
% 3.44/0.98  --res_prop_simpl_given                  true
% 3.44/0.98  --res_passive_queue_type                priority_queues
% 3.44/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/0.98  --res_passive_queues_freq               [15;5]
% 3.44/0.98  --res_forward_subs                      full
% 3.44/0.98  --res_backward_subs                     full
% 3.44/0.98  --res_forward_subs_resolution           true
% 3.44/0.98  --res_backward_subs_resolution          true
% 3.44/0.98  --res_orphan_elimination                true
% 3.44/0.98  --res_time_limit                        2.
% 3.44/0.98  --res_out_proof                         true
% 3.44/0.98  
% 3.44/0.98  ------ Superposition Options
% 3.44/0.98  
% 3.44/0.98  --superposition_flag                    true
% 3.44/0.98  --sup_passive_queue_type                priority_queues
% 3.44/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.44/0.98  --demod_completeness_check              fast
% 3.44/0.98  --demod_use_ground                      true
% 3.44/0.98  --sup_to_prop_solver                    passive
% 3.44/0.98  --sup_prop_simpl_new                    true
% 3.44/0.98  --sup_prop_simpl_given                  true
% 3.44/0.98  --sup_fun_splitting                     false
% 3.44/0.98  --sup_smt_interval                      50000
% 3.44/0.98  
% 3.44/0.98  ------ Superposition Simplification Setup
% 3.44/0.98  
% 3.44/0.98  --sup_indices_passive                   []
% 3.44/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.98  --sup_full_bw                           [BwDemod]
% 3.44/0.98  --sup_immed_triv                        [TrivRules]
% 3.44/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.98  --sup_immed_bw_main                     []
% 3.44/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.98  
% 3.44/0.98  ------ Combination Options
% 3.44/0.98  
% 3.44/0.98  --comb_res_mult                         3
% 3.44/0.98  --comb_sup_mult                         2
% 3.44/0.98  --comb_inst_mult                        10
% 3.44/0.98  
% 3.44/0.98  ------ Debug Options
% 3.44/0.98  
% 3.44/0.98  --dbg_backtrace                         false
% 3.44/0.98  --dbg_dump_prop_clauses                 false
% 3.44/0.98  --dbg_dump_prop_clauses_file            -
% 3.44/0.98  --dbg_out_stat                          false
% 3.44/0.98  ------ Parsing...
% 3.44/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.98  ------ Proving...
% 3.44/0.98  ------ Problem Properties 
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  clauses                                 25
% 3.44/0.98  conjectures                             3
% 3.44/0.98  EPR                                     2
% 3.44/0.98  Horn                                    25
% 3.44/0.98  unary                                   10
% 3.44/0.98  binary                                  5
% 3.44/0.98  lits                                    50
% 3.44/0.98  lits eq                                 20
% 3.44/0.98  fd_pure                                 0
% 3.44/0.98  fd_pseudo                               0
% 3.44/0.98  fd_cond                                 0
% 3.44/0.98  fd_pseudo_cond                          0
% 3.44/0.98  AC symbols                              0
% 3.44/0.98  
% 3.44/0.98  ------ Schedule dynamic 5 is on 
% 3.44/0.98  
% 3.44/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  ------ 
% 3.44/0.98  Current options:
% 3.44/0.98  ------ 
% 3.44/0.98  
% 3.44/0.98  ------ Input Options
% 3.44/0.98  
% 3.44/0.98  --out_options                           all
% 3.44/0.98  --tptp_safe_out                         true
% 3.44/0.98  --problem_path                          ""
% 3.44/0.98  --include_path                          ""
% 3.44/0.98  --clausifier                            res/vclausify_rel
% 3.44/0.98  --clausifier_options                    --mode clausify
% 3.44/0.98  --stdin                                 false
% 3.44/0.98  --stats_out                             all
% 3.44/0.98  
% 3.44/0.98  ------ General Options
% 3.44/0.98  
% 3.44/0.98  --fof                                   false
% 3.44/0.98  --time_out_real                         305.
% 3.44/0.98  --time_out_virtual                      -1.
% 3.44/0.98  --symbol_type_check                     false
% 3.44/0.98  --clausify_out                          false
% 3.44/0.98  --sig_cnt_out                           false
% 3.44/0.98  --trig_cnt_out                          false
% 3.44/0.98  --trig_cnt_out_tolerance                1.
% 3.44/0.98  --trig_cnt_out_sk_spl                   false
% 3.44/0.98  --abstr_cl_out                          false
% 3.44/0.98  
% 3.44/0.98  ------ Global Options
% 3.44/0.98  
% 3.44/0.98  --schedule                              default
% 3.44/0.98  --add_important_lit                     false
% 3.44/0.98  --prop_solver_per_cl                    1000
% 3.44/0.98  --min_unsat_core                        false
% 3.44/0.98  --soft_assumptions                      false
% 3.44/0.98  --soft_lemma_size                       3
% 3.44/0.98  --prop_impl_unit_size                   0
% 3.44/0.98  --prop_impl_unit                        []
% 3.44/0.98  --share_sel_clauses                     true
% 3.44/0.98  --reset_solvers                         false
% 3.44/0.98  --bc_imp_inh                            [conj_cone]
% 3.44/0.98  --conj_cone_tolerance                   3.
% 3.44/0.98  --extra_neg_conj                        none
% 3.44/0.98  --large_theory_mode                     true
% 3.44/0.98  --prolific_symb_bound                   200
% 3.44/0.98  --lt_threshold                          2000
% 3.44/0.98  --clause_weak_htbl                      true
% 3.44/0.98  --gc_record_bc_elim                     false
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing Options
% 3.44/0.98  
% 3.44/0.98  --preprocessing_flag                    true
% 3.44/0.98  --time_out_prep_mult                    0.1
% 3.44/0.98  --splitting_mode                        input
% 3.44/0.98  --splitting_grd                         true
% 3.44/0.98  --splitting_cvd                         false
% 3.44/0.98  --splitting_cvd_svl                     false
% 3.44/0.98  --splitting_nvd                         32
% 3.44/0.98  --sub_typing                            true
% 3.44/0.98  --prep_gs_sim                           true
% 3.44/0.98  --prep_unflatten                        true
% 3.44/0.98  --prep_res_sim                          true
% 3.44/0.98  --prep_upred                            true
% 3.44/0.98  --prep_sem_filter                       exhaustive
% 3.44/0.98  --prep_sem_filter_out                   false
% 3.44/0.98  --pred_elim                             true
% 3.44/0.98  --res_sim_input                         true
% 3.44/0.98  --eq_ax_congr_red                       true
% 3.44/0.98  --pure_diseq_elim                       true
% 3.44/0.98  --brand_transform                       false
% 3.44/0.98  --non_eq_to_eq                          false
% 3.44/0.98  --prep_def_merge                        true
% 3.44/0.98  --prep_def_merge_prop_impl              false
% 3.44/0.98  --prep_def_merge_mbd                    true
% 3.44/0.98  --prep_def_merge_tr_red                 false
% 3.44/0.98  --prep_def_merge_tr_cl                  false
% 3.44/0.98  --smt_preprocessing                     true
% 3.44/0.98  --smt_ac_axioms                         fast
% 3.44/0.98  --preprocessed_out                      false
% 3.44/0.98  --preprocessed_stats                    false
% 3.44/0.98  
% 3.44/0.98  ------ Abstraction refinement Options
% 3.44/0.98  
% 3.44/0.98  --abstr_ref                             []
% 3.44/0.98  --abstr_ref_prep                        false
% 3.44/0.98  --abstr_ref_until_sat                   false
% 3.44/0.98  --abstr_ref_sig_restrict                funpre
% 3.44/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/0.98  --abstr_ref_under                       []
% 3.44/0.98  
% 3.44/0.98  ------ SAT Options
% 3.44/0.98  
% 3.44/0.98  --sat_mode                              false
% 3.44/0.98  --sat_fm_restart_options                ""
% 3.44/0.98  --sat_gr_def                            false
% 3.44/0.98  --sat_epr_types                         true
% 3.44/0.98  --sat_non_cyclic_types                  false
% 3.44/0.98  --sat_finite_models                     false
% 3.44/0.98  --sat_fm_lemmas                         false
% 3.44/0.98  --sat_fm_prep                           false
% 3.44/0.98  --sat_fm_uc_incr                        true
% 3.44/0.98  --sat_out_model                         small
% 3.44/0.98  --sat_out_clauses                       false
% 3.44/0.98  
% 3.44/0.98  ------ QBF Options
% 3.44/0.98  
% 3.44/0.98  --qbf_mode                              false
% 3.44/0.98  --qbf_elim_univ                         false
% 3.44/0.98  --qbf_dom_inst                          none
% 3.44/0.98  --qbf_dom_pre_inst                      false
% 3.44/0.98  --qbf_sk_in                             false
% 3.44/0.98  --qbf_pred_elim                         true
% 3.44/0.98  --qbf_split                             512
% 3.44/0.98  
% 3.44/0.98  ------ BMC1 Options
% 3.44/0.98  
% 3.44/0.98  --bmc1_incremental                      false
% 3.44/0.98  --bmc1_axioms                           reachable_all
% 3.44/0.98  --bmc1_min_bound                        0
% 3.44/0.98  --bmc1_max_bound                        -1
% 3.44/0.98  --bmc1_max_bound_default                -1
% 3.44/0.98  --bmc1_symbol_reachability              true
% 3.44/0.98  --bmc1_property_lemmas                  false
% 3.44/0.98  --bmc1_k_induction                      false
% 3.44/0.98  --bmc1_non_equiv_states                 false
% 3.44/0.98  --bmc1_deadlock                         false
% 3.44/0.98  --bmc1_ucm                              false
% 3.44/0.98  --bmc1_add_unsat_core                   none
% 3.44/0.98  --bmc1_unsat_core_children              false
% 3.44/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/0.98  --bmc1_out_stat                         full
% 3.44/0.98  --bmc1_ground_init                      false
% 3.44/0.98  --bmc1_pre_inst_next_state              false
% 3.44/0.98  --bmc1_pre_inst_state                   false
% 3.44/0.98  --bmc1_pre_inst_reach_state             false
% 3.44/0.98  --bmc1_out_unsat_core                   false
% 3.44/0.98  --bmc1_aig_witness_out                  false
% 3.44/0.98  --bmc1_verbose                          false
% 3.44/0.98  --bmc1_dump_clauses_tptp                false
% 3.44/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.44/0.98  --bmc1_dump_file                        -
% 3.44/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.44/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.44/0.98  --bmc1_ucm_extend_mode                  1
% 3.44/0.98  --bmc1_ucm_init_mode                    2
% 3.44/0.98  --bmc1_ucm_cone_mode                    none
% 3.44/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.44/0.98  --bmc1_ucm_relax_model                  4
% 3.44/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.44/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/0.98  --bmc1_ucm_layered_model                none
% 3.44/0.98  --bmc1_ucm_max_lemma_size               10
% 3.44/0.98  
% 3.44/0.98  ------ AIG Options
% 3.44/0.98  
% 3.44/0.98  --aig_mode                              false
% 3.44/0.98  
% 3.44/0.98  ------ Instantiation Options
% 3.44/0.98  
% 3.44/0.98  --instantiation_flag                    true
% 3.44/0.98  --inst_sos_flag                         false
% 3.44/0.98  --inst_sos_phase                        true
% 3.44/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/0.98  --inst_lit_sel_side                     none
% 3.44/0.98  --inst_solver_per_active                1400
% 3.44/0.98  --inst_solver_calls_frac                1.
% 3.44/0.98  --inst_passive_queue_type               priority_queues
% 3.44/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/0.98  --inst_passive_queues_freq              [25;2]
% 3.44/0.98  --inst_dismatching                      true
% 3.44/0.98  --inst_eager_unprocessed_to_passive     true
% 3.44/0.98  --inst_prop_sim_given                   true
% 3.44/0.98  --inst_prop_sim_new                     false
% 3.44/0.98  --inst_subs_new                         false
% 3.44/0.98  --inst_eq_res_simp                      false
% 3.44/0.98  --inst_subs_given                       false
% 3.44/0.98  --inst_orphan_elimination               true
% 3.44/0.98  --inst_learning_loop_flag               true
% 3.44/0.98  --inst_learning_start                   3000
% 3.44/0.98  --inst_learning_factor                  2
% 3.44/0.98  --inst_start_prop_sim_after_learn       3
% 3.44/0.98  --inst_sel_renew                        solver
% 3.44/0.98  --inst_lit_activity_flag                true
% 3.44/0.98  --inst_restr_to_given                   false
% 3.44/0.98  --inst_activity_threshold               500
% 3.44/0.98  --inst_out_proof                        true
% 3.44/0.98  
% 3.44/0.98  ------ Resolution Options
% 3.44/0.98  
% 3.44/0.98  --resolution_flag                       false
% 3.44/0.98  --res_lit_sel                           adaptive
% 3.44/0.98  --res_lit_sel_side                      none
% 3.44/0.98  --res_ordering                          kbo
% 3.44/0.98  --res_to_prop_solver                    active
% 3.44/0.98  --res_prop_simpl_new                    false
% 3.44/0.98  --res_prop_simpl_given                  true
% 3.44/0.98  --res_passive_queue_type                priority_queues
% 3.44/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/0.98  --res_passive_queues_freq               [15;5]
% 3.44/0.98  --res_forward_subs                      full
% 3.44/0.98  --res_backward_subs                     full
% 3.44/0.98  --res_forward_subs_resolution           true
% 3.44/0.98  --res_backward_subs_resolution          true
% 3.44/0.98  --res_orphan_elimination                true
% 3.44/0.98  --res_time_limit                        2.
% 3.44/0.98  --res_out_proof                         true
% 3.44/0.98  
% 3.44/0.98  ------ Superposition Options
% 3.44/0.98  
% 3.44/0.98  --superposition_flag                    true
% 3.44/0.98  --sup_passive_queue_type                priority_queues
% 3.44/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.44/0.98  --demod_completeness_check              fast
% 3.44/0.98  --demod_use_ground                      true
% 3.44/0.98  --sup_to_prop_solver                    passive
% 3.44/0.98  --sup_prop_simpl_new                    true
% 3.44/0.98  --sup_prop_simpl_given                  true
% 3.44/0.98  --sup_fun_splitting                     false
% 3.44/0.98  --sup_smt_interval                      50000
% 3.44/0.98  
% 3.44/0.98  ------ Superposition Simplification Setup
% 3.44/0.98  
% 3.44/0.98  --sup_indices_passive                   []
% 3.44/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.98  --sup_full_bw                           [BwDemod]
% 3.44/0.98  --sup_immed_triv                        [TrivRules]
% 3.44/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.98  --sup_immed_bw_main                     []
% 3.44/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/0.98  
% 3.44/0.98  ------ Combination Options
% 3.44/0.98  
% 3.44/0.98  --comb_res_mult                         3
% 3.44/0.98  --comb_sup_mult                         2
% 3.44/0.98  --comb_inst_mult                        10
% 3.44/0.98  
% 3.44/0.98  ------ Debug Options
% 3.44/0.98  
% 3.44/0.98  --dbg_backtrace                         false
% 3.44/0.98  --dbg_dump_prop_clauses                 false
% 3.44/0.98  --dbg_dump_prop_clauses_file            -
% 3.44/0.98  --dbg_out_stat                          false
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  ------ Proving...
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  % SZS status Theorem for theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  fof(f20,conjecture,(
% 3.44/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f21,negated_conjecture,(
% 3.44/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 3.44/0.98    inference(negated_conjecture,[],[f20])).
% 3.44/0.98  
% 3.44/0.98  fof(f40,plain,(
% 3.44/0.98    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.44/0.98    inference(ennf_transformation,[],[f21])).
% 3.44/0.98  
% 3.44/0.98  fof(f41,plain,(
% 3.44/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.44/0.98    inference(flattening,[],[f40])).
% 3.44/0.98  
% 3.44/0.98  fof(f48,plain,(
% 3.44/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,X0) & v3_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.44/0.98    introduced(choice_axiom,[])).
% 3.44/0.98  
% 3.44/0.98  fof(f47,plain,(
% 3.44/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.44/0.98    introduced(choice_axiom,[])).
% 3.44/0.98  
% 3.44/0.98  fof(f49,plain,(
% 3.44/0.98    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f48,f47])).
% 3.44/0.98  
% 3.44/0.98  fof(f77,plain,(
% 3.44/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.44/0.98    inference(cnf_transformation,[],[f49])).
% 3.44/0.98  
% 3.44/0.98  fof(f14,axiom,(
% 3.44/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f31,plain,(
% 3.44/0.98    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.44/0.98    inference(ennf_transformation,[],[f14])).
% 3.44/0.98  
% 3.44/0.98  fof(f32,plain,(
% 3.44/0.98    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(flattening,[],[f31])).
% 3.44/0.98  
% 3.44/0.98  fof(f66,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f32])).
% 3.44/0.98  
% 3.44/0.98  fof(f76,plain,(
% 3.44/0.98    l1_pre_topc(sK0)),
% 3.44/0.98    inference(cnf_transformation,[],[f49])).
% 3.44/0.98  
% 3.44/0.98  fof(f17,axiom,(
% 3.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f35,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f17])).
% 3.44/0.98  
% 3.44/0.98  fof(f46,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(nnf_transformation,[],[f35])).
% 3.44/0.98  
% 3.44/0.98  fof(f71,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f46])).
% 3.44/0.98  
% 3.44/0.98  fof(f19,axiom,(
% 3.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f38,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f19])).
% 3.44/0.98  
% 3.44/0.98  fof(f39,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(flattening,[],[f38])).
% 3.44/0.98  
% 3.44/0.98  fof(f74,plain,(
% 3.44/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f39])).
% 3.44/0.98  
% 3.44/0.98  fof(f79,plain,(
% 3.44/0.98    v3_tops_1(sK1,sK0)),
% 3.44/0.98    inference(cnf_transformation,[],[f49])).
% 3.44/0.98  
% 3.44/0.98  fof(f72,plain,(
% 3.44/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f46])).
% 3.44/0.98  
% 3.44/0.98  fof(f11,axiom,(
% 3.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f27,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f11])).
% 3.44/0.98  
% 3.44/0.98  fof(f42,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(nnf_transformation,[],[f27])).
% 3.44/0.98  
% 3.44/0.98  fof(f61,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f42])).
% 3.44/0.98  
% 3.44/0.98  fof(f12,axiom,(
% 3.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f28,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f12])).
% 3.44/0.98  
% 3.44/0.98  fof(f43,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(nnf_transformation,[],[f28])).
% 3.44/0.98  
% 3.44/0.98  fof(f63,plain,(
% 3.44/0.98    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f43])).
% 3.44/0.98  
% 3.44/0.98  fof(f8,axiom,(
% 3.44/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f23,plain,(
% 3.44/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.44/0.98    inference(ennf_transformation,[],[f8])).
% 3.44/0.98  
% 3.44/0.98  fof(f57,plain,(
% 3.44/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.44/0.98    inference(cnf_transformation,[],[f23])).
% 3.44/0.98  
% 3.44/0.98  fof(f7,axiom,(
% 3.44/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f56,plain,(
% 3.44/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.44/0.98    inference(cnf_transformation,[],[f7])).
% 3.44/0.98  
% 3.44/0.98  fof(f5,axiom,(
% 3.44/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f54,plain,(
% 3.44/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.44/0.98    inference(cnf_transformation,[],[f5])).
% 3.44/0.98  
% 3.44/0.98  fof(f9,axiom,(
% 3.44/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f24,plain,(
% 3.44/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.44/0.98    inference(ennf_transformation,[],[f9])).
% 3.44/0.98  
% 3.44/0.98  fof(f58,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.44/0.98    inference(cnf_transformation,[],[f24])).
% 3.44/0.98  
% 3.44/0.98  fof(f6,axiom,(
% 3.44/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f22,plain,(
% 3.44/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.44/0.98    inference(ennf_transformation,[],[f6])).
% 3.44/0.98  
% 3.44/0.98  fof(f55,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.44/0.98    inference(cnf_transformation,[],[f22])).
% 3.44/0.98  
% 3.44/0.98  fof(f1,axiom,(
% 3.44/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f50,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f1])).
% 3.44/0.98  
% 3.44/0.98  fof(f3,axiom,(
% 3.44/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f52,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.44/0.98    inference(cnf_transformation,[],[f3])).
% 3.44/0.98  
% 3.44/0.98  fof(f81,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.44/0.98    inference(definition_unfolding,[],[f50,f52,f52])).
% 3.44/0.98  
% 3.44/0.98  fof(f4,axiom,(
% 3.44/0.98    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f53,plain,(
% 3.44/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f4])).
% 3.44/0.98  
% 3.44/0.98  fof(f2,axiom,(
% 3.44/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f51,plain,(
% 3.44/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.44/0.98    inference(cnf_transformation,[],[f2])).
% 3.44/0.98  
% 3.44/0.98  fof(f16,axiom,(
% 3.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f34,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f16])).
% 3.44/0.98  
% 3.44/0.98  fof(f45,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(nnf_transformation,[],[f34])).
% 3.44/0.98  
% 3.44/0.98  fof(f69,plain,(
% 3.44/0.98    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f45])).
% 3.44/0.98  
% 3.44/0.98  fof(f13,axiom,(
% 3.44/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f29,plain,(
% 3.44/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.44/0.98    inference(ennf_transformation,[],[f13])).
% 3.44/0.98  
% 3.44/0.98  fof(f30,plain,(
% 3.44/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.44/0.98    inference(flattening,[],[f29])).
% 3.44/0.98  
% 3.44/0.98  fof(f65,plain,(
% 3.44/0.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f30])).
% 3.44/0.98  
% 3.44/0.98  fof(f75,plain,(
% 3.44/0.98    v2_pre_topc(sK0)),
% 3.44/0.98    inference(cnf_transformation,[],[f49])).
% 3.44/0.98  
% 3.44/0.98  fof(f10,axiom,(
% 3.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.98  
% 3.44/0.98  fof(f25,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(ennf_transformation,[],[f10])).
% 3.44/0.98  
% 3.44/0.98  fof(f26,plain,(
% 3.44/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.44/0.98    inference(flattening,[],[f25])).
% 3.44/0.98  
% 3.44/0.98  fof(f59,plain,(
% 3.44/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.44/0.98    inference(cnf_transformation,[],[f26])).
% 3.44/0.98  
% 3.44/0.98  fof(f78,plain,(
% 3.44/0.98    v3_pre_topc(sK1,sK0)),
% 3.44/0.98    inference(cnf_transformation,[],[f49])).
% 3.44/0.98  
% 3.44/0.98  fof(f80,plain,(
% 3.44/0.98    k1_xboole_0 != sK1),
% 3.44/0.98    inference(cnf_transformation,[],[f49])).
% 3.44/0.98  
% 3.44/0.98  cnf(c_27,negated_conjecture,
% 3.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.44/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1683,plain,
% 3.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_15,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_28,negated_conjecture,
% 3.44/0.98      ( l1_pre_topc(sK0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_583,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 3.44/0.98      | sK0 != X1 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_584,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_583]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1676,plain,
% 3.44/0.98      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1982,plain,
% 3.44/0.98      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1683,c_1676]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_21,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_523,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.44/0.98      | sK0 != X1 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_524,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_523]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_23,plain,
% 3.44/0.98      ( ~ v3_tops_1(X0,X1)
% 3.44/0.98      | v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_25,negated_conjecture,
% 3.44/0.98      ( v3_tops_1(sK1,sK0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_291,plain,
% 3.44/0.98      ( v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | sK0 != X1
% 3.44/0.98      | sK1 != X0 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_292,plain,
% 3.44/0.98      ( v2_tops_1(sK1,sK0)
% 3.44/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | ~ l1_pre_topc(sK0) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_291]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_294,plain,
% 3.44/0.98      ( v2_tops_1(sK1,sK0) ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_292,c_28,c_27]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_831,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k1_tops_1(sK0,X0) = k1_xboole_0
% 3.44/0.98      | sK0 != sK0
% 3.44/0.98      | sK1 != X0 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_524,c_294]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_832,plain,
% 3.44/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_831]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_834,plain,
% 3.44/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_832,c_27]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1983,plain,
% 3.44/0.98      ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_1982,c_834]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_20,plain,
% 3.44/0.98      ( v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_538,plain,
% 3.44/0.98      ( v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.44/0.98      | sK0 != X1 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_539,plain,
% 3.44/0.98      ( v2_tops_1(X0,sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_538]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_11,plain,
% 3.44/0.98      ( ~ v1_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_13,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_388,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X3)
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | X1 != X3
% 3.44/0.98      | k2_pre_topc(X3,X2) = k2_struct_0(X3)
% 3.44/0.98      | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_389,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_388]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_6,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.44/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.44/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_403,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.44/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_389,c_6]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_493,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 3.44/0.98      | sK0 != X1 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_403,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_494,plain,
% 3.44/0.98      ( ~ v2_tops_1(X0,sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_493]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_774,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k1_tops_1(sK0,X0) != k1_xboole_0
% 3.44/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 3.44/0.98      inference(resolution,[status(thm)],[c_539,c_494]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1674,plain,
% 3.44/0.98      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 3.44/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3898,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0)
% 3.44/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1983,c_1674]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_5,plain,
% 3.44/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.44/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1687,plain,
% 3.44/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3,plain,
% 3.44/0.98      ( k2_subset_1(X0) = X0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1703,plain,
% 3.44/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_1687,c_3]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_7,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.44/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1685,plain,
% 3.44/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.44/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2738,plain,
% 3.44/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1703,c_1685]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.44/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1688,plain,
% 3.44/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.44/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2748,plain,
% 3.44/0.98      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1703,c_1688]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_0,plain,
% 3.44/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.44/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2,plain,
% 3.44/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2178,plain,
% 3.44/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1,plain,
% 3.44/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2181,plain,
% 3.44/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_2178,c_1]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2750,plain,
% 3.44/0.98      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_2748,c_2181]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3535,plain,
% 3.44/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_2738,c_2750]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3916,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0)
% 3.44/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_3898,c_3535]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_19,plain,
% 3.44/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.44/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1) ),
% 3.44/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_553,plain,
% 3.44/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.44/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | sK0 != X1 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_554,plain,
% 3.44/0.98      ( ~ v3_pre_topc(X0,sK0)
% 3.44/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_553]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1678,plain,
% 3.44/0.98      ( v3_pre_topc(X0,sK0) != iProver_top
% 3.44/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) = iProver_top
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3541,plain,
% 3.44/0.98      ( v3_pre_topc(k1_xboole_0,sK0) != iProver_top
% 3.44/0.98      | v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
% 3.44/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_3535,c_1678]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_14,plain,
% 3.44/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.44/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.44/0.98      | ~ l1_pre_topc(X0)
% 3.44/0.98      | ~ v2_pre_topc(X0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_29,negated_conjecture,
% 3.44/0.98      ( v2_pre_topc(sK0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_317,plain,
% 3.44/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.44/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.44/0.98      | ~ l1_pre_topc(X0)
% 3.44/0.98      | sK0 != X0 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_318,plain,
% 3.44/0.98      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | ~ l1_pre_topc(sK0) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_317]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_322,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_318,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_323,plain,
% 3.44/0.98      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.44/0.98      inference(renaming,[status(thm)],[c_322]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1682,plain,
% 3.44/0.98      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1943,plain,
% 3.44/0.98      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1683,c_1682]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1944,plain,
% 3.44/0.98      ( v3_pre_topc(k1_xboole_0,sK0) = iProver_top ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_1943,c_834]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4279,plain,
% 3.44/0.98      ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
% 3.44/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_3541,c_1944]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1686,plain,
% 3.44/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.44/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3419,plain,
% 3.44/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 3.44/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_2750,c_1686]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3565,plain,
% 3.44/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_3419,c_1703]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4285,plain,
% 3.44/0.98      ( v4_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
% 3.44/0.98      inference(forward_subsumption_resolution,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_4279,c_3565]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_9,plain,
% 3.44/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | ~ l1_pre_topc(X1)
% 3.44/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.44/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_595,plain,
% 3.44/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.44/0.98      | k2_pre_topc(X1,X0) = X0
% 3.44/0.98      | sK0 != X1 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_596,plain,
% 3.44/0.98      ( ~ v4_pre_topc(X0,sK0)
% 3.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k2_pre_topc(sK0,X0) = X0 ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_595]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1675,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,X0) = X0
% 3.44/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2648,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0)
% 3.44/0.98      | v4_pre_topc(u1_struct_0(sK0),sK0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1703,c_1675]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4287,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_4285,c_2648]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_9761,plain,
% 3.44/0.98      ( k2_struct_0(sK0) = u1_struct_0(sK0)
% 3.44/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_3916,c_4287]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_9764,plain,
% 3.44/0.98      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 3.44/0.98      inference(forward_subsumption_resolution,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_9761,c_3565]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3373,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 3.44/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) != iProver_top
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1686,c_1675]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_4543,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),X0)
% 3.44/0.98      | v3_pre_topc(X0,sK0) != iProver_top
% 3.44/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1678,c_3373]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_5294,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
% 3.44/0.98      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1683,c_4543]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2747,plain,
% 3.44/0.98      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1683,c_1688]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_839,plain,
% 3.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 3.44/0.98      | sK0 != sK0
% 3.44/0.98      | sK1 != X0 ),
% 3.44/0.98      inference(resolution_lifted,[status(thm)],[c_494,c_294]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_840,plain,
% 3.44/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.44/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.44/0.98      inference(unflattening,[status(thm)],[c_839]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_842,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_840,c_27]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2878,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_2747,c_842]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_5313,plain,
% 3.44/0.98      ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
% 3.44/0.98      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_5294,c_2747,c_2878]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_32,plain,
% 3.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_26,negated_conjecture,
% 3.44/0.98      ( v3_pre_topc(sK1,sK0) ),
% 3.44/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_33,plain,
% 3.44/0.98      ( v3_pre_topc(sK1,sK0) = iProver_top ),
% 3.44/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2901,plain,
% 3.44/0.98      ( v3_pre_topc(sK1,sK0) != iProver_top
% 3.44/0.98      | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 3.44/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_2747,c_1678]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3369,plain,
% 3.44/0.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.44/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_2747,c_1686]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3631,plain,
% 3.44/0.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_3369,c_32]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3638,plain,
% 3.44/0.98      ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),sK1)
% 3.44/0.98      | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_3631,c_1675]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_3647,plain,
% 3.44/0.98      ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
% 3.44/0.98      | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.44/0.98      inference(light_normalisation,[status(thm)],[c_3638,c_2878]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_5329,plain,
% 3.44/0.98      ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
% 3.44/0.98      inference(global_propositional_subsumption,
% 3.44/0.98                [status(thm)],
% 3.44/0.98                [c_5313,c_32,c_33,c_2901,c_3647]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2737,plain,
% 3.44/0.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 3.44/0.98      inference(superposition,[status(thm)],[c_1683,c_1685]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_2875,plain,
% 3.44/0.98      ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_2747,c_2737]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_5342,plain,
% 3.44/0.98      ( k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = sK1 ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_5329,c_2875]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_9776,plain,
% 3.44/0.98      ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = sK1 ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_9764,c_5342]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_9817,plain,
% 3.44/0.98      ( sK1 = k1_xboole_0 ),
% 3.44/0.98      inference(demodulation,[status(thm)],[c_9776,c_2750]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1347,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1937,plain,
% 3.44/0.98      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.44/0.98      inference(instantiation,[status(thm)],[c_1347]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1938,plain,
% 3.44/0.98      ( sK1 != k1_xboole_0
% 3.44/0.98      | k1_xboole_0 = sK1
% 3.44/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.44/0.98      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1346,plain,( X0 = X0 ),theory(equality) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_1369,plain,
% 3.44/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.44/0.98      inference(instantiation,[status(thm)],[c_1346]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(c_24,negated_conjecture,
% 3.44/0.98      ( k1_xboole_0 != sK1 ),
% 3.44/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.44/0.98  
% 3.44/0.98  cnf(contradiction,plain,
% 3.44/0.98      ( $false ),
% 3.44/0.98      inference(minisat,[status(thm)],[c_9817,c_1938,c_1369,c_24]) ).
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  ------                               Statistics
% 3.44/0.98  
% 3.44/0.98  ------ General
% 3.44/0.98  
% 3.44/0.98  abstr_ref_over_cycles:                  0
% 3.44/0.98  abstr_ref_under_cycles:                 0
% 3.44/0.98  gc_basic_clause_elim:                   0
% 3.44/0.98  forced_gc_time:                         0
% 3.44/0.98  parsing_time:                           0.01
% 3.44/0.98  unif_index_cands_time:                  0.
% 3.44/0.98  unif_index_add_time:                    0.
% 3.44/0.98  orderings_time:                         0.
% 3.44/0.98  out_proof_time:                         0.011
% 3.44/0.98  total_time:                             0.281
% 3.44/0.98  num_of_symbols:                         50
% 3.44/0.98  num_of_terms:                           6550
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing
% 3.44/0.98  
% 3.44/0.98  num_of_splits:                          0
% 3.44/0.98  num_of_split_atoms:                     0
% 3.44/0.98  num_of_reused_defs:                     0
% 3.44/0.98  num_eq_ax_congr_red:                    11
% 3.44/0.98  num_of_sem_filtered_clauses:            1
% 3.44/0.98  num_of_subtypes:                        0
% 3.44/0.98  monotx_restored_types:                  0
% 3.44/0.98  sat_num_of_epr_types:                   0
% 3.44/0.98  sat_num_of_non_cyclic_types:            0
% 3.44/0.98  sat_guarded_non_collapsed_types:        0
% 3.44/0.98  num_pure_diseq_elim:                    0
% 3.44/0.98  simp_replaced_by:                       0
% 3.44/0.98  res_preprocessed:                       130
% 3.44/0.98  prep_upred:                             0
% 3.44/0.98  prep_unflattend:                        41
% 3.44/0.98  smt_new_axioms:                         0
% 3.44/0.98  pred_elim_cands:                        3
% 3.44/0.98  pred_elim:                              5
% 3.44/0.98  pred_elim_cl:                           5
% 3.44/0.98  pred_elim_cycles:                       9
% 3.44/0.98  merged_defs:                            0
% 3.44/0.98  merged_defs_ncl:                        0
% 3.44/0.98  bin_hyper_res:                          0
% 3.44/0.98  prep_cycles:                            4
% 3.44/0.98  pred_elim_time:                         0.016
% 3.44/0.98  splitting_time:                         0.
% 3.44/0.98  sem_filter_time:                        0.
% 3.44/0.98  monotx_time:                            0.
% 3.44/0.98  subtype_inf_time:                       0.
% 3.44/0.98  
% 3.44/0.98  ------ Problem properties
% 3.44/0.98  
% 3.44/0.98  clauses:                                25
% 3.44/0.98  conjectures:                            3
% 3.44/0.98  epr:                                    2
% 3.44/0.98  horn:                                   25
% 3.44/0.98  ground:                                 5
% 3.44/0.98  unary:                                  10
% 3.44/0.98  binary:                                 5
% 3.44/0.98  lits:                                   50
% 3.44/0.98  lits_eq:                                20
% 3.44/0.98  fd_pure:                                0
% 3.44/0.98  fd_pseudo:                              0
% 3.44/0.98  fd_cond:                                0
% 3.44/0.98  fd_pseudo_cond:                         0
% 3.44/0.98  ac_symbols:                             0
% 3.44/0.98  
% 3.44/0.98  ------ Propositional Solver
% 3.44/0.98  
% 3.44/0.98  prop_solver_calls:                      30
% 3.44/0.98  prop_fast_solver_calls:                 1139
% 3.44/0.98  smt_solver_calls:                       0
% 3.44/0.98  smt_fast_solver_calls:                  0
% 3.44/0.98  prop_num_of_clauses:                    3610
% 3.44/0.98  prop_preprocess_simplified:             7272
% 3.44/0.98  prop_fo_subsumed:                       44
% 3.44/0.98  prop_solver_time:                       0.
% 3.44/0.98  smt_solver_time:                        0.
% 3.44/0.98  smt_fast_solver_time:                   0.
% 3.44/0.98  prop_fast_solver_time:                  0.
% 3.44/0.98  prop_unsat_core_time:                   0.
% 3.44/0.98  
% 3.44/0.98  ------ QBF
% 3.44/0.98  
% 3.44/0.98  qbf_q_res:                              0
% 3.44/0.98  qbf_num_tautologies:                    0
% 3.44/0.98  qbf_prep_cycles:                        0
% 3.44/0.98  
% 3.44/0.98  ------ BMC1
% 3.44/0.98  
% 3.44/0.98  bmc1_current_bound:                     -1
% 3.44/0.98  bmc1_last_solved_bound:                 -1
% 3.44/0.98  bmc1_unsat_core_size:                   -1
% 3.44/0.98  bmc1_unsat_core_parents_size:           -1
% 3.44/0.98  bmc1_merge_next_fun:                    0
% 3.44/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.44/0.98  
% 3.44/0.98  ------ Instantiation
% 3.44/0.98  
% 3.44/0.98  inst_num_of_clauses:                    1304
% 3.44/0.98  inst_num_in_passive:                    43
% 3.44/0.98  inst_num_in_active:                     608
% 3.44/0.98  inst_num_in_unprocessed:                653
% 3.44/0.98  inst_num_of_loops:                      630
% 3.44/0.98  inst_num_of_learning_restarts:          0
% 3.44/0.98  inst_num_moves_active_passive:          18
% 3.44/0.98  inst_lit_activity:                      0
% 3.44/0.98  inst_lit_activity_moves:                0
% 3.44/0.98  inst_num_tautologies:                   0
% 3.44/0.98  inst_num_prop_implied:                  0
% 3.44/0.98  inst_num_existing_simplified:           0
% 3.44/0.98  inst_num_eq_res_simplified:             0
% 3.44/0.98  inst_num_child_elim:                    0
% 3.44/0.98  inst_num_of_dismatching_blockings:      379
% 3.44/0.98  inst_num_of_non_proper_insts:           1102
% 3.44/0.98  inst_num_of_duplicates:                 0
% 3.44/0.98  inst_inst_num_from_inst_to_res:         0
% 3.44/0.98  inst_dismatching_checking_time:         0.
% 3.44/0.98  
% 3.44/0.98  ------ Resolution
% 3.44/0.98  
% 3.44/0.98  res_num_of_clauses:                     0
% 3.44/0.98  res_num_in_passive:                     0
% 3.44/0.98  res_num_in_active:                      0
% 3.44/0.98  res_num_of_loops:                       134
% 3.44/0.98  res_forward_subset_subsumed:            73
% 3.44/0.98  res_backward_subset_subsumed:           2
% 3.44/0.98  res_forward_subsumed:                   0
% 3.44/0.98  res_backward_subsumed:                  1
% 3.44/0.98  res_forward_subsumption_resolution:     8
% 3.44/0.98  res_backward_subsumption_resolution:    0
% 3.44/0.98  res_clause_to_clause_subsumption:       748
% 3.44/0.98  res_orphan_elimination:                 0
% 3.44/0.98  res_tautology_del:                      111
% 3.44/0.98  res_num_eq_res_simplified:              0
% 3.44/0.98  res_num_sel_changes:                    0
% 3.44/0.98  res_moves_from_active_to_pass:          0
% 3.44/0.98  
% 3.44/0.98  ------ Superposition
% 3.44/0.98  
% 3.44/0.98  sup_time_total:                         0.
% 3.44/0.98  sup_time_generating:                    0.
% 3.44/0.98  sup_time_sim_full:                      0.
% 3.44/0.98  sup_time_sim_immed:                     0.
% 3.44/0.98  
% 3.44/0.98  sup_num_of_clauses:                     111
% 3.44/0.98  sup_num_in_active:                      67
% 3.44/0.98  sup_num_in_passive:                     44
% 3.44/0.98  sup_num_of_loops:                       124
% 3.44/0.98  sup_fw_superposition:                   187
% 3.44/0.98  sup_bw_superposition:                   131
% 3.44/0.98  sup_immediate_simplified:               235
% 3.44/0.98  sup_given_eliminated:                   0
% 3.44/0.98  comparisons_done:                       0
% 3.44/0.98  comparisons_avoided:                    0
% 3.44/0.98  
% 3.44/0.98  ------ Simplifications
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  sim_fw_subset_subsumed:                 41
% 3.44/0.98  sim_bw_subset_subsumed:                 8
% 3.44/0.98  sim_fw_subsumed:                        18
% 3.44/0.98  sim_bw_subsumed:                        0
% 3.44/0.98  sim_fw_subsumption_res:                 5
% 3.44/0.98  sim_bw_subsumption_res:                 0
% 3.44/0.98  sim_tautology_del:                      4
% 3.44/0.98  sim_eq_tautology_del:                   109
% 3.44/0.98  sim_eq_res_simp:                        0
% 3.44/0.98  sim_fw_demodulated:                     31
% 3.44/0.98  sim_bw_demodulated:                     59
% 3.44/0.98  sim_light_normalised:                   175
% 3.44/0.98  sim_joinable_taut:                      0
% 3.44/0.98  sim_joinable_simp:                      0
% 3.44/0.98  sim_ac_normalised:                      0
% 3.44/0.98  sim_smt_subsumption:                    0
% 3.44/0.98  
%------------------------------------------------------------------------------
