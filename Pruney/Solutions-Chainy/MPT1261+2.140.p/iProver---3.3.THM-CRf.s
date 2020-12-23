%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:44 EST 2020

% Result     : Theorem 51.98s
% Output     : CNFRefutation 51.98s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 940 expanded)
%              Number of clauses        :   83 ( 300 expanded)
%              Number of leaves         :   20 ( 210 expanded)
%              Depth                    :   21
%              Number of atoms          :  342 (3339 expanded)
%              Number of equality atoms :  178 (1218 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f57,f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_743,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_759,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_743,c_6])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_740,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3832,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_759,c_740])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_744,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13269,plain,
    ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3832,c_744])).

cnf(c_26598,plain,
    ( k7_subset_1(X0,X0,X0) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_759,c_13269])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_739,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_742,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2405,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_739,c_742])).

cnf(c_2419,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_739,c_744])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2428,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2419,c_5])).

cnf(c_6984,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2405,c_2428])).

cnf(c_26600,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26598,c_6984])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_730,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3834,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3832,c_740])).

cnf(c_17448,plain,
    ( k7_subset_1(k2_tops_1(X0,X1),k2_tops_1(X0,X1),X2) = k7_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_3834])).

cnf(c_57378,plain,
    ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_17448])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_58241,plain,
    ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57378,c_25])).

cnf(c_156247,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26600,c_58241])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_745,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1650,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_745])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_746,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2034,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1650,c_746])).

cnf(c_13313,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2034,c_3832])).

cnf(c_58474,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_58241,c_13313])).

cnf(c_160167,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_156247,c_58474])).

cnf(c_3831,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_730,c_740])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_731,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4031,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3831,c_731])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_737,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5269,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_737])).

cnf(c_5793,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5269,c_25])).

cnf(c_5794,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5793])).

cnf(c_5799,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4031,c_5794])).

cnf(c_6064,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5799,c_745])).

cnf(c_7253,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6064,c_746])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8025,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7253,c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_741,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5034,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_741])).

cnf(c_5636,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_5034])).

cnf(c_5894,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5636,c_25])).

cnf(c_5895,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5894])).

cnf(c_5904,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_730,c_5895])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_733,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1177,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_733])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1521,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1177,c_22,c_21,c_1010])).

cnf(c_5909,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5904,c_1521])).

cnf(c_8033,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_8025,c_5909])).

cnf(c_164464,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_160167,c_8033])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_164467,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_164464,c_1])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_734,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2146,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_734])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2859,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2146,c_22,c_21,c_1017])).

cnf(c_164956,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_164467,c_2859])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1003,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_19,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_164956,c_164467,c_1003,c_19,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 51.98/6.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.98/6.99  
% 51.98/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.98/6.99  
% 51.98/6.99  ------  iProver source info
% 51.98/6.99  
% 51.98/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.98/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.98/6.99  git: non_committed_changes: false
% 51.98/6.99  git: last_make_outside_of_git: false
% 51.98/6.99  
% 51.98/6.99  ------ 
% 51.98/6.99  ------ Parsing...
% 51.98/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.98/6.99  
% 51.98/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.98/6.99  
% 51.98/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.98/6.99  
% 51.98/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.98/6.99  ------ Proving...
% 51.98/6.99  ------ Problem Properties 
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  clauses                                 24
% 51.98/6.99  conjectures                             5
% 51.98/6.99  EPR                                     2
% 51.98/6.99  Horn                                    23
% 51.98/6.99  unary                                   11
% 51.98/6.99  binary                                  6
% 51.98/6.99  lits                                    48
% 51.98/6.99  lits eq                                 16
% 51.98/6.99  fd_pure                                 0
% 51.98/6.99  fd_pseudo                               0
% 51.98/6.99  fd_cond                                 0
% 51.98/6.99  fd_pseudo_cond                          0
% 51.98/6.99  AC symbols                              0
% 51.98/6.99  
% 51.98/6.99  ------ Input Options Time Limit: Unbounded
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  ------ 
% 51.98/6.99  Current options:
% 51.98/6.99  ------ 
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  ------ Proving...
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  % SZS status Theorem for theBenchmark.p
% 51.98/6.99  
% 51.98/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.98/6.99  
% 51.98/6.99  fof(f10,axiom,(
% 51.98/6.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f54,plain,(
% 51.98/6.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f10])).
% 51.98/6.99  
% 51.98/6.99  fof(f8,axiom,(
% 51.98/6.99    ! [X0] : k2_subset_1(X0) = X0),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f52,plain,(
% 51.98/6.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 51.98/6.99    inference(cnf_transformation,[],[f8])).
% 51.98/6.99  
% 51.98/6.99  fof(f13,axiom,(
% 51.98/6.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f29,plain,(
% 51.98/6.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.98/6.99    inference(ennf_transformation,[],[f13])).
% 51.98/6.99  
% 51.98/6.99  fof(f57,plain,(
% 51.98/6.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f29])).
% 51.98/6.99  
% 51.98/6.99  fof(f2,axiom,(
% 51.98/6.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f46,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f2])).
% 51.98/6.99  
% 51.98/6.99  fof(f74,plain,(
% 51.98/6.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(definition_unfolding,[],[f57,f46])).
% 51.98/6.99  
% 51.98/6.99  fof(f9,axiom,(
% 51.98/6.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f25,plain,(
% 51.98/6.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.98/6.99    inference(ennf_transformation,[],[f9])).
% 51.98/6.99  
% 51.98/6.99  fof(f53,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f25])).
% 51.98/6.99  
% 51.98/6.99  fof(f73,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(definition_unfolding,[],[f53,f46])).
% 51.98/6.99  
% 51.98/6.99  fof(f14,axiom,(
% 51.98/6.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f58,plain,(
% 51.98/6.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f14])).
% 51.98/6.99  
% 51.98/6.99  fof(f11,axiom,(
% 51.98/6.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f26,plain,(
% 51.98/6.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.98/6.99    inference(ennf_transformation,[],[f11])).
% 51.98/6.99  
% 51.98/6.99  fof(f55,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f26])).
% 51.98/6.99  
% 51.98/6.99  fof(f7,axiom,(
% 51.98/6.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f51,plain,(
% 51.98/6.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.98/6.99    inference(cnf_transformation,[],[f7])).
% 51.98/6.99  
% 51.98/6.99  fof(f72,plain,(
% 51.98/6.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 51.98/6.99    inference(definition_unfolding,[],[f51,f46])).
% 51.98/6.99  
% 51.98/6.99  fof(f21,conjecture,(
% 51.98/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f22,negated_conjecture,(
% 51.98/6.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 51.98/6.99    inference(negated_conjecture,[],[f21])).
% 51.98/6.99  
% 51.98/6.99  fof(f38,plain,(
% 51.98/6.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 51.98/6.99    inference(ennf_transformation,[],[f22])).
% 51.98/6.99  
% 51.98/6.99  fof(f39,plain,(
% 51.98/6.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.98/6.99    inference(flattening,[],[f38])).
% 51.98/6.99  
% 51.98/6.99  fof(f40,plain,(
% 51.98/6.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.98/6.99    inference(nnf_transformation,[],[f39])).
% 51.98/6.99  
% 51.98/6.99  fof(f41,plain,(
% 51.98/6.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.98/6.99    inference(flattening,[],[f40])).
% 51.98/6.99  
% 51.98/6.99  fof(f43,plain,(
% 51.98/6.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.98/6.99    introduced(choice_axiom,[])).
% 51.98/6.99  
% 51.98/6.99  fof(f42,plain,(
% 51.98/6.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 51.98/6.99    introduced(choice_axiom,[])).
% 51.98/6.99  
% 51.98/6.99  fof(f44,plain,(
% 51.98/6.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 51.98/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 51.98/6.99  
% 51.98/6.99  fof(f67,plain,(
% 51.98/6.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 51.98/6.99    inference(cnf_transformation,[],[f44])).
% 51.98/6.99  
% 51.98/6.99  fof(f17,axiom,(
% 51.98/6.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f32,plain,(
% 51.98/6.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 51.98/6.99    inference(ennf_transformation,[],[f17])).
% 51.98/6.99  
% 51.98/6.99  fof(f33,plain,(
% 51.98/6.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 51.98/6.99    inference(flattening,[],[f32])).
% 51.98/6.99  
% 51.98/6.99  fof(f61,plain,(
% 51.98/6.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f33])).
% 51.98/6.99  
% 51.98/6.99  fof(f66,plain,(
% 51.98/6.99    l1_pre_topc(sK0)),
% 51.98/6.99    inference(cnf_transformation,[],[f44])).
% 51.98/6.99  
% 51.98/6.99  fof(f5,axiom,(
% 51.98/6.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f49,plain,(
% 51.98/6.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f5])).
% 51.98/6.99  
% 51.98/6.99  fof(f70,plain,(
% 51.98/6.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 51.98/6.99    inference(definition_unfolding,[],[f49,f46])).
% 51.98/6.99  
% 51.98/6.99  fof(f4,axiom,(
% 51.98/6.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f24,plain,(
% 51.98/6.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.98/6.99    inference(ennf_transformation,[],[f4])).
% 51.98/6.99  
% 51.98/6.99  fof(f48,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f24])).
% 51.98/6.99  
% 51.98/6.99  fof(f68,plain,(
% 51.98/6.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 51.98/6.99    inference(cnf_transformation,[],[f44])).
% 51.98/6.99  
% 51.98/6.99  fof(f16,axiom,(
% 51.98/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f30,plain,(
% 51.98/6.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.98/6.99    inference(ennf_transformation,[],[f16])).
% 51.98/6.99  
% 51.98/6.99  fof(f31,plain,(
% 51.98/6.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.98/6.99    inference(flattening,[],[f30])).
% 51.98/6.99  
% 51.98/6.99  fof(f59,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f31])).
% 51.98/6.99  
% 51.98/6.99  fof(f6,axiom,(
% 51.98/6.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f50,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f6])).
% 51.98/6.99  
% 51.98/6.99  fof(f71,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 51.98/6.99    inference(definition_unfolding,[],[f50,f46])).
% 51.98/6.99  
% 51.98/6.99  fof(f12,axiom,(
% 51.98/6.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f27,plain,(
% 51.98/6.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 51.98/6.99    inference(ennf_transformation,[],[f12])).
% 51.98/6.99  
% 51.98/6.99  fof(f28,plain,(
% 51.98/6.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.98/6.99    inference(flattening,[],[f27])).
% 51.98/6.99  
% 51.98/6.99  fof(f56,plain,(
% 51.98/6.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.98/6.99    inference(cnf_transformation,[],[f28])).
% 51.98/6.99  
% 51.98/6.99  fof(f20,axiom,(
% 51.98/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f37,plain,(
% 51.98/6.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.98/6.99    inference(ennf_transformation,[],[f20])).
% 51.98/6.99  
% 51.98/6.99  fof(f64,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f37])).
% 51.98/6.99  
% 51.98/6.99  fof(f3,axiom,(
% 51.98/6.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f47,plain,(
% 51.98/6.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.98/6.99    inference(cnf_transformation,[],[f3])).
% 51.98/6.99  
% 51.98/6.99  fof(f19,axiom,(
% 51.98/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 51.98/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.98/6.99  
% 51.98/6.99  fof(f36,plain,(
% 51.98/6.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.98/6.99    inference(ennf_transformation,[],[f19])).
% 51.98/6.99  
% 51.98/6.99  fof(f63,plain,(
% 51.98/6.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f36])).
% 51.98/6.99  
% 51.98/6.99  fof(f60,plain,(
% 51.98/6.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.98/6.99    inference(cnf_transformation,[],[f31])).
% 51.98/6.99  
% 51.98/6.99  fof(f69,plain,(
% 51.98/6.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 51.98/6.99    inference(cnf_transformation,[],[f44])).
% 51.98/6.99  
% 51.98/6.99  fof(f65,plain,(
% 51.98/6.99    v2_pre_topc(sK0)),
% 51.98/6.99    inference(cnf_transformation,[],[f44])).
% 51.98/6.99  
% 51.98/6.99  cnf(c_8,plain,
% 51.98/6.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 51.98/6.99      inference(cnf_transformation,[],[f54]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_743,plain,
% 51.98/6.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_6,plain,
% 51.98/6.99      ( k2_subset_1(X0) = X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f52]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_759,plain,
% 51.98/6.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 51.98/6.99      inference(light_normalisation,[status(thm)],[c_743,c_6]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_11,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.98/6.99      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 51.98/6.99      inference(cnf_transformation,[],[f74]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_740,plain,
% 51.98/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 51.98/6.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_3832,plain,
% 51.98/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_759,c_740]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_7,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.98/6.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 51.98/6.99      inference(cnf_transformation,[],[f73]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_744,plain,
% 51.98/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_13269,plain,
% 51.98/6.99      ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_3832,c_744]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_26598,plain,
% 51.98/6.99      ( k7_subset_1(X0,X0,X0) = k3_subset_1(X0,X0) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_759,c_13269]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_12,plain,
% 51.98/6.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 51.98/6.99      inference(cnf_transformation,[],[f58]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_739,plain,
% 51.98/6.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_9,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.98/6.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f55]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_742,plain,
% 51.98/6.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2405,plain,
% 51.98/6.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_739,c_742]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2419,plain,
% 51.98/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_739,c_744]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5,plain,
% 51.98/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f72]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2428,plain,
% 51.98/6.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 51.98/6.99      inference(light_normalisation,[status(thm)],[c_2419,c_5]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_6984,plain,
% 51.98/6.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 51.98/6.99      inference(light_normalisation,[status(thm)],[c_2405,c_2428]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_26600,plain,
% 51.98/6.99      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 51.98/6.99      inference(light_normalisation,[status(thm)],[c_26598,c_6984]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_21,negated_conjecture,
% 51.98/6.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.98/6.99      inference(cnf_transformation,[],[f67]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_730,plain,
% 51.98/6.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_15,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.98/6.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.98/6.99      | ~ l1_pre_topc(X1) ),
% 51.98/6.99      inference(cnf_transformation,[],[f61]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_736,plain,
% 51.98/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.98/6.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.98/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_3834,plain,
% 51.98/6.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 51.98/6.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_3832,c_740]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_17448,plain,
% 51.98/6.99      ( k7_subset_1(k2_tops_1(X0,X1),k2_tops_1(X0,X1),X2) = k7_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),X2)
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.98/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_736,c_3834]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_57378,plain,
% 51.98/6.99      ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
% 51.98/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_17448]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_22,negated_conjecture,
% 51.98/6.99      ( l1_pre_topc(sK0) ),
% 51.98/6.99      inference(cnf_transformation,[],[f66]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_25,plain,
% 51.98/6.99      ( l1_pre_topc(sK0) = iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_58241,plain,
% 51.98/6.99      ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
% 51.98/6.99      inference(global_propositional_subsumption,
% 51.98/6.99                [status(thm)],
% 51.98/6.99                [c_57378,c_25]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_156247,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_26600,c_58241]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_3,plain,
% 51.98/6.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 51.98/6.99      inference(cnf_transformation,[],[f70]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_745,plain,
% 51.98/6.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1650,plain,
% 51.98/6.99      ( r1_tarski(X0,X0) = iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_5,c_745]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2,plain,
% 51.98/6.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f48]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_746,plain,
% 51.98/6.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2034,plain,
% 51.98/6.99      ( k3_xboole_0(X0,X0) = X0 ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_1650,c_746]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_13313,plain,
% 51.98/6.99      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_2034,c_3832]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_58474,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_58241,c_13313]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_160167,plain,
% 51.98/6.99      ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_156247,c_58474]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_3831,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_740]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_20,negated_conjecture,
% 51.98/6.99      ( v4_pre_topc(sK1,sK0)
% 51.98/6.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(cnf_transformation,[],[f68]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_731,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 51.98/6.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_4031,plain,
% 51.98/6.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 51.98/6.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_3831,c_731]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_14,plain,
% 51.98/6.99      ( ~ v4_pre_topc(X0,X1)
% 51.98/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.98/6.99      | ~ l1_pre_topc(X1)
% 51.98/6.99      | k2_pre_topc(X1,X0) = X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f59]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_737,plain,
% 51.98/6.99      ( k2_pre_topc(X0,X1) = X1
% 51.98/6.99      | v4_pre_topc(X1,X0) != iProver_top
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.98/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5269,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 51.98/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_737]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5793,plain,
% 51.98/6.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 51.98/6.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 51.98/6.99      inference(global_propositional_subsumption,
% 51.98/6.99                [status(thm)],
% 51.98/6.99                [c_5269,c_25]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5794,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 51.98/6.99      inference(renaming,[status(thm)],[c_5793]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5799,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_4031,c_5794]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_6064,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_5799,c_745]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_7253,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_6064,c_746]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_4,plain,
% 51.98/6.99      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 51.98/6.99      inference(cnf_transformation,[],[f71]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_8025,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | k2_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_7253,c_4]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_10,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.98/6.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 51.98/6.99      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 51.98/6.99      inference(cnf_transformation,[],[f56]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_741,plain,
% 51.98/6.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 51.98/6.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5034,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 51.98/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_741]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5636,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 51.98/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.98/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_736,c_5034]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5894,plain,
% 51.98/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.98/6.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 51.98/6.99      inference(global_propositional_subsumption,
% 51.98/6.99                [status(thm)],
% 51.98/6.99                [c_5636,c_25]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5895,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 51.98/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 51.98/6.99      inference(renaming,[status(thm)],[c_5894]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5904,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_5895]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_18,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.98/6.99      | ~ l1_pre_topc(X1)
% 51.98/6.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 51.98/6.99      inference(cnf_transformation,[],[f64]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_733,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.98/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1177,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 51.98/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_733]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1010,plain,
% 51.98/6.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.98/6.99      | ~ l1_pre_topc(sK0)
% 51.98/6.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 51.98/6.99      inference(instantiation,[status(thm)],[c_18]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1521,plain,
% 51.98/6.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 51.98/6.99      inference(global_propositional_subsumption,
% 51.98/6.99                [status(thm)],
% 51.98/6.99                [c_1177,c_22,c_21,c_1010]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_5909,plain,
% 51.98/6.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 51.98/6.99      inference(light_normalisation,[status(thm)],[c_5904,c_1521]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_8033,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1
% 51.98/6.99      | k2_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 51.98/6.99      inference(light_normalisation,[status(thm)],[c_8025,c_5909]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_164464,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k1_xboole_0)
% 51.98/6.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_160167,c_8033]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1,plain,
% 51.98/6.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f47]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_164467,plain,
% 51.98/6.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_164464,c_1]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_17,plain,
% 51.98/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.98/6.99      | ~ l1_pre_topc(X1)
% 51.98/6.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 51.98/6.99      inference(cnf_transformation,[],[f63]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_734,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 51.98/6.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.98/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.98/6.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2146,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 51.98/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.98/6.99      inference(superposition,[status(thm)],[c_730,c_734]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1017,plain,
% 51.98/6.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.98/6.99      | ~ l1_pre_topc(sK0)
% 51.98/6.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(instantiation,[status(thm)],[c_17]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_2859,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(global_propositional_subsumption,
% 51.98/6.99                [status(thm)],
% 51.98/6.99                [c_2146,c_22,c_21,c_1017]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_164956,plain,
% 51.98/6.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(demodulation,[status(thm)],[c_164467,c_2859]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_13,plain,
% 51.98/6.99      ( v4_pre_topc(X0,X1)
% 51.98/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.98/6.99      | ~ l1_pre_topc(X1)
% 51.98/6.99      | ~ v2_pre_topc(X1)
% 51.98/6.99      | k2_pre_topc(X1,X0) != X0 ),
% 51.98/6.99      inference(cnf_transformation,[],[f60]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_1003,plain,
% 51.98/6.99      ( v4_pre_topc(sK1,sK0)
% 51.98/6.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.98/6.99      | ~ l1_pre_topc(sK0)
% 51.98/6.99      | ~ v2_pre_topc(sK0)
% 51.98/6.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 51.98/6.99      inference(instantiation,[status(thm)],[c_13]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_19,negated_conjecture,
% 51.98/6.99      ( ~ v4_pre_topc(sK1,sK0)
% 51.98/6.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 51.98/6.99      inference(cnf_transformation,[],[f69]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(c_23,negated_conjecture,
% 51.98/6.99      ( v2_pre_topc(sK0) ),
% 51.98/6.99      inference(cnf_transformation,[],[f65]) ).
% 51.98/6.99  
% 51.98/6.99  cnf(contradiction,plain,
% 51.98/6.99      ( $false ),
% 51.98/6.99      inference(minisat,
% 51.98/6.99                [status(thm)],
% 51.98/6.99                [c_164956,c_164467,c_1003,c_19,c_21,c_22,c_23]) ).
% 51.98/6.99  
% 51.98/6.99  
% 51.98/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.98/6.99  
% 51.98/6.99  ------                               Statistics
% 51.98/6.99  
% 51.98/6.99  ------ Selected
% 51.98/6.99  
% 51.98/6.99  total_time:                             6.492
% 51.98/6.99  
%------------------------------------------------------------------------------
