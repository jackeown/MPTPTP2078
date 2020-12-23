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
% DateTime   : Thu Dec  3 12:14:35 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 708 expanded)
%              Number of clauses        :   70 ( 200 expanded)
%              Number of leaves         :   18 ( 172 expanded)
%              Depth                    :   18
%              Number of atoms          :  309 (2479 expanded)
%              Number of equality atoms :  159 ( 954 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_605,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_613,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6292,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_605,c_613])).

cnf(c_17,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_606,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6376,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6292,c_606])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_611,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10457,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_611])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10628,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10457,c_22])).

cnf(c_10629,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10628])).

cnf(c_10634,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6376,c_10629])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_615,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_616,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_640,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_616,c_10])).

cnf(c_2860,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_615,c_640])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_637,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_10])).

cnf(c_3627,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2860,c_637])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_629,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_1081,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_629,c_10])).

cnf(c_1093,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1081,c_5])).

cnf(c_1816,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1093,c_637])).

cnf(c_1832,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1816,c_629])).

cnf(c_3645,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3627,c_1832])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3688,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3645,c_7])).

cnf(c_1082,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_10])).

cnf(c_1090,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1082,c_629])).

cnf(c_1817,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1090,c_637])).

cnf(c_1826,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1817,c_5])).

cnf(c_3690,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3688,c_1826])).

cnf(c_11339,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_10634,c_3690])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_614,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_669,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_614,c_7])).

cnf(c_10092,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_669])).

cnf(c_10638,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_10092])).

cnf(c_11101,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10638,c_22])).

cnf(c_11102,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11101])).

cnf(c_11110,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_605,c_11102])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_608,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1633,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_608])).

cnf(c_840,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2153,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_19,c_18,c_840])).

cnf(c_11112,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11110,c_2153])).

cnf(c_11373,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_11339,c_11112])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_609,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10481,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_609])).

cnf(c_848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_10847,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10481,c_19,c_18,c_848])).

cnf(c_11789,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11373,c_10847])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_837,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11789,c_11373,c_837,c_16,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:21:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 3.90/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.01  
% 3.90/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/1.01  
% 3.90/1.01  ------  iProver source info
% 3.90/1.01  
% 3.90/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.90/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/1.01  git: non_committed_changes: false
% 3.90/1.01  git: last_make_outside_of_git: false
% 3.90/1.01  
% 3.90/1.01  ------ 
% 3.90/1.01  ------ Parsing...
% 3.90/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/1.01  
% 3.90/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.90/1.01  
% 3.90/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/1.01  
% 3.90/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/1.01  ------ Proving...
% 3.90/1.01  ------ Problem Properties 
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  clauses                                 21
% 3.90/1.01  conjectures                             5
% 3.90/1.01  EPR                                     2
% 3.90/1.01  Horn                                    20
% 3.90/1.01  unary                                   11
% 3.90/1.01  binary                                  4
% 3.90/1.01  lits                                    40
% 3.90/1.01  lits eq                                 16
% 3.90/1.01  fd_pure                                 0
% 3.90/1.01  fd_pseudo                               0
% 3.90/1.01  fd_cond                                 0
% 3.90/1.01  fd_pseudo_cond                          0
% 3.90/1.01  AC symbols                              0
% 3.90/1.01  
% 3.90/1.01  ------ Input Options Time Limit: Unbounded
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  ------ 
% 3.90/1.01  Current options:
% 3.90/1.01  ------ 
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  ------ Proving...
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  % SZS status Theorem for theBenchmark.p
% 3.90/1.01  
% 3.90/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/1.01  
% 3.90/1.01  fof(f18,conjecture,(
% 3.90/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f19,negated_conjecture,(
% 3.90/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.90/1.01    inference(negated_conjecture,[],[f18])).
% 3.90/1.01  
% 3.90/1.01  fof(f31,plain,(
% 3.90/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.90/1.01    inference(ennf_transformation,[],[f19])).
% 3.90/1.01  
% 3.90/1.01  fof(f32,plain,(
% 3.90/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.90/1.01    inference(flattening,[],[f31])).
% 3.90/1.01  
% 3.90/1.01  fof(f33,plain,(
% 3.90/1.01    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.90/1.01    inference(nnf_transformation,[],[f32])).
% 3.90/1.01  
% 3.90/1.01  fof(f34,plain,(
% 3.90/1.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.90/1.01    inference(flattening,[],[f33])).
% 3.90/1.01  
% 3.90/1.01  fof(f36,plain,(
% 3.90/1.01    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.90/1.01    introduced(choice_axiom,[])).
% 3.90/1.01  
% 3.90/1.01  fof(f35,plain,(
% 3.90/1.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.90/1.01    introduced(choice_axiom,[])).
% 3.90/1.01  
% 3.90/1.01  fof(f37,plain,(
% 3.90/1.01    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.90/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 3.90/1.01  
% 3.90/1.01  fof(f58,plain,(
% 3.90/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.90/1.01    inference(cnf_transformation,[],[f37])).
% 3.90/1.01  
% 3.90/1.01  fof(f12,axiom,(
% 3.90/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f24,plain,(
% 3.90/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/1.01    inference(ennf_transformation,[],[f12])).
% 3.90/1.01  
% 3.90/1.01  fof(f49,plain,(
% 3.90/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/1.01    inference(cnf_transformation,[],[f24])).
% 3.90/1.01  
% 3.90/1.01  fof(f59,plain,(
% 3.90/1.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.90/1.01    inference(cnf_transformation,[],[f37])).
% 3.90/1.01  
% 3.90/1.01  fof(f14,axiom,(
% 3.90/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f25,plain,(
% 3.90/1.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.01    inference(ennf_transformation,[],[f14])).
% 3.90/1.01  
% 3.90/1.01  fof(f26,plain,(
% 3.90/1.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.01    inference(flattening,[],[f25])).
% 3.90/1.01  
% 3.90/1.01  fof(f51,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f26])).
% 3.90/1.01  
% 3.90/1.01  fof(f57,plain,(
% 3.90/1.01    l1_pre_topc(sK0)),
% 3.90/1.01    inference(cnf_transformation,[],[f37])).
% 3.90/1.01  
% 3.90/1.01  fof(f5,axiom,(
% 3.90/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f42,plain,(
% 3.90/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f5])).
% 3.90/1.01  
% 3.90/1.01  fof(f3,axiom,(
% 3.90/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f21,plain,(
% 3.90/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.90/1.01    inference(ennf_transformation,[],[f3])).
% 3.90/1.01  
% 3.90/1.01  fof(f40,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f21])).
% 3.90/1.01  
% 3.90/1.01  fof(f7,axiom,(
% 3.90/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f44,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.90/1.01    inference(cnf_transformation,[],[f7])).
% 3.90/1.01  
% 3.90/1.01  fof(f63,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.90/1.01    inference(definition_unfolding,[],[f40,f44])).
% 3.90/1.01  
% 3.90/1.01  fof(f13,axiom,(
% 3.90/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f50,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.90/1.01    inference(cnf_transformation,[],[f13])).
% 3.90/1.01  
% 3.90/1.01  fof(f67,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.90/1.01    inference(definition_unfolding,[],[f50,f44])).
% 3.90/1.01  
% 3.90/1.01  fof(f2,axiom,(
% 3.90/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f39,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.90/1.01    inference(cnf_transformation,[],[f2])).
% 3.90/1.01  
% 3.90/1.01  fof(f61,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.90/1.01    inference(definition_unfolding,[],[f39,f44])).
% 3.90/1.01  
% 3.90/1.01  fof(f4,axiom,(
% 3.90/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f41,plain,(
% 3.90/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.90/1.01    inference(cnf_transformation,[],[f4])).
% 3.90/1.01  
% 3.90/1.01  fof(f64,plain,(
% 3.90/1.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.90/1.01    inference(definition_unfolding,[],[f41,f44])).
% 3.90/1.01  
% 3.90/1.01  fof(f6,axiom,(
% 3.90/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f43,plain,(
% 3.90/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.90/1.01    inference(cnf_transformation,[],[f6])).
% 3.90/1.01  
% 3.90/1.01  fof(f10,axiom,(
% 3.90/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f47,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.90/1.01    inference(cnf_transformation,[],[f10])).
% 3.90/1.01  
% 3.90/1.01  fof(f8,axiom,(
% 3.90/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f45,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f8])).
% 3.90/1.01  
% 3.90/1.01  fof(f65,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.90/1.01    inference(definition_unfolding,[],[f47,f45])).
% 3.90/1.01  
% 3.90/1.01  fof(f15,axiom,(
% 3.90/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f27,plain,(
% 3.90/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.90/1.01    inference(ennf_transformation,[],[f15])).
% 3.90/1.01  
% 3.90/1.01  fof(f28,plain,(
% 3.90/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.90/1.01    inference(flattening,[],[f27])).
% 3.90/1.01  
% 3.90/1.01  fof(f53,plain,(
% 3.90/1.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f28])).
% 3.90/1.01  
% 3.90/1.01  fof(f11,axiom,(
% 3.90/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f22,plain,(
% 3.90/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.90/1.01    inference(ennf_transformation,[],[f11])).
% 3.90/1.01  
% 3.90/1.01  fof(f23,plain,(
% 3.90/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/1.01    inference(flattening,[],[f22])).
% 3.90/1.01  
% 3.90/1.01  fof(f48,plain,(
% 3.90/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/1.01    inference(cnf_transformation,[],[f23])).
% 3.90/1.01  
% 3.90/1.01  fof(f66,plain,(
% 3.90/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/1.01    inference(definition_unfolding,[],[f48,f45])).
% 3.90/1.01  
% 3.90/1.01  fof(f17,axiom,(
% 3.90/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f30,plain,(
% 3.90/1.01    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.01    inference(ennf_transformation,[],[f17])).
% 3.90/1.01  
% 3.90/1.01  fof(f55,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f30])).
% 3.90/1.01  
% 3.90/1.01  fof(f16,axiom,(
% 3.90/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.90/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.01  
% 3.90/1.01  fof(f29,plain,(
% 3.90/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.90/1.01    inference(ennf_transformation,[],[f16])).
% 3.90/1.01  
% 3.90/1.01  fof(f54,plain,(
% 3.90/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f29])).
% 3.90/1.01  
% 3.90/1.01  fof(f52,plain,(
% 3.90/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.90/1.01    inference(cnf_transformation,[],[f26])).
% 3.90/1.01  
% 3.90/1.01  fof(f60,plain,(
% 3.90/1.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.90/1.01    inference(cnf_transformation,[],[f37])).
% 3.90/1.01  
% 3.90/1.01  fof(f56,plain,(
% 3.90/1.01    v2_pre_topc(sK0)),
% 3.90/1.01    inference(cnf_transformation,[],[f37])).
% 3.90/1.01  
% 3.90/1.01  cnf(c_18,negated_conjecture,
% 3.90/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.90/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_605,plain,
% 3.90/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_9,plain,
% 3.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/1.01      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.90/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_613,plain,
% 3.90/1.01      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.90/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_6292,plain,
% 3.90/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_605,c_613]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_17,negated_conjecture,
% 3.90/1.01      ( v4_pre_topc(sK1,sK0)
% 3.90/1.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_606,plain,
% 3.90/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.90/1.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_6376,plain,
% 3.90/1.01      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.90/1.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.90/1.01      inference(demodulation,[status(thm)],[c_6292,c_606]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_12,plain,
% 3.90/1.01      ( ~ v4_pre_topc(X0,X1)
% 3.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.01      | ~ l1_pre_topc(X1)
% 3.90/1.01      | k2_pre_topc(X1,X0) = X0 ),
% 3.90/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_611,plain,
% 3.90/1.01      ( k2_pre_topc(X0,X1) = X1
% 3.90/1.01      | v4_pre_topc(X1,X0) != iProver_top
% 3.90/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10457,plain,
% 3.90/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.90/1.01      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.90/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_605,c_611]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_19,negated_conjecture,
% 3.90/1.01      ( l1_pre_topc(sK0) ),
% 3.90/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_22,plain,
% 3.90/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10628,plain,
% 3.90/1.01      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.90/1.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.90/1.01      inference(global_propositional_subsumption,
% 3.90/1.01                [status(thm)],
% 3.90/1.01                [c_10457,c_22]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10629,plain,
% 3.90/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.90/1.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.90/1.01      inference(renaming,[status(thm)],[c_10628]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10634,plain,
% 3.90/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.90/1.01      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_6376,c_10629]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_4,plain,
% 3.90/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.90/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_615,plain,
% 3.90/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_2,plain,
% 3.90/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.90/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_616,plain,
% 3.90/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.90/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10,plain,
% 3.90/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.90/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_640,plain,
% 3.90/1.01      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 3.90/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/1.01      inference(demodulation,[status(thm)],[c_616,c_10]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_2860,plain,
% 3.90/1.01      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_615,c_640]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_0,plain,
% 3.90/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.90/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_637,plain,
% 3.90/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_0,c_10]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_3627,plain,
% 3.90/1.01      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_2860,c_637]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_3,plain,
% 3.90/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.90/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_5,plain,
% 3.90/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.90/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_629,plain,
% 3.90/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1081,plain,
% 3.90/1.01      ( k1_setfam_1(k2_tarski(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_629,c_10]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1093,plain,
% 3.90/1.01      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_1081,c_5]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1816,plain,
% 3.90/1.01      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_1093,c_637]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1832,plain,
% 3.90/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_1816,c_629]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_3645,plain,
% 3.90/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.90/1.01      inference(demodulation,[status(thm)],[c_3627,c_1832]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_7,plain,
% 3.90/1.01      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 3.90/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_3688,plain,
% 3.90/1.01      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_3645,c_7]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1082,plain,
% 3.90/1.01      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_5,c_10]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1090,plain,
% 3.90/1.01      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_1082,c_629]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1817,plain,
% 3.90/1.01      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_1090,c_637]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1826,plain,
% 3.90/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_1817,c_5]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_3690,plain,
% 3.90/1.01      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_3688,c_1826]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11339,plain,
% 3.90/1.01      ( k2_pre_topc(sK0,sK1) = sK1
% 3.90/1.01      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_10634,c_3690]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_13,plain,
% 3.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.01      | ~ l1_pre_topc(X1) ),
% 3.90/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_610,plain,
% 3.90/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.90/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.90/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_8,plain,
% 3.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.90/1.01      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 3.90/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_614,plain,
% 3.90/1.01      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 3.90/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.90/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_669,plain,
% 3.90/1.01      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.90/1.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.90/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_614,c_7]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10092,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 3.90/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_605,c_669]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10638,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.90/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_610,c_10092]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11101,plain,
% 3.90/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.90/1.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 3.90/1.01      inference(global_propositional_subsumption,
% 3.90/1.01                [status(thm)],
% 3.90/1.01                [c_10638,c_22]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11102,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.90/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.90/1.01      inference(renaming,[status(thm)],[c_11101]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11110,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_605,c_11102]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_15,plain,
% 3.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.01      | ~ l1_pre_topc(X1)
% 3.90/1.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.90/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_608,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.90/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_1633,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.90/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_605,c_608]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_840,plain,
% 3.90/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.01      | ~ l1_pre_topc(sK0)
% 3.90/1.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.90/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_2153,plain,
% 3.90/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.90/1.01      inference(global_propositional_subsumption,
% 3.90/1.01                [status(thm)],
% 3.90/1.01                [c_1633,c_19,c_18,c_840]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11112,plain,
% 3.90/1.01      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.90/1.01      inference(light_normalisation,[status(thm)],[c_11110,c_2153]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11373,plain,
% 3.90/1.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.90/1.01      inference(demodulation,[status(thm)],[c_11339,c_11112]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_14,plain,
% 3.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.01      | ~ l1_pre_topc(X1)
% 3.90/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.90/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_609,plain,
% 3.90/1.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.90/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.90/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.90/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10481,plain,
% 3.90/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.90/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.90/1.01      inference(superposition,[status(thm)],[c_605,c_609]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_848,plain,
% 3.90/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.01      | ~ l1_pre_topc(sK0)
% 3.90/1.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_10847,plain,
% 3.90/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/1.01      inference(global_propositional_subsumption,
% 3.90/1.01                [status(thm)],
% 3.90/1.01                [c_10481,c_19,c_18,c_848]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11789,plain,
% 3.90/1.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.90/1.01      inference(demodulation,[status(thm)],[c_11373,c_10847]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_11,plain,
% 3.90/1.01      ( v4_pre_topc(X0,X1)
% 3.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.90/1.01      | ~ l1_pre_topc(X1)
% 3.90/1.01      | ~ v2_pre_topc(X1)
% 3.90/1.01      | k2_pre_topc(X1,X0) != X0 ),
% 3.90/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_837,plain,
% 3.90/1.01      ( v4_pre_topc(sK1,sK0)
% 3.90/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.90/1.01      | ~ l1_pre_topc(sK0)
% 3.90/1.01      | ~ v2_pre_topc(sK0)
% 3.90/1.01      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.90/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_16,negated_conjecture,
% 3.90/1.01      ( ~ v4_pre_topc(sK1,sK0)
% 3.90/1.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.90/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(c_20,negated_conjecture,
% 3.90/1.01      ( v2_pre_topc(sK0) ),
% 3.90/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.90/1.01  
% 3.90/1.01  cnf(contradiction,plain,
% 3.90/1.01      ( $false ),
% 3.90/1.01      inference(minisat,
% 3.90/1.01                [status(thm)],
% 3.90/1.01                [c_11789,c_11373,c_837,c_16,c_18,c_19,c_20]) ).
% 3.90/1.01  
% 3.90/1.01  
% 3.90/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/1.01  
% 3.90/1.01  ------                               Statistics
% 3.90/1.01  
% 3.90/1.01  ------ Selected
% 3.90/1.01  
% 3.90/1.01  total_time:                             0.372
% 3.90/1.01  
%------------------------------------------------------------------------------
