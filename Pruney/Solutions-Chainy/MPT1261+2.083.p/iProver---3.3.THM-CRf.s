%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:36 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 476 expanded)
%              Number of clauses        :   60 ( 127 expanded)
%              Number of leaves         :   15 ( 112 expanded)
%              Depth                    :   20
%              Number of atoms          :  302 (2063 expanded)
%              Number of equality atoms :  139 ( 692 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f31,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f49,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f34,f32,f32])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f33,f37,f37,f32])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f35,f37,f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_101,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_246,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_247,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_101,c_247])).

cnf(c_277,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_279,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_14])).

cnf(c_326,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_279])).

cnf(c_327,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_613,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_614,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2242,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_613,c_614])).

cnf(c_2599,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_327,c_2242])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1553,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_5281,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_3,c_1553])).

cnf(c_2,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5337,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5281,c_2])).

cnf(c_5566,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_5337])).

cnf(c_6496,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2599,c_5566])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_615,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8293,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_615])).

cnf(c_9129,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_8293])).

cnf(c_9150,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_613,c_9129])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_612,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_695,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_613,c_612])).

cnf(c_9157,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_9150,c_695])).

cnf(c_14990,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_6496,c_9157])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_611,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_744,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_613,c_611])).

cnf(c_14994,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14990,c_744])).

cnf(c_12,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_99,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_185,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_186,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_186,c_15])).

cnf(c_191,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_99,c_191])).

cnf(c_288,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_290,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14994,c_14990,c_290])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.07/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.07/1.49  
% 7.07/1.49  ------  iProver source info
% 7.07/1.49  
% 7.07/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.07/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.07/1.49  git: non_committed_changes: false
% 7.07/1.49  git: last_make_outside_of_git: false
% 7.07/1.49  
% 7.07/1.49  ------ 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options
% 7.07/1.49  
% 7.07/1.49  --out_options                           all
% 7.07/1.49  --tptp_safe_out                         true
% 7.07/1.49  --problem_path                          ""
% 7.07/1.49  --include_path                          ""
% 7.07/1.49  --clausifier                            res/vclausify_rel
% 7.07/1.49  --clausifier_options                    --mode clausify
% 7.07/1.49  --stdin                                 false
% 7.07/1.49  --stats_out                             all
% 7.07/1.49  
% 7.07/1.49  ------ General Options
% 7.07/1.49  
% 7.07/1.49  --fof                                   false
% 7.07/1.49  --time_out_real                         305.
% 7.07/1.49  --time_out_virtual                      -1.
% 7.07/1.49  --symbol_type_check                     false
% 7.07/1.49  --clausify_out                          false
% 7.07/1.49  --sig_cnt_out                           false
% 7.07/1.49  --trig_cnt_out                          false
% 7.07/1.49  --trig_cnt_out_tolerance                1.
% 7.07/1.49  --trig_cnt_out_sk_spl                   false
% 7.07/1.49  --abstr_cl_out                          false
% 7.07/1.49  
% 7.07/1.49  ------ Global Options
% 7.07/1.49  
% 7.07/1.49  --schedule                              default
% 7.07/1.49  --add_important_lit                     false
% 7.07/1.49  --prop_solver_per_cl                    1000
% 7.07/1.49  --min_unsat_core                        false
% 7.07/1.49  --soft_assumptions                      false
% 7.07/1.49  --soft_lemma_size                       3
% 7.07/1.49  --prop_impl_unit_size                   0
% 7.07/1.49  --prop_impl_unit                        []
% 7.07/1.49  --share_sel_clauses                     true
% 7.07/1.49  --reset_solvers                         false
% 7.07/1.49  --bc_imp_inh                            [conj_cone]
% 7.07/1.49  --conj_cone_tolerance                   3.
% 7.07/1.49  --extra_neg_conj                        none
% 7.07/1.49  --large_theory_mode                     true
% 7.07/1.49  --prolific_symb_bound                   200
% 7.07/1.49  --lt_threshold                          2000
% 7.07/1.49  --clause_weak_htbl                      true
% 7.07/1.49  --gc_record_bc_elim                     false
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing Options
% 7.07/1.49  
% 7.07/1.49  --preprocessing_flag                    true
% 7.07/1.49  --time_out_prep_mult                    0.1
% 7.07/1.49  --splitting_mode                        input
% 7.07/1.49  --splitting_grd                         true
% 7.07/1.49  --splitting_cvd                         false
% 7.07/1.49  --splitting_cvd_svl                     false
% 7.07/1.49  --splitting_nvd                         32
% 7.07/1.49  --sub_typing                            true
% 7.07/1.49  --prep_gs_sim                           true
% 7.07/1.49  --prep_unflatten                        true
% 7.07/1.49  --prep_res_sim                          true
% 7.07/1.49  --prep_upred                            true
% 7.07/1.49  --prep_sem_filter                       exhaustive
% 7.07/1.49  --prep_sem_filter_out                   false
% 7.07/1.49  --pred_elim                             true
% 7.07/1.49  --res_sim_input                         true
% 7.07/1.49  --eq_ax_congr_red                       true
% 7.07/1.49  --pure_diseq_elim                       true
% 7.07/1.49  --brand_transform                       false
% 7.07/1.49  --non_eq_to_eq                          false
% 7.07/1.49  --prep_def_merge                        true
% 7.07/1.49  --prep_def_merge_prop_impl              false
% 7.07/1.49  --prep_def_merge_mbd                    true
% 7.07/1.49  --prep_def_merge_tr_red                 false
% 7.07/1.49  --prep_def_merge_tr_cl                  false
% 7.07/1.49  --smt_preprocessing                     true
% 7.07/1.49  --smt_ac_axioms                         fast
% 7.07/1.49  --preprocessed_out                      false
% 7.07/1.49  --preprocessed_stats                    false
% 7.07/1.49  
% 7.07/1.49  ------ Abstraction refinement Options
% 7.07/1.49  
% 7.07/1.49  --abstr_ref                             []
% 7.07/1.49  --abstr_ref_prep                        false
% 7.07/1.49  --abstr_ref_until_sat                   false
% 7.07/1.49  --abstr_ref_sig_restrict                funpre
% 7.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.07/1.49  --abstr_ref_under                       []
% 7.07/1.49  
% 7.07/1.49  ------ SAT Options
% 7.07/1.49  
% 7.07/1.49  --sat_mode                              false
% 7.07/1.49  --sat_fm_restart_options                ""
% 7.07/1.49  --sat_gr_def                            false
% 7.07/1.49  --sat_epr_types                         true
% 7.07/1.49  --sat_non_cyclic_types                  false
% 7.07/1.49  --sat_finite_models                     false
% 7.07/1.49  --sat_fm_lemmas                         false
% 7.07/1.49  --sat_fm_prep                           false
% 7.07/1.49  --sat_fm_uc_incr                        true
% 7.07/1.49  --sat_out_model                         small
% 7.07/1.49  --sat_out_clauses                       false
% 7.07/1.49  
% 7.07/1.49  ------ QBF Options
% 7.07/1.49  
% 7.07/1.49  --qbf_mode                              false
% 7.07/1.49  --qbf_elim_univ                         false
% 7.07/1.49  --qbf_dom_inst                          none
% 7.07/1.49  --qbf_dom_pre_inst                      false
% 7.07/1.49  --qbf_sk_in                             false
% 7.07/1.49  --qbf_pred_elim                         true
% 7.07/1.49  --qbf_split                             512
% 7.07/1.49  
% 7.07/1.49  ------ BMC1 Options
% 7.07/1.49  
% 7.07/1.49  --bmc1_incremental                      false
% 7.07/1.49  --bmc1_axioms                           reachable_all
% 7.07/1.49  --bmc1_min_bound                        0
% 7.07/1.49  --bmc1_max_bound                        -1
% 7.07/1.49  --bmc1_max_bound_default                -1
% 7.07/1.49  --bmc1_symbol_reachability              true
% 7.07/1.49  --bmc1_property_lemmas                  false
% 7.07/1.49  --bmc1_k_induction                      false
% 7.07/1.49  --bmc1_non_equiv_states                 false
% 7.07/1.49  --bmc1_deadlock                         false
% 7.07/1.49  --bmc1_ucm                              false
% 7.07/1.49  --bmc1_add_unsat_core                   none
% 7.07/1.49  --bmc1_unsat_core_children              false
% 7.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.07/1.49  --bmc1_out_stat                         full
% 7.07/1.49  --bmc1_ground_init                      false
% 7.07/1.49  --bmc1_pre_inst_next_state              false
% 7.07/1.49  --bmc1_pre_inst_state                   false
% 7.07/1.49  --bmc1_pre_inst_reach_state             false
% 7.07/1.49  --bmc1_out_unsat_core                   false
% 7.07/1.49  --bmc1_aig_witness_out                  false
% 7.07/1.49  --bmc1_verbose                          false
% 7.07/1.49  --bmc1_dump_clauses_tptp                false
% 7.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.07/1.49  --bmc1_dump_file                        -
% 7.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.07/1.49  --bmc1_ucm_extend_mode                  1
% 7.07/1.49  --bmc1_ucm_init_mode                    2
% 7.07/1.49  --bmc1_ucm_cone_mode                    none
% 7.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.07/1.49  --bmc1_ucm_relax_model                  4
% 7.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.07/1.49  --bmc1_ucm_layered_model                none
% 7.07/1.49  --bmc1_ucm_max_lemma_size               10
% 7.07/1.49  
% 7.07/1.49  ------ AIG Options
% 7.07/1.49  
% 7.07/1.49  --aig_mode                              false
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation Options
% 7.07/1.49  
% 7.07/1.49  --instantiation_flag                    true
% 7.07/1.49  --inst_sos_flag                         false
% 7.07/1.49  --inst_sos_phase                        true
% 7.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel_side                     num_symb
% 7.07/1.49  --inst_solver_per_active                1400
% 7.07/1.49  --inst_solver_calls_frac                1.
% 7.07/1.49  --inst_passive_queue_type               priority_queues
% 7.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.07/1.49  --inst_passive_queues_freq              [25;2]
% 7.07/1.49  --inst_dismatching                      true
% 7.07/1.49  --inst_eager_unprocessed_to_passive     true
% 7.07/1.49  --inst_prop_sim_given                   true
% 7.07/1.49  --inst_prop_sim_new                     false
% 7.07/1.49  --inst_subs_new                         false
% 7.07/1.49  --inst_eq_res_simp                      false
% 7.07/1.49  --inst_subs_given                       false
% 7.07/1.49  --inst_orphan_elimination               true
% 7.07/1.49  --inst_learning_loop_flag               true
% 7.07/1.49  --inst_learning_start                   3000
% 7.07/1.49  --inst_learning_factor                  2
% 7.07/1.49  --inst_start_prop_sim_after_learn       3
% 7.07/1.49  --inst_sel_renew                        solver
% 7.07/1.49  --inst_lit_activity_flag                true
% 7.07/1.49  --inst_restr_to_given                   false
% 7.07/1.49  --inst_activity_threshold               500
% 7.07/1.49  --inst_out_proof                        true
% 7.07/1.49  
% 7.07/1.49  ------ Resolution Options
% 7.07/1.49  
% 7.07/1.49  --resolution_flag                       true
% 7.07/1.49  --res_lit_sel                           adaptive
% 7.07/1.49  --res_lit_sel_side                      none
% 7.07/1.49  --res_ordering                          kbo
% 7.07/1.49  --res_to_prop_solver                    active
% 7.07/1.49  --res_prop_simpl_new                    false
% 7.07/1.49  --res_prop_simpl_given                  true
% 7.07/1.49  --res_passive_queue_type                priority_queues
% 7.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.07/1.49  --res_passive_queues_freq               [15;5]
% 7.07/1.49  --res_forward_subs                      full
% 7.07/1.49  --res_backward_subs                     full
% 7.07/1.49  --res_forward_subs_resolution           true
% 7.07/1.49  --res_backward_subs_resolution          true
% 7.07/1.49  --res_orphan_elimination                true
% 7.07/1.49  --res_time_limit                        2.
% 7.07/1.49  --res_out_proof                         true
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Options
% 7.07/1.49  
% 7.07/1.49  --superposition_flag                    true
% 7.07/1.49  --sup_passive_queue_type                priority_queues
% 7.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.07/1.49  --demod_completeness_check              fast
% 7.07/1.49  --demod_use_ground                      true
% 7.07/1.49  --sup_to_prop_solver                    passive
% 7.07/1.49  --sup_prop_simpl_new                    true
% 7.07/1.49  --sup_prop_simpl_given                  true
% 7.07/1.49  --sup_fun_splitting                     false
% 7.07/1.49  --sup_smt_interval                      50000
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Simplification Setup
% 7.07/1.49  
% 7.07/1.49  --sup_indices_passive                   []
% 7.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_full_bw                           [BwDemod]
% 7.07/1.49  --sup_immed_triv                        [TrivRules]
% 7.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_immed_bw_main                     []
% 7.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  
% 7.07/1.49  ------ Combination Options
% 7.07/1.49  
% 7.07/1.49  --comb_res_mult                         3
% 7.07/1.49  --comb_sup_mult                         2
% 7.07/1.49  --comb_inst_mult                        10
% 7.07/1.49  
% 7.07/1.49  ------ Debug Options
% 7.07/1.49  
% 7.07/1.49  --dbg_backtrace                         false
% 7.07/1.49  --dbg_dump_prop_clauses                 false
% 7.07/1.49  --dbg_dump_prop_clauses_file            -
% 7.07/1.49  --dbg_out_stat                          false
% 7.07/1.49  ------ Parsing...
% 7.07/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.07/1.49  ------ Proving...
% 7.07/1.49  ------ Problem Properties 
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  clauses                                 13
% 7.07/1.49  conjectures                             1
% 7.07/1.49  EPR                                     0
% 7.07/1.49  Horn                                    12
% 7.07/1.49  unary                                   6
% 7.07/1.49  binary                                  6
% 7.07/1.49  lits                                    21
% 7.07/1.49  lits eq                                 13
% 7.07/1.49  fd_pure                                 0
% 7.07/1.49  fd_pseudo                               0
% 7.07/1.49  fd_cond                                 0
% 7.07/1.49  fd_pseudo_cond                          0
% 7.07/1.49  AC symbols                              0
% 7.07/1.49  
% 7.07/1.49  ------ Schedule dynamic 5 is on 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  ------ 
% 7.07/1.49  Current options:
% 7.07/1.49  ------ 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options
% 7.07/1.49  
% 7.07/1.49  --out_options                           all
% 7.07/1.49  --tptp_safe_out                         true
% 7.07/1.49  --problem_path                          ""
% 7.07/1.49  --include_path                          ""
% 7.07/1.49  --clausifier                            res/vclausify_rel
% 7.07/1.49  --clausifier_options                    --mode clausify
% 7.07/1.49  --stdin                                 false
% 7.07/1.49  --stats_out                             all
% 7.07/1.49  
% 7.07/1.49  ------ General Options
% 7.07/1.49  
% 7.07/1.49  --fof                                   false
% 7.07/1.49  --time_out_real                         305.
% 7.07/1.49  --time_out_virtual                      -1.
% 7.07/1.49  --symbol_type_check                     false
% 7.07/1.49  --clausify_out                          false
% 7.07/1.49  --sig_cnt_out                           false
% 7.07/1.49  --trig_cnt_out                          false
% 7.07/1.49  --trig_cnt_out_tolerance                1.
% 7.07/1.49  --trig_cnt_out_sk_spl                   false
% 7.07/1.49  --abstr_cl_out                          false
% 7.07/1.49  
% 7.07/1.49  ------ Global Options
% 7.07/1.49  
% 7.07/1.49  --schedule                              default
% 7.07/1.49  --add_important_lit                     false
% 7.07/1.49  --prop_solver_per_cl                    1000
% 7.07/1.49  --min_unsat_core                        false
% 7.07/1.49  --soft_assumptions                      false
% 7.07/1.49  --soft_lemma_size                       3
% 7.07/1.49  --prop_impl_unit_size                   0
% 7.07/1.49  --prop_impl_unit                        []
% 7.07/1.49  --share_sel_clauses                     true
% 7.07/1.49  --reset_solvers                         false
% 7.07/1.49  --bc_imp_inh                            [conj_cone]
% 7.07/1.49  --conj_cone_tolerance                   3.
% 7.07/1.49  --extra_neg_conj                        none
% 7.07/1.49  --large_theory_mode                     true
% 7.07/1.49  --prolific_symb_bound                   200
% 7.07/1.49  --lt_threshold                          2000
% 7.07/1.49  --clause_weak_htbl                      true
% 7.07/1.49  --gc_record_bc_elim                     false
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing Options
% 7.07/1.49  
% 7.07/1.49  --preprocessing_flag                    true
% 7.07/1.49  --time_out_prep_mult                    0.1
% 7.07/1.49  --splitting_mode                        input
% 7.07/1.49  --splitting_grd                         true
% 7.07/1.49  --splitting_cvd                         false
% 7.07/1.49  --splitting_cvd_svl                     false
% 7.07/1.49  --splitting_nvd                         32
% 7.07/1.49  --sub_typing                            true
% 7.07/1.49  --prep_gs_sim                           true
% 7.07/1.49  --prep_unflatten                        true
% 7.07/1.49  --prep_res_sim                          true
% 7.07/1.49  --prep_upred                            true
% 7.07/1.49  --prep_sem_filter                       exhaustive
% 7.07/1.49  --prep_sem_filter_out                   false
% 7.07/1.49  --pred_elim                             true
% 7.07/1.49  --res_sim_input                         true
% 7.07/1.49  --eq_ax_congr_red                       true
% 7.07/1.49  --pure_diseq_elim                       true
% 7.07/1.49  --brand_transform                       false
% 7.07/1.49  --non_eq_to_eq                          false
% 7.07/1.49  --prep_def_merge                        true
% 7.07/1.49  --prep_def_merge_prop_impl              false
% 7.07/1.49  --prep_def_merge_mbd                    true
% 7.07/1.49  --prep_def_merge_tr_red                 false
% 7.07/1.49  --prep_def_merge_tr_cl                  false
% 7.07/1.49  --smt_preprocessing                     true
% 7.07/1.49  --smt_ac_axioms                         fast
% 7.07/1.49  --preprocessed_out                      false
% 7.07/1.49  --preprocessed_stats                    false
% 7.07/1.49  
% 7.07/1.49  ------ Abstraction refinement Options
% 7.07/1.49  
% 7.07/1.49  --abstr_ref                             []
% 7.07/1.49  --abstr_ref_prep                        false
% 7.07/1.49  --abstr_ref_until_sat                   false
% 7.07/1.49  --abstr_ref_sig_restrict                funpre
% 7.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.07/1.49  --abstr_ref_under                       []
% 7.07/1.49  
% 7.07/1.49  ------ SAT Options
% 7.07/1.49  
% 7.07/1.49  --sat_mode                              false
% 7.07/1.49  --sat_fm_restart_options                ""
% 7.07/1.49  --sat_gr_def                            false
% 7.07/1.49  --sat_epr_types                         true
% 7.07/1.49  --sat_non_cyclic_types                  false
% 7.07/1.49  --sat_finite_models                     false
% 7.07/1.49  --sat_fm_lemmas                         false
% 7.07/1.49  --sat_fm_prep                           false
% 7.07/1.49  --sat_fm_uc_incr                        true
% 7.07/1.49  --sat_out_model                         small
% 7.07/1.49  --sat_out_clauses                       false
% 7.07/1.49  
% 7.07/1.49  ------ QBF Options
% 7.07/1.49  
% 7.07/1.49  --qbf_mode                              false
% 7.07/1.49  --qbf_elim_univ                         false
% 7.07/1.49  --qbf_dom_inst                          none
% 7.07/1.49  --qbf_dom_pre_inst                      false
% 7.07/1.49  --qbf_sk_in                             false
% 7.07/1.49  --qbf_pred_elim                         true
% 7.07/1.49  --qbf_split                             512
% 7.07/1.49  
% 7.07/1.49  ------ BMC1 Options
% 7.07/1.49  
% 7.07/1.49  --bmc1_incremental                      false
% 7.07/1.49  --bmc1_axioms                           reachable_all
% 7.07/1.49  --bmc1_min_bound                        0
% 7.07/1.49  --bmc1_max_bound                        -1
% 7.07/1.49  --bmc1_max_bound_default                -1
% 7.07/1.49  --bmc1_symbol_reachability              true
% 7.07/1.49  --bmc1_property_lemmas                  false
% 7.07/1.49  --bmc1_k_induction                      false
% 7.07/1.49  --bmc1_non_equiv_states                 false
% 7.07/1.49  --bmc1_deadlock                         false
% 7.07/1.49  --bmc1_ucm                              false
% 7.07/1.49  --bmc1_add_unsat_core                   none
% 7.07/1.49  --bmc1_unsat_core_children              false
% 7.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.07/1.49  --bmc1_out_stat                         full
% 7.07/1.49  --bmc1_ground_init                      false
% 7.07/1.49  --bmc1_pre_inst_next_state              false
% 7.07/1.49  --bmc1_pre_inst_state                   false
% 7.07/1.49  --bmc1_pre_inst_reach_state             false
% 7.07/1.49  --bmc1_out_unsat_core                   false
% 7.07/1.49  --bmc1_aig_witness_out                  false
% 7.07/1.49  --bmc1_verbose                          false
% 7.07/1.49  --bmc1_dump_clauses_tptp                false
% 7.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.07/1.49  --bmc1_dump_file                        -
% 7.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.07/1.49  --bmc1_ucm_extend_mode                  1
% 7.07/1.49  --bmc1_ucm_init_mode                    2
% 7.07/1.49  --bmc1_ucm_cone_mode                    none
% 7.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.07/1.49  --bmc1_ucm_relax_model                  4
% 7.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.07/1.49  --bmc1_ucm_layered_model                none
% 7.07/1.49  --bmc1_ucm_max_lemma_size               10
% 7.07/1.49  
% 7.07/1.49  ------ AIG Options
% 7.07/1.49  
% 7.07/1.49  --aig_mode                              false
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation Options
% 7.07/1.49  
% 7.07/1.49  --instantiation_flag                    true
% 7.07/1.49  --inst_sos_flag                         false
% 7.07/1.49  --inst_sos_phase                        true
% 7.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel_side                     none
% 7.07/1.49  --inst_solver_per_active                1400
% 7.07/1.49  --inst_solver_calls_frac                1.
% 7.07/1.49  --inst_passive_queue_type               priority_queues
% 7.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.07/1.49  --inst_passive_queues_freq              [25;2]
% 7.07/1.49  --inst_dismatching                      true
% 7.07/1.49  --inst_eager_unprocessed_to_passive     true
% 7.07/1.49  --inst_prop_sim_given                   true
% 7.07/1.49  --inst_prop_sim_new                     false
% 7.07/1.49  --inst_subs_new                         false
% 7.07/1.49  --inst_eq_res_simp                      false
% 7.07/1.49  --inst_subs_given                       false
% 7.07/1.49  --inst_orphan_elimination               true
% 7.07/1.49  --inst_learning_loop_flag               true
% 7.07/1.49  --inst_learning_start                   3000
% 7.07/1.49  --inst_learning_factor                  2
% 7.07/1.49  --inst_start_prop_sim_after_learn       3
% 7.07/1.49  --inst_sel_renew                        solver
% 7.07/1.49  --inst_lit_activity_flag                true
% 7.07/1.49  --inst_restr_to_given                   false
% 7.07/1.49  --inst_activity_threshold               500
% 7.07/1.49  --inst_out_proof                        true
% 7.07/1.49  
% 7.07/1.49  ------ Resolution Options
% 7.07/1.49  
% 7.07/1.49  --resolution_flag                       false
% 7.07/1.49  --res_lit_sel                           adaptive
% 7.07/1.49  --res_lit_sel_side                      none
% 7.07/1.49  --res_ordering                          kbo
% 7.07/1.49  --res_to_prop_solver                    active
% 7.07/1.49  --res_prop_simpl_new                    false
% 7.07/1.49  --res_prop_simpl_given                  true
% 7.07/1.49  --res_passive_queue_type                priority_queues
% 7.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.07/1.49  --res_passive_queues_freq               [15;5]
% 7.07/1.49  --res_forward_subs                      full
% 7.07/1.49  --res_backward_subs                     full
% 7.07/1.49  --res_forward_subs_resolution           true
% 7.07/1.49  --res_backward_subs_resolution          true
% 7.07/1.49  --res_orphan_elimination                true
% 7.07/1.49  --res_time_limit                        2.
% 7.07/1.49  --res_out_proof                         true
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Options
% 7.07/1.49  
% 7.07/1.49  --superposition_flag                    true
% 7.07/1.49  --sup_passive_queue_type                priority_queues
% 7.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.07/1.49  --demod_completeness_check              fast
% 7.07/1.49  --demod_use_ground                      true
% 7.07/1.49  --sup_to_prop_solver                    passive
% 7.07/1.49  --sup_prop_simpl_new                    true
% 7.07/1.49  --sup_prop_simpl_given                  true
% 7.07/1.49  --sup_fun_splitting                     false
% 7.07/1.49  --sup_smt_interval                      50000
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Simplification Setup
% 7.07/1.49  
% 7.07/1.49  --sup_indices_passive                   []
% 7.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_full_bw                           [BwDemod]
% 7.07/1.49  --sup_immed_triv                        [TrivRules]
% 7.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_immed_bw_main                     []
% 7.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  
% 7.07/1.49  ------ Combination Options
% 7.07/1.49  
% 7.07/1.49  --comb_res_mult                         3
% 7.07/1.49  --comb_sup_mult                         2
% 7.07/1.49  --comb_inst_mult                        10
% 7.07/1.49  
% 7.07/1.49  ------ Debug Options
% 7.07/1.49  
% 7.07/1.49  --dbg_backtrace                         false
% 7.07/1.49  --dbg_dump_prop_clauses                 false
% 7.07/1.49  --dbg_dump_prop_clauses_file            -
% 7.07/1.49  --dbg_out_stat                          false
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  ------ Proving...
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  % SZS status Theorem for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  fof(f14,conjecture,(
% 7.07/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f15,negated_conjecture,(
% 7.07/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.07/1.49    inference(negated_conjecture,[],[f14])).
% 7.07/1.49  
% 7.07/1.49  fof(f25,plain,(
% 7.07/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.07/1.49    inference(ennf_transformation,[],[f15])).
% 7.07/1.49  
% 7.07/1.49  fof(f26,plain,(
% 7.07/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.07/1.49    inference(flattening,[],[f25])).
% 7.07/1.49  
% 7.07/1.49  fof(f27,plain,(
% 7.07/1.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.07/1.49    inference(nnf_transformation,[],[f26])).
% 7.07/1.49  
% 7.07/1.49  fof(f28,plain,(
% 7.07/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.07/1.49    inference(flattening,[],[f27])).
% 7.07/1.49  
% 7.07/1.49  fof(f30,plain,(
% 7.07/1.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f29,plain,(
% 7.07/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f31,plain,(
% 7.07/1.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 7.07/1.49  
% 7.07/1.49  fof(f49,plain,(
% 7.07/1.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.07/1.49    inference(cnf_transformation,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  fof(f10,axiom,(
% 7.07/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f19,plain,(
% 7.07/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f10])).
% 7.07/1.49  
% 7.07/1.49  fof(f20,plain,(
% 7.07/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.07/1.49    inference(flattening,[],[f19])).
% 7.07/1.49  
% 7.07/1.49  fof(f41,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f20])).
% 7.07/1.49  
% 7.07/1.49  fof(f47,plain,(
% 7.07/1.49    l1_pre_topc(sK0)),
% 7.07/1.49    inference(cnf_transformation,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  fof(f48,plain,(
% 7.07/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.07/1.49    inference(cnf_transformation,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  fof(f8,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f18,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.07/1.49    inference(ennf_transformation,[],[f8])).
% 7.07/1.49  
% 7.07/1.49  fof(f39,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f18])).
% 7.07/1.49  
% 7.07/1.49  fof(f1,axiom,(
% 7.07/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f32,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f1])).
% 7.07/1.49  
% 7.07/1.49  fof(f55,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.07/1.49    inference(definition_unfolding,[],[f39,f32])).
% 7.07/1.49  
% 7.07/1.49  fof(f5,axiom,(
% 7.07/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f36,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f5])).
% 7.07/1.49  
% 7.07/1.49  fof(f3,axiom,(
% 7.07/1.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f34,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f3])).
% 7.07/1.49  
% 7.07/1.49  fof(f51,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 7.07/1.49    inference(definition_unfolding,[],[f34,f32,f32])).
% 7.07/1.49  
% 7.07/1.49  fof(f2,axiom,(
% 7.07/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f33,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f2])).
% 7.07/1.49  
% 7.07/1.49  fof(f6,axiom,(
% 7.07/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f37,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f6])).
% 7.07/1.49  
% 7.07/1.49  fof(f52,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 7.07/1.49    inference(definition_unfolding,[],[f33,f37,f37,f32])).
% 7.07/1.49  
% 7.07/1.49  fof(f4,axiom,(
% 7.07/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f35,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.07/1.49    inference(cnf_transformation,[],[f4])).
% 7.07/1.49  
% 7.07/1.49  fof(f53,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 7.07/1.49    inference(definition_unfolding,[],[f35,f37,f32])).
% 7.07/1.49  
% 7.07/1.49  fof(f11,axiom,(
% 7.07/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f21,plain,(
% 7.07/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.07/1.49    inference(ennf_transformation,[],[f11])).
% 7.07/1.49  
% 7.07/1.49  fof(f22,plain,(
% 7.07/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.07/1.49    inference(flattening,[],[f21])).
% 7.07/1.49  
% 7.07/1.49  fof(f43,plain,(
% 7.07/1.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f22])).
% 7.07/1.49  
% 7.07/1.49  fof(f7,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f16,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.07/1.49    inference(ennf_transformation,[],[f7])).
% 7.07/1.49  
% 7.07/1.49  fof(f17,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.07/1.49    inference(flattening,[],[f16])).
% 7.07/1.49  
% 7.07/1.49  fof(f38,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f17])).
% 7.07/1.49  
% 7.07/1.49  fof(f54,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.07/1.49    inference(definition_unfolding,[],[f38,f37])).
% 7.07/1.49  
% 7.07/1.49  fof(f13,axiom,(
% 7.07/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f24,plain,(
% 7.07/1.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f13])).
% 7.07/1.49  
% 7.07/1.49  fof(f45,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f24])).
% 7.07/1.49  
% 7.07/1.49  fof(f12,axiom,(
% 7.07/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f23,plain,(
% 7.07/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f12])).
% 7.07/1.49  
% 7.07/1.49  fof(f44,plain,(
% 7.07/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f23])).
% 7.07/1.49  
% 7.07/1.49  fof(f50,plain,(
% 7.07/1.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.07/1.49    inference(cnf_transformation,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  fof(f42,plain,(
% 7.07/1.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f20])).
% 7.07/1.49  
% 7.07/1.49  fof(f46,plain,(
% 7.07/1.49    v2_pre_topc(sK0)),
% 7.07/1.49    inference(cnf_transformation,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  cnf(c_13,negated_conjecture,
% 7.07/1.49      ( v4_pre_topc(sK1,sK0)
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_101,plain,
% 7.07/1.49      ( v4_pre_topc(sK1,sK0)
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(prop_impl,[status(thm)],[c_13]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_8,plain,
% 7.07/1.49      ( ~ v4_pre_topc(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | ~ l1_pre_topc(X1)
% 7.07/1.49      | k2_pre_topc(X1,X0) = X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_15,negated_conjecture,
% 7.07/1.49      ( l1_pre_topc(sK0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_246,plain,
% 7.07/1.49      ( ~ v4_pre_topc(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | k2_pre_topc(X1,X0) = X0
% 7.07/1.49      | sK0 != X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_247,plain,
% 7.07/1.49      ( ~ v4_pre_topc(X0,sK0)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k2_pre_topc(sK0,X0) = X0 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_246]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_276,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,X0) = X0
% 7.07/1.49      | sK1 != X0
% 7.07/1.49      | sK0 != sK0 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_101,c_247]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_277,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_276]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_14,negated_conjecture,
% 7.07/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.07/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_279,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_277,c_14]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_326,plain,
% 7.07/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(prop_impl,[status(thm)],[c_279]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_327,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_326]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_613,plain,
% 7.07/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.07/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.07/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_614,plain,
% 7.07/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 7.07/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2242,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_613,c_614]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2599,plain,
% 7.07/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.07/1.49      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_327,c_2242]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_3,plain,
% 7.07/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_0,plain,
% 7.07/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_1553,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5281,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_3,c_1553]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5337,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = X0 ),
% 7.07/1.49      inference(light_normalisation,[status(thm)],[c_5281,c_2]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5566,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_3,c_5337]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_6496,plain,
% 7.07/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.07/1.49      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_2599,c_5566]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_9,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | ~ l1_pre_topc(X1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_234,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | sK0 != X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_235,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_234]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_610,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.07/1.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.07/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.07/1.49      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_615,plain,
% 7.07/1.49      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 7.07/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.07/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_8293,plain,
% 7.07/1.49      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
% 7.07/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.07/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_610,c_615]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_9129,plain,
% 7.07/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.07/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_613,c_8293]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_9150,plain,
% 7.07/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_613,c_9129]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_11,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | ~ l1_pre_topc(X1)
% 7.07/1.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_210,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 7.07/1.49      | sK0 != X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_211,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_210]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_612,plain,
% 7.07/1.49      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 7.07/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_695,plain,
% 7.07/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_613,c_612]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_9157,plain,
% 7.07/1.49      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 7.07/1.49      inference(light_normalisation,[status(thm)],[c_9150,c_695]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_14990,plain,
% 7.07/1.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_6496,c_9157]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_10,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | ~ l1_pre_topc(X1)
% 7.07/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_222,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 7.07/1.49      | sK0 != X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_223,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_222]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_611,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 7.07/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_744,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_613,c_611]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_14994,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_14990,c_744]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_12,negated_conjecture,
% 7.07/1.49      ( ~ v4_pre_topc(sK1,sK0)
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_99,plain,
% 7.07/1.49      ( ~ v4_pre_topc(sK1,sK0)
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.07/1.49      inference(prop_impl,[status(thm)],[c_12]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7,plain,
% 7.07/1.49      ( v4_pre_topc(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | ~ l1_pre_topc(X1)
% 7.07/1.49      | ~ v2_pre_topc(X1)
% 7.07/1.49      | k2_pre_topc(X1,X0) != X0 ),
% 7.07/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_16,negated_conjecture,
% 7.07/1.49      ( v2_pre_topc(sK0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_185,plain,
% 7.07/1.49      ( v4_pre_topc(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.07/1.49      | ~ l1_pre_topc(X1)
% 7.07/1.49      | k2_pre_topc(X1,X0) != X0
% 7.07/1.49      | sK0 != X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_186,plain,
% 7.07/1.49      ( v4_pre_topc(X0,sK0)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | ~ l1_pre_topc(sK0)
% 7.07/1.49      | k2_pre_topc(sK0,X0) != X0 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_185]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_190,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | v4_pre_topc(X0,sK0)
% 7.07/1.49      | k2_pre_topc(sK0,X0) != X0 ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_186,c_15]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_191,plain,
% 7.07/1.49      ( v4_pre_topc(X0,sK0)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k2_pre_topc(sK0,X0) != X0 ),
% 7.07/1.49      inference(renaming,[status(thm)],[c_190]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_287,plain,
% 7.07/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,X0) != X0
% 7.07/1.49      | sK1 != X0
% 7.07/1.49      | sK0 != sK0 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_99,c_191]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_288,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.07/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_287]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_290,plain,
% 7.07/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.07/1.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_288,c_14]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(contradiction,plain,
% 7.07/1.49      ( $false ),
% 7.07/1.49      inference(minisat,[status(thm)],[c_14994,c_14990,c_290]) ).
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  ------                               Statistics
% 7.07/1.49  
% 7.07/1.49  ------ General
% 7.07/1.49  
% 7.07/1.49  abstr_ref_over_cycles:                  0
% 7.07/1.49  abstr_ref_under_cycles:                 0
% 7.07/1.49  gc_basic_clause_elim:                   0
% 7.07/1.49  forced_gc_time:                         0
% 7.07/1.49  parsing_time:                           0.013
% 7.07/1.49  unif_index_cands_time:                  0.
% 7.07/1.49  unif_index_add_time:                    0.
% 7.07/1.49  orderings_time:                         0.
% 7.07/1.49  out_proof_time:                         0.009
% 7.07/1.49  total_time:                             0.633
% 7.07/1.49  num_of_symbols:                         49
% 7.07/1.49  num_of_terms:                           20504
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing
% 7.07/1.49  
% 7.07/1.49  num_of_splits:                          0
% 7.07/1.49  num_of_split_atoms:                     0
% 7.07/1.49  num_of_reused_defs:                     0
% 7.07/1.49  num_eq_ax_congr_red:                    11
% 7.07/1.49  num_of_sem_filtered_clauses:            1
% 7.07/1.49  num_of_subtypes:                        0
% 7.07/1.49  monotx_restored_types:                  0
% 7.07/1.49  sat_num_of_epr_types:                   0
% 7.07/1.49  sat_num_of_non_cyclic_types:            0
% 7.07/1.49  sat_guarded_non_collapsed_types:        0
% 7.07/1.49  num_pure_diseq_elim:                    0
% 7.07/1.49  simp_replaced_by:                       0
% 7.07/1.49  res_preprocessed:                       87
% 7.07/1.49  prep_upred:                             0
% 7.07/1.49  prep_unflattend:                        7
% 7.07/1.49  smt_new_axioms:                         0
% 7.07/1.49  pred_elim_cands:                        1
% 7.07/1.49  pred_elim:                              3
% 7.07/1.49  pred_elim_cl:                           4
% 7.07/1.49  pred_elim_cycles:                       5
% 7.07/1.49  merged_defs:                            8
% 7.07/1.49  merged_defs_ncl:                        0
% 7.07/1.49  bin_hyper_res:                          8
% 7.07/1.49  prep_cycles:                            4
% 7.07/1.49  pred_elim_time:                         0.003
% 7.07/1.49  splitting_time:                         0.
% 7.07/1.49  sem_filter_time:                        0.
% 7.07/1.49  monotx_time:                            0.
% 7.07/1.49  subtype_inf_time:                       0.
% 7.07/1.49  
% 7.07/1.49  ------ Problem properties
% 7.07/1.49  
% 7.07/1.49  clauses:                                13
% 7.07/1.49  conjectures:                            1
% 7.07/1.49  epr:                                    0
% 7.07/1.49  horn:                                   12
% 7.07/1.49  ground:                                 3
% 7.07/1.49  unary:                                  6
% 7.07/1.49  binary:                                 6
% 7.07/1.49  lits:                                   21
% 7.07/1.49  lits_eq:                                13
% 7.07/1.49  fd_pure:                                0
% 7.07/1.49  fd_pseudo:                              0
% 7.07/1.49  fd_cond:                                0
% 7.07/1.49  fd_pseudo_cond:                         0
% 7.07/1.49  ac_symbols:                             0
% 7.07/1.49  
% 7.07/1.49  ------ Propositional Solver
% 7.07/1.49  
% 7.07/1.49  prop_solver_calls:                      32
% 7.07/1.49  prop_fast_solver_calls:                 666
% 7.07/1.49  smt_solver_calls:                       0
% 7.07/1.49  smt_fast_solver_calls:                  0
% 7.07/1.49  prop_num_of_clauses:                    6898
% 7.07/1.49  prop_preprocess_simplified:             12123
% 7.07/1.49  prop_fo_subsumed:                       3
% 7.07/1.49  prop_solver_time:                       0.
% 7.07/1.49  smt_solver_time:                        0.
% 7.07/1.49  smt_fast_solver_time:                   0.
% 7.07/1.49  prop_fast_solver_time:                  0.
% 7.07/1.49  prop_unsat_core_time:                   0.001
% 7.07/1.49  
% 7.07/1.49  ------ QBF
% 7.07/1.49  
% 7.07/1.49  qbf_q_res:                              0
% 7.07/1.49  qbf_num_tautologies:                    0
% 7.07/1.49  qbf_prep_cycles:                        0
% 7.07/1.49  
% 7.07/1.49  ------ BMC1
% 7.07/1.49  
% 7.07/1.49  bmc1_current_bound:                     -1
% 7.07/1.49  bmc1_last_solved_bound:                 -1
% 7.07/1.49  bmc1_unsat_core_size:                   -1
% 7.07/1.49  bmc1_unsat_core_parents_size:           -1
% 7.07/1.49  bmc1_merge_next_fun:                    0
% 7.07/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation
% 7.07/1.49  
% 7.07/1.49  inst_num_of_clauses:                    2021
% 7.07/1.49  inst_num_in_passive:                    991
% 7.07/1.49  inst_num_in_active:                     1026
% 7.07/1.49  inst_num_in_unprocessed:                4
% 7.07/1.49  inst_num_of_loops:                      1060
% 7.07/1.49  inst_num_of_learning_restarts:          0
% 7.07/1.49  inst_num_moves_active_passive:          29
% 7.07/1.49  inst_lit_activity:                      0
% 7.07/1.49  inst_lit_activity_moves:                1
% 7.07/1.49  inst_num_tautologies:                   0
% 7.07/1.49  inst_num_prop_implied:                  0
% 7.07/1.49  inst_num_existing_simplified:           0
% 7.07/1.49  inst_num_eq_res_simplified:             0
% 7.07/1.49  inst_num_child_elim:                    0
% 7.07/1.49  inst_num_of_dismatching_blockings:      568
% 7.07/1.49  inst_num_of_non_proper_insts:           1670
% 7.07/1.49  inst_num_of_duplicates:                 0
% 7.07/1.49  inst_inst_num_from_inst_to_res:         0
% 7.07/1.49  inst_dismatching_checking_time:         0.
% 7.07/1.49  
% 7.07/1.49  ------ Resolution
% 7.07/1.49  
% 7.07/1.49  res_num_of_clauses:                     0
% 7.07/1.49  res_num_in_passive:                     0
% 7.07/1.49  res_num_in_active:                      0
% 7.07/1.49  res_num_of_loops:                       91
% 7.07/1.49  res_forward_subset_subsumed:            123
% 7.07/1.49  res_backward_subset_subsumed:           0
% 7.07/1.49  res_forward_subsumed:                   0
% 7.07/1.49  res_backward_subsumed:                  0
% 7.07/1.49  res_forward_subsumption_resolution:     0
% 7.07/1.49  res_backward_subsumption_resolution:    0
% 7.07/1.49  res_clause_to_clause_subsumption:       2403
% 7.07/1.49  res_orphan_elimination:                 0
% 7.07/1.49  res_tautology_del:                      141
% 7.07/1.49  res_num_eq_res_simplified:              0
% 7.07/1.49  res_num_sel_changes:                    0
% 7.07/1.49  res_moves_from_active_to_pass:          0
% 7.07/1.49  
% 7.07/1.49  ------ Superposition
% 7.07/1.49  
% 7.07/1.49  sup_time_total:                         0.
% 7.07/1.49  sup_time_generating:                    0.
% 7.07/1.49  sup_time_sim_full:                      0.
% 7.07/1.49  sup_time_sim_immed:                     0.
% 7.07/1.49  
% 7.07/1.49  sup_num_of_clauses:                     446
% 7.07/1.49  sup_num_in_active:                      186
% 7.07/1.49  sup_num_in_passive:                     260
% 7.07/1.49  sup_num_of_loops:                       210
% 7.07/1.49  sup_fw_superposition:                   804
% 7.07/1.49  sup_bw_superposition:                   441
% 7.07/1.49  sup_immediate_simplified:               267
% 7.07/1.49  sup_given_eliminated:                   1
% 7.07/1.49  comparisons_done:                       0
% 7.07/1.49  comparisons_avoided:                    18
% 7.07/1.49  
% 7.07/1.49  ------ Simplifications
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  sim_fw_subset_subsumed:                 0
% 7.07/1.49  sim_bw_subset_subsumed:                 30
% 7.07/1.49  sim_fw_subsumed:                        21
% 7.07/1.49  sim_bw_subsumed:                        45
% 7.07/1.49  sim_fw_subsumption_res:                 0
% 7.07/1.49  sim_bw_subsumption_res:                 0
% 7.07/1.49  sim_tautology_del:                      1
% 7.07/1.49  sim_eq_tautology_del:                   33
% 7.07/1.49  sim_eq_res_simp:                        1
% 7.07/1.49  sim_fw_demodulated:                     59
% 7.07/1.49  sim_bw_demodulated:                     29
% 7.07/1.49  sim_light_normalised:                   159
% 7.07/1.49  sim_joinable_taut:                      0
% 7.07/1.49  sim_joinable_simp:                      0
% 7.07/1.49  sim_ac_normalised:                      0
% 7.07/1.49  sim_smt_subsumption:                    0
% 7.07/1.49  
%------------------------------------------------------------------------------
