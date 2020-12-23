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
% DateTime   : Thu Dec  3 12:14:44 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 642 expanded)
%              Number of clauses        :   66 ( 184 expanded)
%              Number of leaves         :   18 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :  322 (2549 expanded)
%              Number of equality atoms :  159 ( 900 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f49,f49])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_818,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_826,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3134,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_818,c_826])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_819,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3453,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3134,c_819])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_824,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9708,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_824])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9893,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9708,c_24])).

cnf(c_9894,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9893])).

cnf(c_9899,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3453,c_9894])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_831,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_828,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2165,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_831,c_828])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_830,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1684,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_831,c_830])).

cnf(c_2166,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2165,c_1684])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1307,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_1692,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1684,c_1307])).

cnf(c_1697,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1692,c_1684])).

cnf(c_2541,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2166,c_1697])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1419,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_10,c_1307])).

cnf(c_2591,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2541,c_1419])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3766,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2591,c_9])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3769,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3766,c_7])).

cnf(c_10212,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_9899,c_3769])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_823,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_827,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8872,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_827])).

cnf(c_8894,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_8872])).

cnf(c_9111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8894,c_24])).

cnf(c_9112,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9111])).

cnf(c_9120,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_818,c_9112])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_821,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2044,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_821])).

cnf(c_1064,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2316,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_21,c_20,c_1064])).

cnf(c_9122,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_9120,c_2316])).

cnf(c_10338,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_10212,c_9122])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_822,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9732,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_822])).

cnf(c_1067,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9958,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9732,c_21,c_20,c_1067])).

cnf(c_10624,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10338,c_9958])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1061,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10624,c_10338,c_1061,c_18,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:54:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.03/0.99  
% 4.03/0.99  ------  iProver source info
% 4.03/0.99  
% 4.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.03/0.99  git: non_committed_changes: false
% 4.03/0.99  git: last_make_outside_of_git: false
% 4.03/0.99  
% 4.03/0.99  ------ 
% 4.03/0.99  ------ Parsing...
% 4.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.03/0.99  ------ Proving...
% 4.03/0.99  ------ Problem Properties 
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  clauses                                 22
% 4.03/0.99  conjectures                             5
% 4.03/0.99  EPR                                     4
% 4.03/0.99  Horn                                    21
% 4.03/0.99  unary                                   9
% 4.03/0.99  binary                                  6
% 4.03/0.99  lits                                    45
% 4.03/0.99  lits eq                                 17
% 4.03/0.99  fd_pure                                 0
% 4.03/0.99  fd_pseudo                               0
% 4.03/0.99  fd_cond                                 0
% 4.03/0.99  fd_pseudo_cond                          1
% 4.03/0.99  AC symbols                              0
% 4.03/0.99  
% 4.03/0.99  ------ Input Options Time Limit: Unbounded
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  ------ 
% 4.03/0.99  Current options:
% 4.03/0.99  ------ 
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  ------ Proving...
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  % SZS status Theorem for theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  fof(f16,conjecture,(
% 4.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f17,negated_conjecture,(
% 4.03/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 4.03/0.99    inference(negated_conjecture,[],[f16])).
% 4.03/0.99  
% 4.03/0.99  fof(f28,plain,(
% 4.03/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.03/0.99    inference(ennf_transformation,[],[f17])).
% 4.03/0.99  
% 4.03/0.99  fof(f29,plain,(
% 4.03/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.03/0.99    inference(flattening,[],[f28])).
% 4.03/0.99  
% 4.03/0.99  fof(f33,plain,(
% 4.03/0.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.03/0.99    inference(nnf_transformation,[],[f29])).
% 4.03/0.99  
% 4.03/0.99  fof(f34,plain,(
% 4.03/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.03/0.99    inference(flattening,[],[f33])).
% 4.03/0.99  
% 4.03/0.99  fof(f36,plain,(
% 4.03/0.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.03/0.99    introduced(choice_axiom,[])).
% 4.03/0.99  
% 4.03/0.99  fof(f35,plain,(
% 4.03/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.03/0.99    introduced(choice_axiom,[])).
% 4.03/0.99  
% 4.03/0.99  fof(f37,plain,(
% 4.03/0.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 4.03/0.99  
% 4.03/0.99  fof(f59,plain,(
% 4.03/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f11,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f21,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.03/0.99    inference(ennf_transformation,[],[f11])).
% 4.03/0.99  
% 4.03/0.99  fof(f51,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f21])).
% 4.03/0.99  
% 4.03/0.99  fof(f60,plain,(
% 4.03/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f12,axiom,(
% 4.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f22,plain,(
% 4.03/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/0.99    inference(ennf_transformation,[],[f12])).
% 4.03/0.99  
% 4.03/0.99  fof(f23,plain,(
% 4.03/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/0.99    inference(flattening,[],[f22])).
% 4.03/0.99  
% 4.03/0.99  fof(f52,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f23])).
% 4.03/0.99  
% 4.03/0.99  fof(f58,plain,(
% 4.03/0.99    l1_pre_topc(sK0)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f2,axiom,(
% 4.03/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f30,plain,(
% 4.03/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.03/0.99    inference(nnf_transformation,[],[f2])).
% 4.03/0.99  
% 4.03/0.99  fof(f31,plain,(
% 4.03/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.03/0.99    inference(flattening,[],[f30])).
% 4.03/0.99  
% 4.03/0.99  fof(f39,plain,(
% 4.03/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.03/0.99    inference(cnf_transformation,[],[f31])).
% 4.03/0.99  
% 4.03/0.99  fof(f67,plain,(
% 4.03/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.03/0.99    inference(equality_resolution,[],[f39])).
% 4.03/0.99  
% 4.03/0.99  fof(f6,axiom,(
% 4.03/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f18,plain,(
% 4.03/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.03/0.99    inference(ennf_transformation,[],[f6])).
% 4.03/0.99  
% 4.03/0.99  fof(f46,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f18])).
% 4.03/0.99  
% 4.03/0.99  fof(f9,axiom,(
% 4.03/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f49,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f9])).
% 4.03/0.99  
% 4.03/0.99  fof(f64,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(definition_unfolding,[],[f46,f49])).
% 4.03/0.99  
% 4.03/0.99  fof(f3,axiom,(
% 4.03/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f32,plain,(
% 4.03/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.03/0.99    inference(nnf_transformation,[],[f3])).
% 4.03/0.99  
% 4.03/0.99  fof(f43,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f32])).
% 4.03/0.99  
% 4.03/0.99  fof(f1,axiom,(
% 4.03/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f38,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f1])).
% 4.03/0.99  
% 4.03/0.99  fof(f63,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.03/0.99    inference(definition_unfolding,[],[f38,f49,f49])).
% 4.03/0.99  
% 4.03/0.99  fof(f4,axiom,(
% 4.03/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f44,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f4])).
% 4.03/0.99  
% 4.03/0.99  fof(f62,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.03/0.99    inference(definition_unfolding,[],[f44,f49])).
% 4.03/0.99  
% 4.03/0.99  fof(f8,axiom,(
% 4.03/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f48,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f8])).
% 4.03/0.99  
% 4.03/0.99  fof(f65,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.03/0.99    inference(definition_unfolding,[],[f48,f49])).
% 4.03/0.99  
% 4.03/0.99  fof(f7,axiom,(
% 4.03/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f47,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f7])).
% 4.03/0.99  
% 4.03/0.99  fof(f5,axiom,(
% 4.03/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f45,plain,(
% 4.03/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.03/0.99    inference(cnf_transformation,[],[f5])).
% 4.03/0.99  
% 4.03/0.99  fof(f13,axiom,(
% 4.03/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f24,plain,(
% 4.03/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.03/0.99    inference(ennf_transformation,[],[f13])).
% 4.03/0.99  
% 4.03/0.99  fof(f25,plain,(
% 4.03/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.03/0.99    inference(flattening,[],[f24])).
% 4.03/0.99  
% 4.03/0.99  fof(f54,plain,(
% 4.03/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f25])).
% 4.03/0.99  
% 4.03/0.99  fof(f10,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f19,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.03/0.99    inference(ennf_transformation,[],[f10])).
% 4.03/0.99  
% 4.03/0.99  fof(f20,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.03/0.99    inference(flattening,[],[f19])).
% 4.03/0.99  
% 4.03/0.99  fof(f50,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f20])).
% 4.03/0.99  
% 4.03/0.99  fof(f15,axiom,(
% 4.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f27,plain,(
% 4.03/0.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/0.99    inference(ennf_transformation,[],[f15])).
% 4.03/0.99  
% 4.03/0.99  fof(f56,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f27])).
% 4.03/0.99  
% 4.03/0.99  fof(f14,axiom,(
% 4.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f26,plain,(
% 4.03/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.03/0.99    inference(ennf_transformation,[],[f14])).
% 4.03/0.99  
% 4.03/0.99  fof(f55,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f26])).
% 4.03/0.99  
% 4.03/0.99  fof(f53,plain,(
% 4.03/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f23])).
% 4.03/0.99  
% 4.03/0.99  fof(f61,plain,(
% 4.03/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f57,plain,(
% 4.03/0.99    v2_pre_topc(sK0)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  cnf(c_20,negated_conjecture,
% 4.03/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.03/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_818,plain,
% 4.03/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_12,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.03/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.03/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_826,plain,
% 4.03/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 4.03/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3134,plain,
% 4.03/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_818,c_826]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_19,negated_conjecture,
% 4.03/0.99      ( v4_pre_topc(sK1,sK0)
% 4.03/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_819,plain,
% 4.03/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 4.03/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3453,plain,
% 4.03/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 4.03/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_3134,c_819]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14,plain,
% 4.03/0.99      ( ~ v4_pre_topc(X0,X1)
% 4.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/0.99      | ~ l1_pre_topc(X1)
% 4.03/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_824,plain,
% 4.03/0.99      ( k2_pre_topc(X0,X1) = X1
% 4.03/0.99      | v4_pre_topc(X1,X0) != iProver_top
% 4.03/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.03/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9708,plain,
% 4.03/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 4.03/0.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 4.03/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_818,c_824]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_21,negated_conjecture,
% 4.03/0.99      ( l1_pre_topc(sK0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f58]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_24,plain,
% 4.03/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9893,plain,
% 4.03/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 4.03/0.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 4.03/0.99      inference(global_propositional_subsumption,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_9708,c_24]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9894,plain,
% 4.03/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 4.03/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 4.03/0.99      inference(renaming,[status(thm)],[c_9893]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9899,plain,
% 4.03/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 4.03/0.99      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_3453,c_9894]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_4,plain,
% 4.03/0.99      ( r1_tarski(X0,X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_831,plain,
% 4.03/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_8,plain,
% 4.03/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_828,plain,
% 4.03/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 4.03/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2165,plain,
% 4.03/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_831,c_828]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_5,plain,
% 4.03/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_830,plain,
% 4.03/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 4.03/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1684,plain,
% 4.03/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_831,c_830]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2166,plain,
% 4.03/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.03/0.99      inference(light_normalisation,[status(thm)],[c_2165,c_1684]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1,plain,
% 4.03/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.03/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_0,plain,
% 4.03/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1307,plain,
% 4.03/0.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1692,plain,
% 4.03/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1684,c_1307]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1697,plain,
% 4.03/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.03/0.99      inference(light_normalisation,[status(thm)],[c_1692,c_1684]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2541,plain,
% 4.03/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_2166,c_1697]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_10,plain,
% 4.03/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1419,plain,
% 4.03/0.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_10,c_1307]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2591,plain,
% 4.03/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_2541,c_1419]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9,plain,
% 4.03/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3766,plain,
% 4.03/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_2591,c_9]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_7,plain,
% 4.03/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3769,plain,
% 4.03/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.03/0.99      inference(light_normalisation,[status(thm)],[c_3766,c_7]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_10212,plain,
% 4.03/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 4.03/0.99      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_9899,c_3769]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_15,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/0.99      | ~ l1_pre_topc(X1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_823,plain,
% 4.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.03/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.03/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_11,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.03/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.03/0.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_827,plain,
% 4.03/0.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 4.03/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 4.03/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_8872,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 4.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_818,c_827]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_8894,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 4.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.03/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_823,c_8872]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9111,plain,
% 4.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.03/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 4.03/0.99      inference(global_propositional_subsumption,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_8894,c_24]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9112,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 4.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.03/0.99      inference(renaming,[status(thm)],[c_9111]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9120,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_818,c_9112]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_17,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/0.99      | ~ l1_pre_topc(X1)
% 4.03/0.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_821,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 4.03/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.03/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2044,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 4.03/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_818,c_821]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1064,plain,
% 4.03/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.03/0.99      | ~ l1_pre_topc(sK0)
% 4.03/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 4.03/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2316,plain,
% 4.03/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 4.03/0.99      inference(global_propositional_subsumption,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_2044,c_21,c_20,c_1064]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9122,plain,
% 4.03/0.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 4.03/0.99      inference(light_normalisation,[status(thm)],[c_9120,c_2316]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_10338,plain,
% 4.03/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_10212,c_9122]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_16,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/0.99      | ~ l1_pre_topc(X1)
% 4.03/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_822,plain,
% 4.03/0.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 4.03/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.03/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9732,plain,
% 4.03/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 4.03/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_818,c_822]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1067,plain,
% 4.03/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.03/0.99      | ~ l1_pre_topc(sK0)
% 4.03/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 4.03/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9958,plain,
% 4.03/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 4.03/0.99      inference(global_propositional_subsumption,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_9732,c_21,c_20,c_1067]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_10624,plain,
% 4.03/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_10338,c_9958]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13,plain,
% 4.03/0.99      ( v4_pre_topc(X0,X1)
% 4.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.03/0.99      | ~ l1_pre_topc(X1)
% 4.03/0.99      | ~ v2_pre_topc(X1)
% 4.03/0.99      | k2_pre_topc(X1,X0) != X0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1061,plain,
% 4.03/0.99      ( v4_pre_topc(sK1,sK0)
% 4.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.03/0.99      | ~ l1_pre_topc(sK0)
% 4.03/0.99      | ~ v2_pre_topc(sK0)
% 4.03/0.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 4.03/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_18,negated_conjecture,
% 4.03/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 4.03/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_22,negated_conjecture,
% 4.03/0.99      ( v2_pre_topc(sK0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(contradiction,plain,
% 4.03/0.99      ( $false ),
% 4.03/0.99      inference(minisat,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_10624,c_10338,c_1061,c_18,c_20,c_21,c_22]) ).
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  ------                               Statistics
% 4.03/0.99  
% 4.03/0.99  ------ Selected
% 4.03/0.99  
% 4.03/0.99  total_time:                             0.317
% 4.03/0.99  
%------------------------------------------------------------------------------
