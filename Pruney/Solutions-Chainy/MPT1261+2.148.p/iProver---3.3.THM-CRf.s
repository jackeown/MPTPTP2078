%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:45 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  163 (1012 expanded)
%              Number of clauses        :  100 ( 298 expanded)
%              Number of leaves         :   19 ( 236 expanded)
%              Depth                    :   25
%              Number of atoms          :  408 (4043 expanded)
%              Number of equality atoms :  186 (1410 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f49,f49])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1312,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1313,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6136,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1312,c_1313])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_160,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_360,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_361,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_361])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_516,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_19])).

cnf(c_730,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_516])).

cnf(c_731,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_730])).

cnf(c_6250,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6136,c_731])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1684,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_2721,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1684])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1315,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1319,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3060,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1315,c_1319])).

cnf(c_6941,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2721,c_2721,c_3060])).

cnf(c_14720,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6250,c_6941])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1309,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1387,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1309])).

cnf(c_3061,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1387,c_1319])).

cnf(c_14772,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14720,c_3061])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_1311,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_1527,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1312,c_1311])).

cnf(c_6251,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6136,c_1527])).

cnf(c_6344,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_6251,c_1684])).

cnf(c_14773,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14772,c_7,c_6344])).

cnf(c_726,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_309,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_310,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,X0),X0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_310])).

cnf(c_525,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_527,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_19])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_158,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_272,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_273,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_20])).

cnf(c_278,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_158,c_278])).

cnf(c_539,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_541,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_19])).

cnf(c_728,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_541])).

cnf(c_729,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_762,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(bin_hyper_res,[status(thm)],[c_527,c_729])).

cnf(c_902,plain,
    ( k2_tops_1(sK0,sK1) != X0
    | k2_pre_topc(sK0,sK1) != sK1
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_726,c_762])).

cnf(c_903,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_14788,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14773,c_903])).

cnf(c_14824,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14788,c_1])).

cnf(c_14825,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14824,c_6251])).

cnf(c_14826,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14825,c_7])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1308,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1314,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2536,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,X1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1314])).

cnf(c_2935,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_2536])).

cnf(c_3126,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_1312,c_2935])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1310,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1458,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1312,c_1310])).

cnf(c_3128,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3126,c_1458])).

cnf(c_14790,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_14788,c_3128])).

cnf(c_1679,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_1683,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_5191,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1679,c_1683])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1316,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3059,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1316,c_1319])).

cnf(c_2067,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1315])).

cnf(c_3064,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2067,c_1319])).

cnf(c_5197,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5191,c_7,c_3059,c_3064])).

cnf(c_5198,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_5197,c_0,c_7,c_3059,c_3064])).

cnf(c_14791,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_14790,c_5198])).

cnf(c_6247,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6136,c_729])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14826,c_14791,c_6247])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:43:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     num_symb
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       true
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 19
% 7.75/1.50  conjectures                             1
% 7.75/1.50  EPR                                     1
% 7.75/1.50  Horn                                    18
% 7.75/1.50  unary                                   6
% 7.75/1.50  binary                                  11
% 7.75/1.50  lits                                    34
% 7.75/1.50  lits eq                                 16
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 0
% 7.75/1.50  fd_pseudo_cond                          0
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Schedule dynamic 5 is on 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     none
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       false
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f18,conjecture,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f19,negated_conjecture,(
% 7.75/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.75/1.50    inference(negated_conjecture,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f19])).
% 7.75/1.50  
% 7.75/1.50  fof(f34,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f34])).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f36])).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f52,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f12,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f24,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f12])).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f53,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f61,plain,(
% 7.75/1.50    l1_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f66,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f41,f49,f49])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f65,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f44,f49])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f2,axiom,(
% 7.75/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.75/1.50    inference(nnf_transformation,[],[f2])).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f14,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f56,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.75/1.50    inference(cnf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f17,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f32,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f17])).
% 7.75/1.50  
% 7.75/1.50  fof(f59,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f32])).
% 7.75/1.50  
% 7.75/1.50  fof(f16,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f31,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f31])).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    v2_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f13,axiom,(
% 7.75/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f26,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f13])).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f26])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f10,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f21,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.75/1.50    inference(ennf_transformation,[],[f10])).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.75/1.50    inference(flattening,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f51,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f9,axiom,(
% 7.75/1.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f50,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f9])).
% 7.75/1.50  
% 7.75/1.50  fof(f68,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.75/1.50    inference(definition_unfolding,[],[f51,f50])).
% 7.75/1.50  
% 7.75/1.50  fof(f15,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f29,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f29])).
% 7.75/1.50  
% 7.75/1.50  fof(f5,axiom,(
% 7.75/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f46,plain,(
% 7.75/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f5])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1312,plain,
% 7.75/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.75/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1313,plain,
% 7.75/1.50      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.75/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6136,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1312,c_1313]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18,negated_conjecture,
% 7.75/1.50      ( v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_160,plain,
% 7.75/1.50      ( v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(prop_impl,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_11,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k2_pre_topc(X1,X0) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20,negated_conjecture,
% 7.75/1.50      ( l1_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_360,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | k2_pre_topc(X1,X0) = X0
% 7.75/1.50      | sK0 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_361,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,sK0)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k2_pre_topc(sK0,X0) = X0 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_360]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_513,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,X0) = X0
% 7.75/1.50      | sK1 != X0
% 7.75/1.50      | sK0 != sK0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_160,c_361]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_514,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_513]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_516,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_514,c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_730,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(prop_impl,[status(thm)],[c_516]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_731,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_730]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6250,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_6136,c_731]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1,plain,
% 7.75/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_0,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1684,plain,
% 7.75/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2721,plain,
% 7.75/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1,c_1684]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6,plain,
% 7.75/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1315,plain,
% 7.75/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1319,plain,
% 7.75/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.75/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3060,plain,
% 7.75/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1315,c_1319]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6941,plain,
% 7.75/1.50      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_2721,c_2721,c_3060]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14720,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)))) = k1_xboole_0 ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_6250,c_6941]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_13,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_336,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.75/1.50      | sK0 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_337,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_336]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1309,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1387,plain,
% 7.75/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1312,c_1309]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3061,plain,
% 7.75/1.50      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1387,c_1319]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14772,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0))) = k1_xboole_0 ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_14720,c_3061]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7,plain,
% 7.75/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_297,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 7.75/1.50      | sK0 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_298,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_297]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1311,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1527,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1312,c_1311]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6251,plain,
% 7.75/1.50      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_6136,c_1527]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6344,plain,
% 7.75/1.50      ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_6251,c_1684]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14773,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) = sK1
% 7.75/1.50      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_14772,c_7,c_6344]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_726,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.75/1.50      inference(prop_impl,[status(thm)],[c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_15,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | r1_tarski(k2_tops_1(X1,X0),X0)
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_309,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | r1_tarski(k2_tops_1(X1,X0),X0)
% 7.75/1.50      | sK0 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_310,plain,
% 7.75/1.50      ( ~ v4_pre_topc(X0,sK0)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | r1_tarski(k2_tops_1(sK0,X0),X0) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_309]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_524,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | r1_tarski(k2_tops_1(sK0,X0),X0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.75/1.50      | sK1 != X0
% 7.75/1.50      | sK0 != sK0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_160,c_310]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_525,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_524]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_527,plain,
% 7.75/1.50      ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_525,c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17,negated_conjecture,
% 7.75/1.50      ( ~ v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_158,plain,
% 7.75/1.50      ( ~ v4_pre_topc(sK1,sK0)
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.75/1.50      inference(prop_impl,[status(thm)],[c_17]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10,plain,
% 7.75/1.50      ( v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | k2_pre_topc(X1,X0) != X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_21,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_272,plain,
% 7.75/1.50      ( v4_pre_topc(X0,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | k2_pre_topc(X1,X0) != X0
% 7.75/1.50      | sK0 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_273,plain,
% 7.75/1.50      ( v4_pre_topc(X0,sK0)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | k2_pre_topc(sK0,X0) != X0 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_272]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_277,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | v4_pre_topc(X0,sK0)
% 7.75/1.50      | k2_pre_topc(sK0,X0) != X0 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_273,c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_278,plain,
% 7.75/1.50      ( v4_pre_topc(X0,sK0)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k2_pre_topc(sK0,X0) != X0 ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_277]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_538,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,X0) != X0
% 7.75/1.50      | sK1 != X0
% 7.75/1.50      | sK0 != sK0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_158,c_278]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_539,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_538]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_541,plain,
% 7.75/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.75/1.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_539,c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_728,plain,
% 7.75/1.50      ( k2_pre_topc(sK0,sK1) != sK1
% 7.75/1.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.75/1.51      inference(prop_impl,[status(thm)],[c_541]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_729,plain,
% 7.75/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.75/1.51      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_728]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_762,plain,
% 7.75/1.51      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.75/1.51      inference(bin_hyper_res,[status(thm)],[c_527,c_729]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_902,plain,
% 7.75/1.51      ( k2_tops_1(sK0,sK1) != X0
% 7.75/1.51      | k2_pre_topc(sK0,sK1) != sK1
% 7.75/1.51      | k4_xboole_0(X0,X1) = k1_xboole_0
% 7.75/1.51      | sK1 != X1 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_726,c_762]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_903,plain,
% 7.75/1.51      ( k2_pre_topc(sK0,sK1) != sK1
% 7.75/1.51      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_902]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14788,plain,
% 7.75/1.51      ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_14773,c_903]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14824,plain,
% 7.75/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_14788,c_1]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14825,plain,
% 7.75/1.51      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_14824,c_6251]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14826,plain,
% 7.75/1.51      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_14825,c_7]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_12,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.51      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.51      | ~ l1_pre_topc(X1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_348,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.51      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.51      | sK0 != X1 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_349,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.51      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_348]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1308,plain,
% 7.75/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.51      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.75/1.51      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1314,plain,
% 7.75/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 7.75/1.51      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 7.75/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2536,plain,
% 7.75/1.51      ( k5_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,X1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1))
% 7.75/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.75/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1308,c_1314]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2935,plain,
% 7.75/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 7.75/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1312,c_2536]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3126,plain,
% 7.75/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1312,c_2935]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_324,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.51      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 7.75/1.51      | sK0 != X1 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_325,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.75/1.51      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_324]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1310,plain,
% 7.75/1.51      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 7.75/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1458,plain,
% 7.75/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1312,c_1310]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3128,plain,
% 7.75/1.51      ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_3126,c_1458]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14790,plain,
% 7.75/1.51      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_14788,c_3128]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1679,plain,
% 7.75/1.51      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1683,plain,
% 7.75/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5191,plain,
% 7.75/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1679,c_1683]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5,plain,
% 7.75/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1316,plain,
% 7.75/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3059,plain,
% 7.75/1.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1316,c_1319]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2067,plain,
% 7.75/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_7,c_1315]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3064,plain,
% 7.75/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_2067,c_1319]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5197,plain,
% 7.75/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) = X0 ),
% 7.75/1.51      inference(light_normalisation,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_5191,c_7,c_3059,c_3064]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5198,plain,
% 7.75/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.75/1.51      inference(demodulation,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_5197,c_0,c_7,c_3059,c_3064]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14791,plain,
% 7.75/1.51      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_14790,c_5198]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6247,plain,
% 7.75/1.51      ( k2_pre_topc(sK0,sK1) != sK1
% 7.75/1.51      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_6136,c_729]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(contradiction,plain,
% 7.75/1.51      ( $false ),
% 7.75/1.51      inference(minisat,[status(thm)],[c_14826,c_14791,c_6247]) ).
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  ------                               Statistics
% 7.75/1.51  
% 7.75/1.51  ------ General
% 7.75/1.51  
% 7.75/1.51  abstr_ref_over_cycles:                  0
% 7.75/1.51  abstr_ref_under_cycles:                 0
% 7.75/1.51  gc_basic_clause_elim:                   0
% 7.75/1.51  forced_gc_time:                         0
% 7.75/1.51  parsing_time:                           0.006
% 7.75/1.51  unif_index_cands_time:                  0.
% 7.75/1.51  unif_index_add_time:                    0.
% 7.75/1.51  orderings_time:                         0.
% 7.75/1.51  out_proof_time:                         0.012
% 7.75/1.51  total_time:                             0.627
% 7.75/1.51  num_of_symbols:                         48
% 7.75/1.51  num_of_terms:                           14190
% 7.75/1.51  
% 7.75/1.51  ------ Preprocessing
% 7.75/1.51  
% 7.75/1.51  num_of_splits:                          0
% 7.75/1.51  num_of_split_atoms:                     0
% 7.75/1.51  num_of_reused_defs:                     0
% 7.75/1.51  num_eq_ax_congr_red:                    12
% 7.75/1.51  num_of_sem_filtered_clauses:            1
% 7.75/1.51  num_of_subtypes:                        0
% 7.75/1.51  monotx_restored_types:                  0
% 7.75/1.51  sat_num_of_epr_types:                   0
% 7.75/1.51  sat_num_of_non_cyclic_types:            0
% 7.75/1.51  sat_guarded_non_collapsed_types:        0
% 7.75/1.51  num_pure_diseq_elim:                    0
% 7.75/1.51  simp_replaced_by:                       0
% 7.75/1.51  res_preprocessed:                       106
% 7.75/1.51  prep_upred:                             0
% 7.75/1.51  prep_unflattend:                        66
% 7.75/1.51  smt_new_axioms:                         0
% 7.75/1.51  pred_elim_cands:                        2
% 7.75/1.51  pred_elim:                              3
% 7.75/1.51  pred_elim_cl:                           3
% 7.75/1.51  pred_elim_cycles:                       6
% 7.75/1.51  merged_defs:                            16
% 7.75/1.51  merged_defs_ncl:                        0
% 7.75/1.51  bin_hyper_res:                          17
% 7.75/1.51  prep_cycles:                            4
% 7.75/1.51  pred_elim_time:                         0.006
% 7.75/1.51  splitting_time:                         0.
% 7.75/1.51  sem_filter_time:                        0.
% 7.75/1.51  monotx_time:                            0.
% 7.75/1.51  subtype_inf_time:                       0.
% 7.75/1.51  
% 7.75/1.51  ------ Problem properties
% 7.75/1.51  
% 7.75/1.51  clauses:                                19
% 7.75/1.51  conjectures:                            1
% 7.75/1.51  epr:                                    1
% 7.75/1.51  horn:                                   18
% 7.75/1.51  ground:                                 4
% 7.75/1.51  unary:                                  6
% 7.75/1.51  binary:                                 11
% 7.75/1.51  lits:                                   34
% 7.75/1.51  lits_eq:                                16
% 7.75/1.51  fd_pure:                                0
% 7.75/1.51  fd_pseudo:                              0
% 7.75/1.51  fd_cond:                                0
% 7.75/1.51  fd_pseudo_cond:                         0
% 7.75/1.51  ac_symbols:                             0
% 7.75/1.51  
% 7.75/1.51  ------ Propositional Solver
% 7.75/1.51  
% 7.75/1.51  prop_solver_calls:                      33
% 7.75/1.51  prop_fast_solver_calls:                 877
% 7.75/1.51  smt_solver_calls:                       0
% 7.75/1.51  smt_fast_solver_calls:                  0
% 7.75/1.51  prop_num_of_clauses:                    6976
% 7.75/1.51  prop_preprocess_simplified:             14269
% 7.75/1.51  prop_fo_subsumed:                       5
% 7.75/1.51  prop_solver_time:                       0.
% 7.75/1.51  smt_solver_time:                        0.
% 7.75/1.51  smt_fast_solver_time:                   0.
% 7.75/1.51  prop_fast_solver_time:                  0.
% 7.75/1.51  prop_unsat_core_time:                   0.
% 7.75/1.51  
% 7.75/1.51  ------ QBF
% 7.75/1.51  
% 7.75/1.51  qbf_q_res:                              0
% 7.75/1.51  qbf_num_tautologies:                    0
% 7.75/1.51  qbf_prep_cycles:                        0
% 7.75/1.51  
% 7.75/1.51  ------ BMC1
% 7.75/1.51  
% 7.75/1.51  bmc1_current_bound:                     -1
% 7.75/1.51  bmc1_last_solved_bound:                 -1
% 7.75/1.51  bmc1_unsat_core_size:                   -1
% 7.75/1.51  bmc1_unsat_core_parents_size:           -1
% 7.75/1.51  bmc1_merge_next_fun:                    0
% 7.75/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.75/1.51  
% 7.75/1.51  ------ Instantiation
% 7.75/1.51  
% 7.75/1.51  inst_num_of_clauses:                    2443
% 7.75/1.51  inst_num_in_passive:                    302
% 7.75/1.51  inst_num_in_active:                     1046
% 7.75/1.51  inst_num_in_unprocessed:                1095
% 7.75/1.51  inst_num_of_loops:                      1130
% 7.75/1.51  inst_num_of_learning_restarts:          0
% 7.75/1.51  inst_num_moves_active_passive:          78
% 7.75/1.51  inst_lit_activity:                      0
% 7.75/1.51  inst_lit_activity_moves:                1
% 7.75/1.51  inst_num_tautologies:                   0
% 7.75/1.51  inst_num_prop_implied:                  0
% 7.75/1.51  inst_num_existing_simplified:           0
% 7.75/1.51  inst_num_eq_res_simplified:             0
% 7.75/1.51  inst_num_child_elim:                    0
% 7.75/1.51  inst_num_of_dismatching_blockings:      454
% 7.75/1.51  inst_num_of_non_proper_insts:           1948
% 7.75/1.51  inst_num_of_duplicates:                 0
% 7.75/1.51  inst_inst_num_from_inst_to_res:         0
% 7.75/1.51  inst_dismatching_checking_time:         0.
% 7.75/1.51  
% 7.75/1.51  ------ Resolution
% 7.75/1.51  
% 7.75/1.51  res_num_of_clauses:                     0
% 7.75/1.51  res_num_in_passive:                     0
% 7.75/1.51  res_num_in_active:                      0
% 7.75/1.51  res_num_of_loops:                       110
% 7.75/1.51  res_forward_subset_subsumed:            171
% 7.75/1.51  res_backward_subset_subsumed:           0
% 7.75/1.51  res_forward_subsumed:                   0
% 7.75/1.51  res_backward_subsumed:                  3
% 7.75/1.51  res_forward_subsumption_resolution:     0
% 7.75/1.51  res_backward_subsumption_resolution:    0
% 7.75/1.51  res_clause_to_clause_subsumption:       2542
% 7.75/1.51  res_orphan_elimination:                 0
% 7.75/1.51  res_tautology_del:                      303
% 7.75/1.51  res_num_eq_res_simplified:              0
% 7.75/1.51  res_num_sel_changes:                    0
% 7.75/1.51  res_moves_from_active_to_pass:          0
% 7.75/1.51  
% 7.75/1.51  ------ Superposition
% 7.75/1.51  
% 7.75/1.51  sup_time_total:                         0.
% 7.75/1.51  sup_time_generating:                    0.
% 7.75/1.51  sup_time_sim_full:                      0.
% 7.75/1.51  sup_time_sim_immed:                     0.
% 7.75/1.51  
% 7.75/1.51  sup_num_of_clauses:                     425
% 7.75/1.51  sup_num_in_active:                      220
% 7.75/1.51  sup_num_in_passive:                     205
% 7.75/1.51  sup_num_of_loops:                       225
% 7.75/1.51  sup_fw_superposition:                   597
% 7.75/1.51  sup_bw_superposition:                   826
% 7.75/1.51  sup_immediate_simplified:               781
% 7.75/1.51  sup_given_eliminated:                   0
% 7.75/1.51  comparisons_done:                       0
% 7.75/1.51  comparisons_avoided:                    6
% 7.75/1.51  
% 7.75/1.51  ------ Simplifications
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  sim_fw_subset_subsumed:                 3
% 7.75/1.51  sim_bw_subset_subsumed:                 5
% 7.75/1.51  sim_fw_subsumed:                        172
% 7.75/1.51  sim_bw_subsumed:                        2
% 7.75/1.51  sim_fw_subsumption_res:                 0
% 7.75/1.51  sim_bw_subsumption_res:                 0
% 7.75/1.51  sim_tautology_del:                      1
% 7.75/1.51  sim_eq_tautology_del:                   258
% 7.75/1.51  sim_eq_res_simp:                        2
% 7.75/1.51  sim_fw_demodulated:                     604
% 7.75/1.51  sim_bw_demodulated:                     3
% 7.75/1.51  sim_light_normalised:                   275
% 7.75/1.51  sim_joinable_taut:                      0
% 7.75/1.51  sim_joinable_simp:                      0
% 7.75/1.51  sim_ac_normalised:                      0
% 7.75/1.51  sim_smt_subsumption:                    0
% 7.75/1.51  
%------------------------------------------------------------------------------
