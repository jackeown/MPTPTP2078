%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:57 EST 2020

% Result     : Theorem 15.78s
% Output     : CNFRefutation 15.78s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 540 expanded)
%              Number of clauses        :  100 ( 165 expanded)
%              Number of leaves         :   18 ( 130 expanded)
%              Depth                    :   23
%              Number of atoms          :  558 (2227 expanded)
%              Number of equality atoms :  153 ( 500 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f51,f50])).

fof(f76,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | k2_tops_1(X0,X1) != X1 )
            & ( k2_tops_1(X0,X1) = X1
              | ~ v3_tops_1(X1,X0) ) )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = X1
      | ~ v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_432,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_434,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_23,c_22])).

cnf(c_1046,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_1048,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_1037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_1043,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_2033,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1043])).

cnf(c_3760,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1048,c_2033])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3760,c_1044])).

cnf(c_27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1102,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_1103,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1234,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_1241,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_15013,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3807,c_27,c_1103,c_1241])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1050,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3015,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1050])).

cnf(c_15055,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15013,c_3015])).

cnf(c_50251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15055,c_27,c_1103])).

cnf(c_50252,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_50251])).

cnf(c_50258,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_50252])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_1111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_50279,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50258,c_27,c_1111])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_1042,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_2276,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1042])).

cnf(c_4786,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1048,c_2276])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_1038,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1454,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1048,c_1038])).

cnf(c_4792,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4786,c_1454])).

cnf(c_50339,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_50279,c_4792])).

cnf(c_2274,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1048,c_1042])).

cnf(c_50344,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_50339,c_2274])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_23])).

cnf(c_1047,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_2155,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1047])).

cnf(c_3317,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1048,c_2155])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_18,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_19,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_267,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_268,plain,
    ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X0,sK0)
    | v3_tops_1(k2_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_23])).

cnf(c_273,plain,
    ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_356,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0
    | k2_tops_1(sK0,X2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_273])).

cnf(c_357,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(k2_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_306,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_307,plain,
    ( v4_pre_topc(k2_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_361,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X0,sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_23,c_307])).

cnf(c_362,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_572,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_500,c_362])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_288,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_289,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_23])).

cnf(c_294,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
    | k2_pre_topc(sK0,X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_572,c_294])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_548])).

cnf(c_1036,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_2401,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1048,c_1036])).

cnf(c_3321,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3317,c_2401])).

cnf(c_50443,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50344,c_3321])).

cnf(c_20,negated_conjecture,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50443,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:23:55 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.78/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.78/2.49  
% 15.78/2.49  ------  iProver source info
% 15.78/2.49  
% 15.78/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.78/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.78/2.49  git: non_committed_changes: false
% 15.78/2.49  git: last_make_outside_of_git: false
% 15.78/2.49  
% 15.78/2.49  ------ 
% 15.78/2.49  
% 15.78/2.49  ------ Input Options
% 15.78/2.49  
% 15.78/2.49  --out_options                           all
% 15.78/2.49  --tptp_safe_out                         true
% 15.78/2.49  --problem_path                          ""
% 15.78/2.49  --include_path                          ""
% 15.78/2.49  --clausifier                            res/vclausify_rel
% 15.78/2.49  --clausifier_options                    ""
% 15.78/2.49  --stdin                                 false
% 15.78/2.49  --stats_out                             all
% 15.78/2.49  
% 15.78/2.49  ------ General Options
% 15.78/2.49  
% 15.78/2.49  --fof                                   false
% 15.78/2.49  --time_out_real                         305.
% 15.78/2.49  --time_out_virtual                      -1.
% 15.78/2.49  --symbol_type_check                     false
% 15.78/2.49  --clausify_out                          false
% 15.78/2.49  --sig_cnt_out                           false
% 15.78/2.49  --trig_cnt_out                          false
% 15.78/2.49  --trig_cnt_out_tolerance                1.
% 15.78/2.49  --trig_cnt_out_sk_spl                   false
% 15.78/2.49  --abstr_cl_out                          false
% 15.78/2.49  
% 15.78/2.49  ------ Global Options
% 15.78/2.49  
% 15.78/2.49  --schedule                              default
% 15.78/2.49  --add_important_lit                     false
% 15.78/2.49  --prop_solver_per_cl                    1000
% 15.78/2.49  --min_unsat_core                        false
% 15.78/2.49  --soft_assumptions                      false
% 15.78/2.49  --soft_lemma_size                       3
% 15.78/2.49  --prop_impl_unit_size                   0
% 15.78/2.49  --prop_impl_unit                        []
% 15.78/2.49  --share_sel_clauses                     true
% 15.78/2.49  --reset_solvers                         false
% 15.78/2.49  --bc_imp_inh                            [conj_cone]
% 15.78/2.49  --conj_cone_tolerance                   3.
% 15.78/2.49  --extra_neg_conj                        none
% 15.78/2.49  --large_theory_mode                     true
% 15.78/2.49  --prolific_symb_bound                   200
% 15.78/2.49  --lt_threshold                          2000
% 15.78/2.49  --clause_weak_htbl                      true
% 15.78/2.49  --gc_record_bc_elim                     false
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing Options
% 15.78/2.49  
% 15.78/2.49  --preprocessing_flag                    true
% 15.78/2.49  --time_out_prep_mult                    0.1
% 15.78/2.49  --splitting_mode                        input
% 15.78/2.49  --splitting_grd                         true
% 15.78/2.49  --splitting_cvd                         false
% 15.78/2.49  --splitting_cvd_svl                     false
% 15.78/2.49  --splitting_nvd                         32
% 15.78/2.49  --sub_typing                            true
% 15.78/2.49  --prep_gs_sim                           true
% 15.78/2.49  --prep_unflatten                        true
% 15.78/2.49  --prep_res_sim                          true
% 15.78/2.49  --prep_upred                            true
% 15.78/2.49  --prep_sem_filter                       exhaustive
% 15.78/2.49  --prep_sem_filter_out                   false
% 15.78/2.49  --pred_elim                             true
% 15.78/2.49  --res_sim_input                         true
% 15.78/2.49  --eq_ax_congr_red                       true
% 15.78/2.49  --pure_diseq_elim                       true
% 15.78/2.49  --brand_transform                       false
% 15.78/2.49  --non_eq_to_eq                          false
% 15.78/2.49  --prep_def_merge                        true
% 15.78/2.49  --prep_def_merge_prop_impl              false
% 15.78/2.49  --prep_def_merge_mbd                    true
% 15.78/2.49  --prep_def_merge_tr_red                 false
% 15.78/2.49  --prep_def_merge_tr_cl                  false
% 15.78/2.49  --smt_preprocessing                     true
% 15.78/2.49  --smt_ac_axioms                         fast
% 15.78/2.49  --preprocessed_out                      false
% 15.78/2.49  --preprocessed_stats                    false
% 15.78/2.49  
% 15.78/2.49  ------ Abstraction refinement Options
% 15.78/2.49  
% 15.78/2.49  --abstr_ref                             []
% 15.78/2.49  --abstr_ref_prep                        false
% 15.78/2.49  --abstr_ref_until_sat                   false
% 15.78/2.49  --abstr_ref_sig_restrict                funpre
% 15.78/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.78/2.49  --abstr_ref_under                       []
% 15.78/2.49  
% 15.78/2.49  ------ SAT Options
% 15.78/2.49  
% 15.78/2.49  --sat_mode                              false
% 15.78/2.49  --sat_fm_restart_options                ""
% 15.78/2.49  --sat_gr_def                            false
% 15.78/2.49  --sat_epr_types                         true
% 15.78/2.49  --sat_non_cyclic_types                  false
% 15.78/2.49  --sat_finite_models                     false
% 15.78/2.49  --sat_fm_lemmas                         false
% 15.78/2.49  --sat_fm_prep                           false
% 15.78/2.49  --sat_fm_uc_incr                        true
% 15.78/2.49  --sat_out_model                         small
% 15.78/2.49  --sat_out_clauses                       false
% 15.78/2.49  
% 15.78/2.49  ------ QBF Options
% 15.78/2.49  
% 15.78/2.49  --qbf_mode                              false
% 15.78/2.49  --qbf_elim_univ                         false
% 15.78/2.49  --qbf_dom_inst                          none
% 15.78/2.49  --qbf_dom_pre_inst                      false
% 15.78/2.49  --qbf_sk_in                             false
% 15.78/2.49  --qbf_pred_elim                         true
% 15.78/2.49  --qbf_split                             512
% 15.78/2.49  
% 15.78/2.49  ------ BMC1 Options
% 15.78/2.49  
% 15.78/2.49  --bmc1_incremental                      false
% 15.78/2.49  --bmc1_axioms                           reachable_all
% 15.78/2.49  --bmc1_min_bound                        0
% 15.78/2.49  --bmc1_max_bound                        -1
% 15.78/2.49  --bmc1_max_bound_default                -1
% 15.78/2.49  --bmc1_symbol_reachability              true
% 15.78/2.49  --bmc1_property_lemmas                  false
% 15.78/2.49  --bmc1_k_induction                      false
% 15.78/2.49  --bmc1_non_equiv_states                 false
% 15.78/2.49  --bmc1_deadlock                         false
% 15.78/2.49  --bmc1_ucm                              false
% 15.78/2.49  --bmc1_add_unsat_core                   none
% 15.78/2.49  --bmc1_unsat_core_children              false
% 15.78/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.78/2.49  --bmc1_out_stat                         full
% 15.78/2.49  --bmc1_ground_init                      false
% 15.78/2.49  --bmc1_pre_inst_next_state              false
% 15.78/2.49  --bmc1_pre_inst_state                   false
% 15.78/2.49  --bmc1_pre_inst_reach_state             false
% 15.78/2.49  --bmc1_out_unsat_core                   false
% 15.78/2.49  --bmc1_aig_witness_out                  false
% 15.78/2.49  --bmc1_verbose                          false
% 15.78/2.49  --bmc1_dump_clauses_tptp                false
% 15.78/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.78/2.49  --bmc1_dump_file                        -
% 15.78/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.78/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.78/2.49  --bmc1_ucm_extend_mode                  1
% 15.78/2.49  --bmc1_ucm_init_mode                    2
% 15.78/2.49  --bmc1_ucm_cone_mode                    none
% 15.78/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.78/2.49  --bmc1_ucm_relax_model                  4
% 15.78/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.78/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.78/2.49  --bmc1_ucm_layered_model                none
% 15.78/2.49  --bmc1_ucm_max_lemma_size               10
% 15.78/2.49  
% 15.78/2.49  ------ AIG Options
% 15.78/2.49  
% 15.78/2.49  --aig_mode                              false
% 15.78/2.49  
% 15.78/2.49  ------ Instantiation Options
% 15.78/2.49  
% 15.78/2.49  --instantiation_flag                    true
% 15.78/2.49  --inst_sos_flag                         true
% 15.78/2.49  --inst_sos_phase                        true
% 15.78/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel_side                     num_symb
% 15.78/2.49  --inst_solver_per_active                1400
% 15.78/2.49  --inst_solver_calls_frac                1.
% 15.78/2.49  --inst_passive_queue_type               priority_queues
% 15.78/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.78/2.49  --inst_passive_queues_freq              [25;2]
% 15.78/2.49  --inst_dismatching                      true
% 15.78/2.49  --inst_eager_unprocessed_to_passive     true
% 15.78/2.49  --inst_prop_sim_given                   true
% 15.78/2.49  --inst_prop_sim_new                     false
% 15.78/2.49  --inst_subs_new                         false
% 15.78/2.49  --inst_eq_res_simp                      false
% 15.78/2.49  --inst_subs_given                       false
% 15.78/2.49  --inst_orphan_elimination               true
% 15.78/2.49  --inst_learning_loop_flag               true
% 15.78/2.49  --inst_learning_start                   3000
% 15.78/2.49  --inst_learning_factor                  2
% 15.78/2.49  --inst_start_prop_sim_after_learn       3
% 15.78/2.49  --inst_sel_renew                        solver
% 15.78/2.49  --inst_lit_activity_flag                true
% 15.78/2.49  --inst_restr_to_given                   false
% 15.78/2.49  --inst_activity_threshold               500
% 15.78/2.49  --inst_out_proof                        true
% 15.78/2.49  
% 15.78/2.49  ------ Resolution Options
% 15.78/2.49  
% 15.78/2.49  --resolution_flag                       true
% 15.78/2.49  --res_lit_sel                           adaptive
% 15.78/2.49  --res_lit_sel_side                      none
% 15.78/2.49  --res_ordering                          kbo
% 15.78/2.49  --res_to_prop_solver                    active
% 15.78/2.49  --res_prop_simpl_new                    false
% 15.78/2.49  --res_prop_simpl_given                  true
% 15.78/2.49  --res_passive_queue_type                priority_queues
% 15.78/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.78/2.49  --res_passive_queues_freq               [15;5]
% 15.78/2.49  --res_forward_subs                      full
% 15.78/2.49  --res_backward_subs                     full
% 15.78/2.49  --res_forward_subs_resolution           true
% 15.78/2.49  --res_backward_subs_resolution          true
% 15.78/2.49  --res_orphan_elimination                true
% 15.78/2.49  --res_time_limit                        2.
% 15.78/2.49  --res_out_proof                         true
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Options
% 15.78/2.49  
% 15.78/2.49  --superposition_flag                    true
% 15.78/2.49  --sup_passive_queue_type                priority_queues
% 15.78/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.78/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.78/2.49  --demod_completeness_check              fast
% 15.78/2.49  --demod_use_ground                      true
% 15.78/2.49  --sup_to_prop_solver                    passive
% 15.78/2.49  --sup_prop_simpl_new                    true
% 15.78/2.49  --sup_prop_simpl_given                  true
% 15.78/2.49  --sup_fun_splitting                     true
% 15.78/2.49  --sup_smt_interval                      50000
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Simplification Setup
% 15.78/2.49  
% 15.78/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.78/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.78/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_immed_triv                        [TrivRules]
% 15.78/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_bw_main                     []
% 15.78/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.78/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_input_bw                          []
% 15.78/2.49  
% 15.78/2.49  ------ Combination Options
% 15.78/2.49  
% 15.78/2.49  --comb_res_mult                         3
% 15.78/2.49  --comb_sup_mult                         2
% 15.78/2.49  --comb_inst_mult                        10
% 15.78/2.49  
% 15.78/2.49  ------ Debug Options
% 15.78/2.49  
% 15.78/2.49  --dbg_backtrace                         false
% 15.78/2.49  --dbg_dump_prop_clauses                 false
% 15.78/2.49  --dbg_dump_prop_clauses_file            -
% 15.78/2.49  --dbg_out_stat                          false
% 15.78/2.49  ------ Parsing...
% 15.78/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.78/2.49  ------ Proving...
% 15.78/2.49  ------ Problem Properties 
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  clauses                                 17
% 15.78/2.49  conjectures                             2
% 15.78/2.49  EPR                                     2
% 15.78/2.49  Horn                                    17
% 15.78/2.49  unary                                   5
% 15.78/2.49  binary                                  10
% 15.78/2.49  lits                                    32
% 15.78/2.49  lits eq                                 8
% 15.78/2.49  fd_pure                                 0
% 15.78/2.49  fd_pseudo                               0
% 15.78/2.49  fd_cond                                 0
% 15.78/2.49  fd_pseudo_cond                          1
% 15.78/2.49  AC symbols                              0
% 15.78/2.49  
% 15.78/2.49  ------ Schedule dynamic 5 is on 
% 15.78/2.49  
% 15.78/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  ------ 
% 15.78/2.49  Current options:
% 15.78/2.49  ------ 
% 15.78/2.49  
% 15.78/2.49  ------ Input Options
% 15.78/2.49  
% 15.78/2.49  --out_options                           all
% 15.78/2.49  --tptp_safe_out                         true
% 15.78/2.49  --problem_path                          ""
% 15.78/2.49  --include_path                          ""
% 15.78/2.49  --clausifier                            res/vclausify_rel
% 15.78/2.49  --clausifier_options                    ""
% 15.78/2.49  --stdin                                 false
% 15.78/2.49  --stats_out                             all
% 15.78/2.49  
% 15.78/2.49  ------ General Options
% 15.78/2.49  
% 15.78/2.49  --fof                                   false
% 15.78/2.49  --time_out_real                         305.
% 15.78/2.49  --time_out_virtual                      -1.
% 15.78/2.49  --symbol_type_check                     false
% 15.78/2.49  --clausify_out                          false
% 15.78/2.49  --sig_cnt_out                           false
% 15.78/2.49  --trig_cnt_out                          false
% 15.78/2.49  --trig_cnt_out_tolerance                1.
% 15.78/2.49  --trig_cnt_out_sk_spl                   false
% 15.78/2.49  --abstr_cl_out                          false
% 15.78/2.49  
% 15.78/2.49  ------ Global Options
% 15.78/2.49  
% 15.78/2.49  --schedule                              default
% 15.78/2.49  --add_important_lit                     false
% 15.78/2.49  --prop_solver_per_cl                    1000
% 15.78/2.49  --min_unsat_core                        false
% 15.78/2.49  --soft_assumptions                      false
% 15.78/2.49  --soft_lemma_size                       3
% 15.78/2.49  --prop_impl_unit_size                   0
% 15.78/2.49  --prop_impl_unit                        []
% 15.78/2.49  --share_sel_clauses                     true
% 15.78/2.49  --reset_solvers                         false
% 15.78/2.49  --bc_imp_inh                            [conj_cone]
% 15.78/2.49  --conj_cone_tolerance                   3.
% 15.78/2.49  --extra_neg_conj                        none
% 15.78/2.49  --large_theory_mode                     true
% 15.78/2.49  --prolific_symb_bound                   200
% 15.78/2.49  --lt_threshold                          2000
% 15.78/2.49  --clause_weak_htbl                      true
% 15.78/2.49  --gc_record_bc_elim                     false
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing Options
% 15.78/2.49  
% 15.78/2.49  --preprocessing_flag                    true
% 15.78/2.49  --time_out_prep_mult                    0.1
% 15.78/2.49  --splitting_mode                        input
% 15.78/2.49  --splitting_grd                         true
% 15.78/2.49  --splitting_cvd                         false
% 15.78/2.49  --splitting_cvd_svl                     false
% 15.78/2.49  --splitting_nvd                         32
% 15.78/2.49  --sub_typing                            true
% 15.78/2.49  --prep_gs_sim                           true
% 15.78/2.49  --prep_unflatten                        true
% 15.78/2.49  --prep_res_sim                          true
% 15.78/2.49  --prep_upred                            true
% 15.78/2.49  --prep_sem_filter                       exhaustive
% 15.78/2.49  --prep_sem_filter_out                   false
% 15.78/2.49  --pred_elim                             true
% 15.78/2.49  --res_sim_input                         true
% 15.78/2.49  --eq_ax_congr_red                       true
% 15.78/2.49  --pure_diseq_elim                       true
% 15.78/2.49  --brand_transform                       false
% 15.78/2.49  --non_eq_to_eq                          false
% 15.78/2.49  --prep_def_merge                        true
% 15.78/2.49  --prep_def_merge_prop_impl              false
% 15.78/2.49  --prep_def_merge_mbd                    true
% 15.78/2.49  --prep_def_merge_tr_red                 false
% 15.78/2.49  --prep_def_merge_tr_cl                  false
% 15.78/2.49  --smt_preprocessing                     true
% 15.78/2.49  --smt_ac_axioms                         fast
% 15.78/2.49  --preprocessed_out                      false
% 15.78/2.49  --preprocessed_stats                    false
% 15.78/2.49  
% 15.78/2.49  ------ Abstraction refinement Options
% 15.78/2.49  
% 15.78/2.49  --abstr_ref                             []
% 15.78/2.49  --abstr_ref_prep                        false
% 15.78/2.49  --abstr_ref_until_sat                   false
% 15.78/2.49  --abstr_ref_sig_restrict                funpre
% 15.78/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.78/2.49  --abstr_ref_under                       []
% 15.78/2.49  
% 15.78/2.49  ------ SAT Options
% 15.78/2.49  
% 15.78/2.49  --sat_mode                              false
% 15.78/2.49  --sat_fm_restart_options                ""
% 15.78/2.49  --sat_gr_def                            false
% 15.78/2.49  --sat_epr_types                         true
% 15.78/2.49  --sat_non_cyclic_types                  false
% 15.78/2.49  --sat_finite_models                     false
% 15.78/2.49  --sat_fm_lemmas                         false
% 15.78/2.49  --sat_fm_prep                           false
% 15.78/2.49  --sat_fm_uc_incr                        true
% 15.78/2.49  --sat_out_model                         small
% 15.78/2.49  --sat_out_clauses                       false
% 15.78/2.49  
% 15.78/2.49  ------ QBF Options
% 15.78/2.49  
% 15.78/2.49  --qbf_mode                              false
% 15.78/2.49  --qbf_elim_univ                         false
% 15.78/2.49  --qbf_dom_inst                          none
% 15.78/2.49  --qbf_dom_pre_inst                      false
% 15.78/2.49  --qbf_sk_in                             false
% 15.78/2.49  --qbf_pred_elim                         true
% 15.78/2.49  --qbf_split                             512
% 15.78/2.49  
% 15.78/2.49  ------ BMC1 Options
% 15.78/2.49  
% 15.78/2.49  --bmc1_incremental                      false
% 15.78/2.49  --bmc1_axioms                           reachable_all
% 15.78/2.49  --bmc1_min_bound                        0
% 15.78/2.49  --bmc1_max_bound                        -1
% 15.78/2.49  --bmc1_max_bound_default                -1
% 15.78/2.49  --bmc1_symbol_reachability              true
% 15.78/2.49  --bmc1_property_lemmas                  false
% 15.78/2.49  --bmc1_k_induction                      false
% 15.78/2.49  --bmc1_non_equiv_states                 false
% 15.78/2.49  --bmc1_deadlock                         false
% 15.78/2.49  --bmc1_ucm                              false
% 15.78/2.49  --bmc1_add_unsat_core                   none
% 15.78/2.49  --bmc1_unsat_core_children              false
% 15.78/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.78/2.49  --bmc1_out_stat                         full
% 15.78/2.49  --bmc1_ground_init                      false
% 15.78/2.49  --bmc1_pre_inst_next_state              false
% 15.78/2.49  --bmc1_pre_inst_state                   false
% 15.78/2.49  --bmc1_pre_inst_reach_state             false
% 15.78/2.49  --bmc1_out_unsat_core                   false
% 15.78/2.49  --bmc1_aig_witness_out                  false
% 15.78/2.49  --bmc1_verbose                          false
% 15.78/2.49  --bmc1_dump_clauses_tptp                false
% 15.78/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.78/2.49  --bmc1_dump_file                        -
% 15.78/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.78/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.78/2.49  --bmc1_ucm_extend_mode                  1
% 15.78/2.49  --bmc1_ucm_init_mode                    2
% 15.78/2.49  --bmc1_ucm_cone_mode                    none
% 15.78/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.78/2.49  --bmc1_ucm_relax_model                  4
% 15.78/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.78/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.78/2.49  --bmc1_ucm_layered_model                none
% 15.78/2.49  --bmc1_ucm_max_lemma_size               10
% 15.78/2.49  
% 15.78/2.49  ------ AIG Options
% 15.78/2.49  
% 15.78/2.49  --aig_mode                              false
% 15.78/2.49  
% 15.78/2.49  ------ Instantiation Options
% 15.78/2.49  
% 15.78/2.49  --instantiation_flag                    true
% 15.78/2.49  --inst_sos_flag                         true
% 15.78/2.49  --inst_sos_phase                        true
% 15.78/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel_side                     none
% 15.78/2.49  --inst_solver_per_active                1400
% 15.78/2.49  --inst_solver_calls_frac                1.
% 15.78/2.49  --inst_passive_queue_type               priority_queues
% 15.78/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.78/2.49  --inst_passive_queues_freq              [25;2]
% 15.78/2.49  --inst_dismatching                      true
% 15.78/2.49  --inst_eager_unprocessed_to_passive     true
% 15.78/2.49  --inst_prop_sim_given                   true
% 15.78/2.49  --inst_prop_sim_new                     false
% 15.78/2.49  --inst_subs_new                         false
% 15.78/2.49  --inst_eq_res_simp                      false
% 15.78/2.49  --inst_subs_given                       false
% 15.78/2.49  --inst_orphan_elimination               true
% 15.78/2.49  --inst_learning_loop_flag               true
% 15.78/2.49  --inst_learning_start                   3000
% 15.78/2.49  --inst_learning_factor                  2
% 15.78/2.49  --inst_start_prop_sim_after_learn       3
% 15.78/2.49  --inst_sel_renew                        solver
% 15.78/2.49  --inst_lit_activity_flag                true
% 15.78/2.49  --inst_restr_to_given                   false
% 15.78/2.49  --inst_activity_threshold               500
% 15.78/2.49  --inst_out_proof                        true
% 15.78/2.49  
% 15.78/2.49  ------ Resolution Options
% 15.78/2.49  
% 15.78/2.49  --resolution_flag                       false
% 15.78/2.49  --res_lit_sel                           adaptive
% 15.78/2.49  --res_lit_sel_side                      none
% 15.78/2.49  --res_ordering                          kbo
% 15.78/2.49  --res_to_prop_solver                    active
% 15.78/2.49  --res_prop_simpl_new                    false
% 15.78/2.49  --res_prop_simpl_given                  true
% 15.78/2.49  --res_passive_queue_type                priority_queues
% 15.78/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.78/2.49  --res_passive_queues_freq               [15;5]
% 15.78/2.49  --res_forward_subs                      full
% 15.78/2.49  --res_backward_subs                     full
% 15.78/2.49  --res_forward_subs_resolution           true
% 15.78/2.49  --res_backward_subs_resolution          true
% 15.78/2.49  --res_orphan_elimination                true
% 15.78/2.49  --res_time_limit                        2.
% 15.78/2.49  --res_out_proof                         true
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Options
% 15.78/2.49  
% 15.78/2.49  --superposition_flag                    true
% 15.78/2.49  --sup_passive_queue_type                priority_queues
% 15.78/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.78/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.78/2.49  --demod_completeness_check              fast
% 15.78/2.49  --demod_use_ground                      true
% 15.78/2.49  --sup_to_prop_solver                    passive
% 15.78/2.49  --sup_prop_simpl_new                    true
% 15.78/2.49  --sup_prop_simpl_given                  true
% 15.78/2.49  --sup_fun_splitting                     true
% 15.78/2.49  --sup_smt_interval                      50000
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Simplification Setup
% 15.78/2.49  
% 15.78/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.78/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.78/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_immed_triv                        [TrivRules]
% 15.78/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_bw_main                     []
% 15.78/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.78/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_input_bw                          []
% 15.78/2.49  
% 15.78/2.49  ------ Combination Options
% 15.78/2.49  
% 15.78/2.49  --comb_res_mult                         3
% 15.78/2.49  --comb_sup_mult                         2
% 15.78/2.49  --comb_inst_mult                        10
% 15.78/2.49  
% 15.78/2.49  ------ Debug Options
% 15.78/2.49  
% 15.78/2.49  --dbg_backtrace                         false
% 15.78/2.49  --dbg_dump_prop_clauses                 false
% 15.78/2.49  --dbg_dump_prop_clauses_file            -
% 15.78/2.49  --dbg_out_stat                          false
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  ------ Proving...
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  % SZS status Theorem for theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  fof(f5,axiom,(
% 15.78/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f23,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(ennf_transformation,[],[f5])).
% 15.78/2.49  
% 15.78/2.49  fof(f47,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(nnf_transformation,[],[f23])).
% 15.78/2.49  
% 15.78/2.49  fof(f48,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f47])).
% 15.78/2.49  
% 15.78/2.49  fof(f59,plain,(
% 15.78/2.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f48])).
% 15.78/2.49  
% 15.78/2.49  fof(f16,conjecture,(
% 15.78/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f17,negated_conjecture,(
% 15.78/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 15.78/2.49    inference(negated_conjecture,[],[f16])).
% 15.78/2.49  
% 15.78/2.49  fof(f43,plain,(
% 15.78/2.49    ? [X0] : (? [X1] : ((k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f17])).
% 15.78/2.49  
% 15.78/2.49  fof(f44,plain,(
% 15.78/2.49    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f43])).
% 15.78/2.49  
% 15.78/2.49  fof(f51,plain,(
% 15.78/2.49    ( ! [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.78/2.49    introduced(choice_axiom,[])).
% 15.78/2.49  
% 15.78/2.49  fof(f50,plain,(
% 15.78/2.49    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0 & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 15.78/2.49    introduced(choice_axiom,[])).
% 15.78/2.49  
% 15.78/2.49  fof(f52,plain,(
% 15.78/2.49    (k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 15.78/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f51,f50])).
% 15.78/2.49  
% 15.78/2.49  fof(f76,plain,(
% 15.78/2.49    v4_tops_1(sK1,sK0)),
% 15.78/2.49    inference(cnf_transformation,[],[f52])).
% 15.78/2.49  
% 15.78/2.49  fof(f74,plain,(
% 15.78/2.49    l1_pre_topc(sK0)),
% 15.78/2.49    inference(cnf_transformation,[],[f52])).
% 15.78/2.49  
% 15.78/2.49  fof(f75,plain,(
% 15.78/2.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.78/2.49    inference(cnf_transformation,[],[f52])).
% 15.78/2.49  
% 15.78/2.49  fof(f2,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f18,plain,(
% 15.78/2.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f2])).
% 15.78/2.49  
% 15.78/2.49  fof(f19,plain,(
% 15.78/2.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f18])).
% 15.78/2.49  
% 15.78/2.49  fof(f56,plain,(
% 15.78/2.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f19])).
% 15.78/2.49  
% 15.78/2.49  fof(f12,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f35,plain,(
% 15.78/2.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f12])).
% 15.78/2.49  
% 15.78/2.49  fof(f36,plain,(
% 15.78/2.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f35])).
% 15.78/2.49  
% 15.78/2.49  fof(f68,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f36])).
% 15.78/2.49  
% 15.78/2.49  fof(f13,axiom,(
% 15.78/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f37,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(ennf_transformation,[],[f13])).
% 15.78/2.49  
% 15.78/2.49  fof(f38,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f37])).
% 15.78/2.49  
% 15.78/2.49  fof(f69,plain,(
% 15.78/2.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f38])).
% 15.78/2.49  
% 15.78/2.49  fof(f6,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f24,plain,(
% 15.78/2.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f6])).
% 15.78/2.49  
% 15.78/2.49  fof(f25,plain,(
% 15.78/2.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f24])).
% 15.78/2.49  
% 15.78/2.49  fof(f62,plain,(
% 15.78/2.49    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f25])).
% 15.78/2.49  
% 15.78/2.49  fof(f1,axiom,(
% 15.78/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f45,plain,(
% 15.78/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.78/2.49    inference(nnf_transformation,[],[f1])).
% 15.78/2.49  
% 15.78/2.49  fof(f46,plain,(
% 15.78/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.78/2.49    inference(flattening,[],[f45])).
% 15.78/2.49  
% 15.78/2.49  fof(f55,plain,(
% 15.78/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f46])).
% 15.78/2.49  
% 15.78/2.49  fof(f4,axiom,(
% 15.78/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f22,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(ennf_transformation,[],[f4])).
% 15.78/2.49  
% 15.78/2.49  fof(f58,plain,(
% 15.78/2.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f22])).
% 15.78/2.49  
% 15.78/2.49  fof(f10,axiom,(
% 15.78/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f32,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(ennf_transformation,[],[f10])).
% 15.78/2.49  
% 15.78/2.49  fof(f66,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f32])).
% 15.78/2.49  
% 15.78/2.49  fof(f3,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f20,plain,(
% 15.78/2.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f3])).
% 15.78/2.49  
% 15.78/2.49  fof(f21,plain,(
% 15.78/2.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f20])).
% 15.78/2.49  
% 15.78/2.49  fof(f57,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f21])).
% 15.78/2.49  
% 15.78/2.49  fof(f11,axiom,(
% 15.78/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f33,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f11])).
% 15.78/2.49  
% 15.78/2.49  fof(f34,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f33])).
% 15.78/2.49  
% 15.78/2.49  fof(f67,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f34])).
% 15.78/2.49  
% 15.78/2.49  fof(f73,plain,(
% 15.78/2.49    v2_pre_topc(sK0)),
% 15.78/2.49    inference(cnf_transformation,[],[f52])).
% 15.78/2.49  
% 15.78/2.49  fof(f7,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f26,plain,(
% 15.78/2.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f7])).
% 15.78/2.49  
% 15.78/2.49  fof(f27,plain,(
% 15.78/2.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f26])).
% 15.78/2.49  
% 15.78/2.49  fof(f63,plain,(
% 15.78/2.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f27])).
% 15.78/2.49  
% 15.78/2.49  fof(f14,axiom,(
% 15.78/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f39,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(ennf_transformation,[],[f14])).
% 15.78/2.49  
% 15.78/2.49  fof(f40,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f39])).
% 15.78/2.49  
% 15.78/2.49  fof(f49,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | k2_tops_1(X0,X1) != X1) & (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0))) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.78/2.49    inference(nnf_transformation,[],[f40])).
% 15.78/2.49  
% 15.78/2.49  fof(f70,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f49])).
% 15.78/2.49  
% 15.78/2.49  fof(f15,axiom,(
% 15.78/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f41,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f15])).
% 15.78/2.49  
% 15.78/2.49  fof(f42,plain,(
% 15.78/2.49    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f41])).
% 15.78/2.49  
% 15.78/2.49  fof(f72,plain,(
% 15.78/2.49    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f42])).
% 15.78/2.49  
% 15.78/2.49  fof(f8,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f28,plain,(
% 15.78/2.49    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f8])).
% 15.78/2.49  
% 15.78/2.49  fof(f29,plain,(
% 15.78/2.49    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f28])).
% 15.78/2.49  
% 15.78/2.49  fof(f64,plain,(
% 15.78/2.49    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f29])).
% 15.78/2.49  
% 15.78/2.49  fof(f9,axiom,(
% 15.78/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 15.78/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f30,plain,(
% 15.78/2.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.78/2.49    inference(ennf_transformation,[],[f9])).
% 15.78/2.49  
% 15.78/2.49  fof(f31,plain,(
% 15.78/2.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.78/2.49    inference(flattening,[],[f30])).
% 15.78/2.49  
% 15.78/2.49  fof(f65,plain,(
% 15.78/2.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f31])).
% 15.78/2.49  
% 15.78/2.49  fof(f77,plain,(
% 15.78/2.49    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0),
% 15.78/2.49    inference(cnf_transformation,[],[f52])).
% 15.78/2.49  
% 15.78/2.49  cnf(c_8,plain,
% 15.78/2.49      ( ~ v4_tops_1(X0,X1)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 15.78/2.49      | ~ l1_pre_topc(X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_21,negated_conjecture,
% 15.78/2.49      ( v4_tops_1(sK1,sK0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_431,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | sK1 != X0
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_432,plain,
% 15.78/2.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 15.78/2.49      | ~ l1_pre_topc(sK0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_431]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_23,negated_conjecture,
% 15.78/2.49      ( l1_pre_topc(sK0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_22,negated_conjecture,
% 15.78/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_434,plain,
% 15.78/2.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_432,c_23,c_22]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1046,plain,
% 15.78/2.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1048,plain,
% 15.78/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_547,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_548,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_547]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1037,plain,
% 15.78/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_15,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_475,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_476,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_475]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1043,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2033,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1037,c_1043]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3760,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1048,c_2033]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_16,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ r1_tarski(X0,X2)
% 15.78/2.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 15.78/2.49      | ~ l1_pre_topc(X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_457,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ r1_tarski(X0,X2)
% 15.78/2.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_458,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ r1_tarski(X0,X1)
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_457]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1044,plain,
% 15.78/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3807,plain,
% 15.78/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_3760,c_1044]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_27,plain,
% 15.78/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1102,plain,
% 15.78/2.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(instantiation,[status(thm)],[c_548]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1103,plain,
% 15.78/2.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.78/2.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_1102]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_9,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_511,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_512,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_511]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1234,plain,
% 15.78/2.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(instantiation,[status(thm)],[c_512]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1241,plain,
% 15.78/2.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.78/2.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_1234]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_15013,plain,
% 15.78/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_3807,c_27,c_1103,c_1241]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_0,plain,
% 15.78/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.78/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1050,plain,
% 15.78/2.49      ( X0 = X1
% 15.78/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.78/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3015,plain,
% 15.78/2.49      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 15.78/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(X1,X0) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) != iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1044,c_1050]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_15055,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_15013,c_3015]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50251,plain,
% 15.78/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 15.78/2.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_15055,c_27,c_1103]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50252,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 15.78/2.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 15.78/2.49      inference(renaming,[status(thm)],[c_50251]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50258,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 15.78/2.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1046,c_50252]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_5,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 15.78/2.49      | ~ l1_pre_topc(X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_523,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_524,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_523]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1110,plain,
% 15.78/2.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 15.78/2.49      inference(instantiation,[status(thm)],[c_524]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1111,plain,
% 15.78/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.78/2.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50279,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_50258,c_27,c_1111]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_13,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_487,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_488,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_487]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1042,plain,
% 15.78/2.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2276,plain,
% 15.78/2.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1037,c_1042]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4786,plain,
% 15.78/2.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1048,c_2276]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_535,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_536,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_535]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1038,plain,
% 15.78/2.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1454,plain,
% 15.78/2.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1048,c_1038]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4792,plain,
% 15.78/2.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_4786,c_1454]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50339,plain,
% 15.78/2.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_50279,c_4792]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2274,plain,
% 15.78/2.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1048,c_1042]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50344,plain,
% 15.78/2.49      ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_50339,c_2274]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_14,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ v2_pre_topc(X1)
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_24,negated_conjecture,
% 15.78/2.49      ( v2_pre_topc(sK0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_324,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_325,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ l1_pre_topc(sK0)
% 15.78/2.49      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_324]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_329,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_325,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1047,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2155,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1037,c_1047]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3317,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1048,c_2155]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_10,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_499,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_500,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_499]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_18,plain,
% 15.78/2.49      ( ~ v3_tops_1(X0,X1)
% 15.78/2.49      | ~ v4_pre_topc(X0,X1)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k2_tops_1(X1,X0) = X0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_19,plain,
% 15.78/2.49      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 15.78/2.49      | ~ v4_pre_topc(X1,X0)
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.78/2.49      | ~ v2_pre_topc(X0)
% 15.78/2.49      | ~ l1_pre_topc(X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_267,plain,
% 15.78/2.49      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 15.78/2.49      | ~ v4_pre_topc(X1,X0)
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.78/2.49      | ~ l1_pre_topc(X0)
% 15.78/2.49      | sK0 != X0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_268,plain,
% 15.78/2.49      ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
% 15.78/2.49      | ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ l1_pre_topc(sK0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_267]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_272,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | v3_tops_1(k2_tops_1(sK0,X0),sK0) ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_268,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_273,plain,
% 15.78/2.49      ( v3_tops_1(k2_tops_1(sK0,X0),sK0)
% 15.78/2.49      | ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(renaming,[status(thm)],[c_272]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_356,plain,
% 15.78/2.49      ( ~ v4_pre_topc(X0,X1)
% 15.78/2.49      | ~ v4_pre_topc(X2,sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.78/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ l1_pre_topc(X1)
% 15.78/2.49      | k2_tops_1(X1,X0) = X0
% 15.78/2.49      | k2_tops_1(sK0,X2) != X0
% 15.78/2.49      | sK0 != X1 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_18,c_273]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_357,plain,
% 15.78/2.49      ( ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | ~ v4_pre_topc(k2_tops_1(sK0,X0),sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ l1_pre_topc(sK0)
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_356]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_11,plain,
% 15.78/2.49      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.78/2.49      | ~ v2_pre_topc(X0)
% 15.78/2.49      | ~ l1_pre_topc(X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_306,plain,
% 15.78/2.49      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.78/2.49      | ~ l1_pre_topc(X0)
% 15.78/2.49      | sK0 != X0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_307,plain,
% 15.78/2.49      ( v4_pre_topc(k2_tops_1(sK0,X0),sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ l1_pre_topc(sK0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_306]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_361,plain,
% 15.78/2.49      ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_357,c_23,c_307]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_362,plain,
% 15.78/2.49      ( ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.78/2.49      inference(renaming,[status(thm)],[c_361]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_572,plain,
% 15.78/2.49      ( ~ v4_pre_topc(X0,sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.78/2.49      inference(backward_subsumption_resolution,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_500,c_362]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_12,plain,
% 15.78/2.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.78/2.49      | ~ v2_pre_topc(X0)
% 15.78/2.49      | ~ l1_pre_topc(X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_288,plain,
% 15.78/2.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.78/2.49      | ~ l1_pre_topc(X0)
% 15.78/2.49      | sK0 != X0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_289,plain,
% 15.78/2.49      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ l1_pre_topc(sK0) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_288]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_293,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_289,c_23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_294,plain,
% 15.78/2.49      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 15.78/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.78/2.49      inference(renaming,[status(thm)],[c_293]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_589,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
% 15.78/2.49      | k2_pre_topc(sK0,X0) != X1
% 15.78/2.49      | sK0 != sK0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_572,c_294]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_590,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_589]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_594,plain,
% 15.78/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.78/2.49      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 15.78/2.49      inference(global_propositional_subsumption,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_590,c_548]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1036,plain,
% 15.78/2.49      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 15.78/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.78/2.49      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2401,plain,
% 15.78/2.49      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1048,c_1036]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3321,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_3317,c_2401]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_50443,plain,
% 15.78/2.49      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_50344,c_3321]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_20,negated_conjecture,
% 15.78/2.49      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f77]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(contradiction,plain,
% 15.78/2.49      ( $false ),
% 15.78/2.49      inference(minisat,[status(thm)],[c_50443,c_20]) ).
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  ------                               Statistics
% 15.78/2.49  
% 15.78/2.49  ------ General
% 15.78/2.49  
% 15.78/2.49  abstr_ref_over_cycles:                  0
% 15.78/2.49  abstr_ref_under_cycles:                 0
% 15.78/2.49  gc_basic_clause_elim:                   0
% 15.78/2.49  forced_gc_time:                         0
% 15.78/2.49  parsing_time:                           0.009
% 15.78/2.49  unif_index_cands_time:                  0.
% 15.78/2.49  unif_index_add_time:                    0.
% 15.78/2.49  orderings_time:                         0.
% 15.78/2.49  out_proof_time:                         0.017
% 15.78/2.49  total_time:                             1.671
% 15.78/2.49  num_of_symbols:                         47
% 15.78/2.49  num_of_terms:                           69816
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing
% 15.78/2.49  
% 15.78/2.49  num_of_splits:                          0
% 15.78/2.49  num_of_split_atoms:                     0
% 15.78/2.49  num_of_reused_defs:                     0
% 15.78/2.49  num_eq_ax_congr_red:                    3
% 15.78/2.49  num_of_sem_filtered_clauses:            1
% 15.78/2.49  num_of_subtypes:                        0
% 15.78/2.49  monotx_restored_types:                  0
% 15.78/2.49  sat_num_of_epr_types:                   0
% 15.78/2.49  sat_num_of_non_cyclic_types:            0
% 15.78/2.49  sat_guarded_non_collapsed_types:        0
% 15.78/2.49  num_pure_diseq_elim:                    0
% 15.78/2.49  simp_replaced_by:                       0
% 15.78/2.49  res_preprocessed:                       96
% 15.78/2.49  prep_upred:                             0
% 15.78/2.49  prep_unflattend:                        22
% 15.78/2.49  smt_new_axioms:                         0
% 15.78/2.49  pred_elim_cands:                        2
% 15.78/2.49  pred_elim:                              5
% 15.78/2.49  pred_elim_cl:                           7
% 15.78/2.49  pred_elim_cycles:                       8
% 15.78/2.49  merged_defs:                            0
% 15.78/2.49  merged_defs_ncl:                        0
% 15.78/2.49  bin_hyper_res:                          0
% 15.78/2.49  prep_cycles:                            4
% 15.78/2.49  pred_elim_time:                         0.007
% 15.78/2.49  splitting_time:                         0.
% 15.78/2.49  sem_filter_time:                        0.
% 15.78/2.49  monotx_time:                            0.
% 15.78/2.49  subtype_inf_time:                       0.
% 15.78/2.49  
% 15.78/2.49  ------ Problem properties
% 15.78/2.49  
% 15.78/2.49  clauses:                                17
% 15.78/2.49  conjectures:                            2
% 15.78/2.49  epr:                                    2
% 15.78/2.49  horn:                                   17
% 15.78/2.49  ground:                                 4
% 15.78/2.49  unary:                                  5
% 15.78/2.49  binary:                                 10
% 15.78/2.49  lits:                                   32
% 15.78/2.49  lits_eq:                                8
% 15.78/2.49  fd_pure:                                0
% 15.78/2.49  fd_pseudo:                              0
% 15.78/2.49  fd_cond:                                0
% 15.78/2.49  fd_pseudo_cond:                         1
% 15.78/2.49  ac_symbols:                             0
% 15.78/2.49  
% 15.78/2.49  ------ Propositional Solver
% 15.78/2.49  
% 15.78/2.49  prop_solver_calls:                      41
% 15.78/2.49  prop_fast_solver_calls:                 2616
% 15.78/2.49  smt_solver_calls:                       0
% 15.78/2.49  smt_fast_solver_calls:                  0
% 15.78/2.49  prop_num_of_clauses:                    18677
% 15.78/2.49  prop_preprocess_simplified:             23535
% 15.78/2.49  prop_fo_subsumed:                       197
% 15.78/2.49  prop_solver_time:                       0.
% 15.78/2.49  smt_solver_time:                        0.
% 15.78/2.49  smt_fast_solver_time:                   0.
% 15.78/2.49  prop_fast_solver_time:                  0.
% 15.78/2.49  prop_unsat_core_time:                   0.001
% 15.78/2.49  
% 15.78/2.49  ------ QBF
% 15.78/2.49  
% 15.78/2.49  qbf_q_res:                              0
% 15.78/2.49  qbf_num_tautologies:                    0
% 15.78/2.49  qbf_prep_cycles:                        0
% 15.78/2.49  
% 15.78/2.49  ------ BMC1
% 15.78/2.49  
% 15.78/2.49  bmc1_current_bound:                     -1
% 15.78/2.49  bmc1_last_solved_bound:                 -1
% 15.78/2.49  bmc1_unsat_core_size:                   -1
% 15.78/2.49  bmc1_unsat_core_parents_size:           -1
% 15.78/2.49  bmc1_merge_next_fun:                    0
% 15.78/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.78/2.49  
% 15.78/2.49  ------ Instantiation
% 15.78/2.49  
% 15.78/2.49  inst_num_of_clauses:                    547
% 15.78/2.49  inst_num_in_passive:                    157
% 15.78/2.49  inst_num_in_active:                     3278
% 15.78/2.49  inst_num_in_unprocessed:                8
% 15.78/2.49  inst_num_of_loops:                      3389
% 15.78/2.49  inst_num_of_learning_restarts:          1
% 15.78/2.49  inst_num_moves_active_passive:          106
% 15.78/2.49  inst_lit_activity:                      0
% 15.78/2.49  inst_lit_activity_moves:                3
% 15.78/2.49  inst_num_tautologies:                   0
% 15.78/2.49  inst_num_prop_implied:                  0
% 15.78/2.49  inst_num_existing_simplified:           0
% 15.78/2.49  inst_num_eq_res_simplified:             0
% 15.78/2.49  inst_num_child_elim:                    0
% 15.78/2.49  inst_num_of_dismatching_blockings:      15139
% 15.78/2.49  inst_num_of_non_proper_insts:           4969
% 15.78/2.49  inst_num_of_duplicates:                 0
% 15.78/2.49  inst_inst_num_from_inst_to_res:         0
% 15.78/2.49  inst_dismatching_checking_time:         0.
% 15.78/2.49  
% 15.78/2.49  ------ Resolution
% 15.78/2.49  
% 15.78/2.49  res_num_of_clauses:                     27
% 15.78/2.49  res_num_in_passive:                     27
% 15.78/2.49  res_num_in_active:                      0
% 15.78/2.49  res_num_of_loops:                       100
% 15.78/2.49  res_forward_subset_subsumed:            523
% 15.78/2.49  res_backward_subset_subsumed:           6
% 15.78/2.49  res_forward_subsumed:                   0
% 15.78/2.49  res_backward_subsumed:                  0
% 15.78/2.49  res_forward_subsumption_resolution:     0
% 15.78/2.49  res_backward_subsumption_resolution:    1
% 15.78/2.49  res_clause_to_clause_subsumption:       16733
% 15.78/2.49  res_orphan_elimination:                 0
% 15.78/2.49  res_tautology_del:                      176
% 15.78/2.49  res_num_eq_res_simplified:              0
% 15.78/2.49  res_num_sel_changes:                    0
% 15.78/2.49  res_moves_from_active_to_pass:          0
% 15.78/2.49  
% 15.78/2.49  ------ Superposition
% 15.78/2.49  
% 15.78/2.49  sup_time_total:                         0.
% 15.78/2.49  sup_time_generating:                    0.
% 15.78/2.49  sup_time_sim_full:                      0.
% 15.78/2.49  sup_time_sim_immed:                     0.
% 15.78/2.49  
% 15.78/2.49  sup_num_of_clauses:                     2659
% 15.78/2.49  sup_num_in_active:                      570
% 15.78/2.49  sup_num_in_passive:                     2089
% 15.78/2.49  sup_num_of_loops:                       677
% 15.78/2.49  sup_fw_superposition:                   2739
% 15.78/2.49  sup_bw_superposition:                   2322
% 15.78/2.49  sup_immediate_simplified:               2513
% 15.78/2.49  sup_given_eliminated:                   0
% 15.78/2.49  comparisons_done:                       0
% 15.78/2.49  comparisons_avoided:                    0
% 15.78/2.49  
% 15.78/2.49  ------ Simplifications
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  sim_fw_subset_subsumed:                 402
% 15.78/2.49  sim_bw_subset_subsumed:                 190
% 15.78/2.49  sim_fw_subsumed:                        432
% 15.78/2.49  sim_bw_subsumed:                        3
% 15.78/2.49  sim_fw_subsumption_res:                 0
% 15.78/2.49  sim_bw_subsumption_res:                 0
% 15.78/2.49  sim_tautology_del:                      310
% 15.78/2.49  sim_eq_tautology_del:                   642
% 15.78/2.49  sim_eq_res_simp:                        0
% 15.78/2.49  sim_fw_demodulated:                     70
% 15.78/2.49  sim_bw_demodulated:                     106
% 15.78/2.49  sim_light_normalised:                   1862
% 15.78/2.49  sim_joinable_taut:                      0
% 15.78/2.49  sim_joinable_simp:                      0
% 15.78/2.49  sim_ac_normalised:                      0
% 15.78/2.49  sim_smt_subsumption:                    0
% 15.78/2.49  
%------------------------------------------------------------------------------
