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
% DateTime   : Thu Dec  3 12:15:24 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 792 expanded)
%              Number of clauses        :   91 ( 215 expanded)
%              Number of leaves         :   20 ( 175 expanded)
%              Depth                    :   22
%              Number of atoms          :  465 (3894 expanded)
%              Number of equality atoms :  169 (1050 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_840,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_844,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1592,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_840,c_844])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1597,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1592,c_3])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_842,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1332,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_840,c_842])).

cnf(c_1852,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1597,c_1332])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_839,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_319,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_406,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_319,c_24])).

cnf(c_407,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_857,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_839,c_407])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_837,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_896,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_837,c_407])).

cnf(c_995,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_857,c_896])).

cnf(c_21,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_191,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_18,plain,
    ( ~ v3_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_378,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = k2_struct_0(X3)
    | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_379,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_393,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_379,c_5])).

cnf(c_411,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_24])).

cnf(c_412,plain,
    ( ~ v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = sK1
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_412])).

cnf(c_486,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = sK1
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_488,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_23])).

cnf(c_860,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_488,c_407])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_80,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_79,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_81,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_84,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_333,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_334,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_336,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_24,c_23])).

cnf(c_360,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_336])).

cnf(c_361,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_363,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v3_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_24,c_23])).

cnf(c_364,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_364,c_412])).

cnf(c_472,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_474,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_23])).

cnf(c_835,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_891,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_835,c_407])).

cnf(c_601,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_977,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_978,plain,
    ( k2_tops_1(sK0,sK1) != X0
    | sK1 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_980,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_1104,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_80,c_84,c_461,c_979])).

cnf(c_1399,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_995,c_1104])).

cnf(c_1991,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1852,c_1399])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_838,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_901,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_838,c_407])).

cnf(c_999,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_857,c_901])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_350,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_24,c_23])).

cnf(c_1000,plain,
    ( k7_subset_1(k2_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_999,c_350])).

cnf(c_2303,plain,
    ( k7_subset_1(k2_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1991,c_1000])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_841,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1868,plain,
    ( k7_subset_1(k2_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_857,c_841])).

cnf(c_2305,plain,
    ( k2_tops_1(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2303,c_3,c_1868])).

cnf(c_20,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_189,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_461,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(resolution,[status(thm)],[c_364,c_189])).

cnf(c_836,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_979,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_1197,plain,
    ( k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_80,c_84,c_461,c_979])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2305,c_1197])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:45:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.84/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/0.97  
% 2.84/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/0.97  
% 2.84/0.97  ------  iProver source info
% 2.84/0.97  
% 2.84/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.84/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/0.97  git: non_committed_changes: false
% 2.84/0.97  git: last_make_outside_of_git: false
% 2.84/0.97  
% 2.84/0.97  ------ 
% 2.84/0.97  
% 2.84/0.97  ------ Input Options
% 2.84/0.97  
% 2.84/0.97  --out_options                           all
% 2.84/0.97  --tptp_safe_out                         true
% 2.84/0.97  --problem_path                          ""
% 2.84/0.97  --include_path                          ""
% 2.84/0.97  --clausifier                            res/vclausify_rel
% 2.84/0.97  --clausifier_options                    --mode clausify
% 2.84/0.97  --stdin                                 false
% 2.84/0.97  --stats_out                             all
% 2.84/0.97  
% 2.84/0.97  ------ General Options
% 2.84/0.97  
% 2.84/0.97  --fof                                   false
% 2.84/0.97  --time_out_real                         305.
% 2.84/0.97  --time_out_virtual                      -1.
% 2.84/0.97  --symbol_type_check                     false
% 2.84/0.97  --clausify_out                          false
% 2.84/0.97  --sig_cnt_out                           false
% 2.84/0.97  --trig_cnt_out                          false
% 2.84/0.97  --trig_cnt_out_tolerance                1.
% 2.84/0.97  --trig_cnt_out_sk_spl                   false
% 2.84/0.97  --abstr_cl_out                          false
% 2.84/0.97  
% 2.84/0.97  ------ Global Options
% 2.84/0.97  
% 2.84/0.97  --schedule                              default
% 2.84/0.97  --add_important_lit                     false
% 2.84/0.97  --prop_solver_per_cl                    1000
% 2.84/0.97  --min_unsat_core                        false
% 2.84/0.97  --soft_assumptions                      false
% 2.84/0.97  --soft_lemma_size                       3
% 2.84/0.97  --prop_impl_unit_size                   0
% 2.84/0.97  --prop_impl_unit                        []
% 2.84/0.97  --share_sel_clauses                     true
% 2.84/0.97  --reset_solvers                         false
% 2.84/0.97  --bc_imp_inh                            [conj_cone]
% 2.84/0.97  --conj_cone_tolerance                   3.
% 2.84/0.97  --extra_neg_conj                        none
% 2.84/0.97  --large_theory_mode                     true
% 2.84/0.97  --prolific_symb_bound                   200
% 2.84/0.97  --lt_threshold                          2000
% 2.84/0.97  --clause_weak_htbl                      true
% 2.84/0.97  --gc_record_bc_elim                     false
% 2.84/0.97  
% 2.84/0.97  ------ Preprocessing Options
% 2.84/0.97  
% 2.84/0.97  --preprocessing_flag                    true
% 2.84/0.97  --time_out_prep_mult                    0.1
% 2.84/0.97  --splitting_mode                        input
% 2.84/0.97  --splitting_grd                         true
% 2.84/0.97  --splitting_cvd                         false
% 2.84/0.97  --splitting_cvd_svl                     false
% 2.84/0.97  --splitting_nvd                         32
% 2.84/0.97  --sub_typing                            true
% 2.84/0.97  --prep_gs_sim                           true
% 2.84/0.97  --prep_unflatten                        true
% 2.84/0.97  --prep_res_sim                          true
% 2.84/0.97  --prep_upred                            true
% 2.84/0.97  --prep_sem_filter                       exhaustive
% 2.84/0.97  --prep_sem_filter_out                   false
% 2.84/0.97  --pred_elim                             true
% 2.84/0.97  --res_sim_input                         true
% 2.84/0.97  --eq_ax_congr_red                       true
% 2.84/0.97  --pure_diseq_elim                       true
% 2.84/0.97  --brand_transform                       false
% 2.84/0.97  --non_eq_to_eq                          false
% 2.84/0.97  --prep_def_merge                        true
% 2.84/0.97  --prep_def_merge_prop_impl              false
% 2.84/0.97  --prep_def_merge_mbd                    true
% 2.84/0.97  --prep_def_merge_tr_red                 false
% 2.84/0.97  --prep_def_merge_tr_cl                  false
% 2.84/0.97  --smt_preprocessing                     true
% 2.84/0.97  --smt_ac_axioms                         fast
% 2.84/0.97  --preprocessed_out                      false
% 2.84/0.97  --preprocessed_stats                    false
% 2.84/0.97  
% 2.84/0.97  ------ Abstraction refinement Options
% 2.84/0.97  
% 2.84/0.97  --abstr_ref                             []
% 2.84/0.97  --abstr_ref_prep                        false
% 2.84/0.97  --abstr_ref_until_sat                   false
% 2.84/0.97  --abstr_ref_sig_restrict                funpre
% 2.84/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.97  --abstr_ref_under                       []
% 2.84/0.97  
% 2.84/0.97  ------ SAT Options
% 2.84/0.97  
% 2.84/0.97  --sat_mode                              false
% 2.84/0.97  --sat_fm_restart_options                ""
% 2.84/0.97  --sat_gr_def                            false
% 2.84/0.97  --sat_epr_types                         true
% 2.84/0.97  --sat_non_cyclic_types                  false
% 2.84/0.97  --sat_finite_models                     false
% 2.84/0.97  --sat_fm_lemmas                         false
% 2.84/0.97  --sat_fm_prep                           false
% 2.84/0.97  --sat_fm_uc_incr                        true
% 2.84/0.97  --sat_out_model                         small
% 2.84/0.97  --sat_out_clauses                       false
% 2.84/0.97  
% 2.84/0.97  ------ QBF Options
% 2.84/0.97  
% 2.84/0.97  --qbf_mode                              false
% 2.84/0.97  --qbf_elim_univ                         false
% 2.84/0.97  --qbf_dom_inst                          none
% 2.84/0.97  --qbf_dom_pre_inst                      false
% 2.84/0.97  --qbf_sk_in                             false
% 2.84/0.97  --qbf_pred_elim                         true
% 2.84/0.97  --qbf_split                             512
% 2.84/0.97  
% 2.84/0.97  ------ BMC1 Options
% 2.84/0.97  
% 2.84/0.97  --bmc1_incremental                      false
% 2.84/0.97  --bmc1_axioms                           reachable_all
% 2.84/0.97  --bmc1_min_bound                        0
% 2.84/0.97  --bmc1_max_bound                        -1
% 2.84/0.97  --bmc1_max_bound_default                -1
% 2.84/0.97  --bmc1_symbol_reachability              true
% 2.84/0.97  --bmc1_property_lemmas                  false
% 2.84/0.97  --bmc1_k_induction                      false
% 2.84/0.97  --bmc1_non_equiv_states                 false
% 2.84/0.97  --bmc1_deadlock                         false
% 2.84/0.97  --bmc1_ucm                              false
% 2.84/0.97  --bmc1_add_unsat_core                   none
% 2.84/0.97  --bmc1_unsat_core_children              false
% 2.84/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.97  --bmc1_out_stat                         full
% 2.84/0.97  --bmc1_ground_init                      false
% 2.84/0.97  --bmc1_pre_inst_next_state              false
% 2.84/0.97  --bmc1_pre_inst_state                   false
% 2.84/0.97  --bmc1_pre_inst_reach_state             false
% 2.84/0.97  --bmc1_out_unsat_core                   false
% 2.84/0.97  --bmc1_aig_witness_out                  false
% 2.84/0.97  --bmc1_verbose                          false
% 2.84/0.97  --bmc1_dump_clauses_tptp                false
% 2.84/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.97  --bmc1_dump_file                        -
% 2.84/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.97  --bmc1_ucm_extend_mode                  1
% 2.84/0.97  --bmc1_ucm_init_mode                    2
% 2.84/0.97  --bmc1_ucm_cone_mode                    none
% 2.84/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.97  --bmc1_ucm_relax_model                  4
% 2.84/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.97  --bmc1_ucm_layered_model                none
% 2.84/0.97  --bmc1_ucm_max_lemma_size               10
% 2.84/0.97  
% 2.84/0.97  ------ AIG Options
% 2.84/0.97  
% 2.84/0.97  --aig_mode                              false
% 2.84/0.97  
% 2.84/0.97  ------ Instantiation Options
% 2.84/0.97  
% 2.84/0.97  --instantiation_flag                    true
% 2.84/0.97  --inst_sos_flag                         false
% 2.84/0.97  --inst_sos_phase                        true
% 2.84/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.97  --inst_lit_sel_side                     num_symb
% 2.84/0.97  --inst_solver_per_active                1400
% 2.84/0.97  --inst_solver_calls_frac                1.
% 2.84/0.97  --inst_passive_queue_type               priority_queues
% 2.84/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.97  --inst_passive_queues_freq              [25;2]
% 2.84/0.97  --inst_dismatching                      true
% 2.84/0.97  --inst_eager_unprocessed_to_passive     true
% 2.84/0.97  --inst_prop_sim_given                   true
% 2.84/0.97  --inst_prop_sim_new                     false
% 2.84/0.97  --inst_subs_new                         false
% 2.84/0.97  --inst_eq_res_simp                      false
% 2.84/0.97  --inst_subs_given                       false
% 2.84/0.97  --inst_orphan_elimination               true
% 2.84/0.97  --inst_learning_loop_flag               true
% 2.84/0.97  --inst_learning_start                   3000
% 2.84/0.97  --inst_learning_factor                  2
% 2.84/0.97  --inst_start_prop_sim_after_learn       3
% 2.84/0.97  --inst_sel_renew                        solver
% 2.84/0.97  --inst_lit_activity_flag                true
% 2.84/0.97  --inst_restr_to_given                   false
% 2.84/0.97  --inst_activity_threshold               500
% 2.84/0.97  --inst_out_proof                        true
% 2.84/0.97  
% 2.84/0.97  ------ Resolution Options
% 2.84/0.97  
% 2.84/0.97  --resolution_flag                       true
% 2.84/0.97  --res_lit_sel                           adaptive
% 2.84/0.97  --res_lit_sel_side                      none
% 2.84/0.97  --res_ordering                          kbo
% 2.84/0.97  --res_to_prop_solver                    active
% 2.84/0.97  --res_prop_simpl_new                    false
% 2.84/0.97  --res_prop_simpl_given                  true
% 2.84/0.97  --res_passive_queue_type                priority_queues
% 2.84/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.97  --res_passive_queues_freq               [15;5]
% 2.84/0.97  --res_forward_subs                      full
% 2.84/0.97  --res_backward_subs                     full
% 2.84/0.97  --res_forward_subs_resolution           true
% 2.84/0.97  --res_backward_subs_resolution          true
% 2.84/0.97  --res_orphan_elimination                true
% 2.84/0.97  --res_time_limit                        2.
% 2.84/0.97  --res_out_proof                         true
% 2.84/0.97  
% 2.84/0.97  ------ Superposition Options
% 2.84/0.97  
% 2.84/0.97  --superposition_flag                    true
% 2.84/0.97  --sup_passive_queue_type                priority_queues
% 2.84/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.97  --demod_completeness_check              fast
% 2.84/0.97  --demod_use_ground                      true
% 2.84/0.97  --sup_to_prop_solver                    passive
% 2.84/0.97  --sup_prop_simpl_new                    true
% 2.84/0.97  --sup_prop_simpl_given                  true
% 2.84/0.97  --sup_fun_splitting                     false
% 2.84/0.97  --sup_smt_interval                      50000
% 2.84/0.97  
% 2.84/0.97  ------ Superposition Simplification Setup
% 2.84/0.97  
% 2.84/0.97  --sup_indices_passive                   []
% 2.84/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.97  --sup_full_bw                           [BwDemod]
% 2.84/0.97  --sup_immed_triv                        [TrivRules]
% 2.84/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.97  --sup_immed_bw_main                     []
% 2.84/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.97  
% 2.84/0.97  ------ Combination Options
% 2.84/0.97  
% 2.84/0.97  --comb_res_mult                         3
% 2.84/0.97  --comb_sup_mult                         2
% 2.84/0.97  --comb_inst_mult                        10
% 2.84/0.97  
% 2.84/0.97  ------ Debug Options
% 2.84/0.97  
% 2.84/0.97  --dbg_backtrace                         false
% 2.84/0.97  --dbg_dump_prop_clauses                 false
% 2.84/0.97  --dbg_dump_prop_clauses_file            -
% 2.84/0.97  --dbg_out_stat                          false
% 2.84/0.97  ------ Parsing...
% 2.84/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/0.97  
% 2.84/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.84/0.97  
% 2.84/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/0.97  
% 2.84/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/0.97  ------ Proving...
% 2.84/0.97  ------ Problem Properties 
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  clauses                                 16
% 2.84/0.97  conjectures                             1
% 2.84/0.97  EPR                                     2
% 2.84/0.97  Horn                                    15
% 2.84/0.97  unary                                   6
% 2.84/0.97  binary                                  9
% 2.84/0.97  lits                                    27
% 2.84/0.97  lits eq                                 13
% 2.84/0.97  fd_pure                                 0
% 2.84/0.97  fd_pseudo                               0
% 2.84/0.97  fd_cond                                 0
% 2.84/0.97  fd_pseudo_cond                          1
% 2.84/0.97  AC symbols                              0
% 2.84/0.97  
% 2.84/0.97  ------ Schedule dynamic 5 is on 
% 2.84/0.97  
% 2.84/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  ------ 
% 2.84/0.97  Current options:
% 2.84/0.97  ------ 
% 2.84/0.97  
% 2.84/0.97  ------ Input Options
% 2.84/0.97  
% 2.84/0.97  --out_options                           all
% 2.84/0.97  --tptp_safe_out                         true
% 2.84/0.97  --problem_path                          ""
% 2.84/0.97  --include_path                          ""
% 2.84/0.97  --clausifier                            res/vclausify_rel
% 2.84/0.97  --clausifier_options                    --mode clausify
% 2.84/0.97  --stdin                                 false
% 2.84/0.97  --stats_out                             all
% 2.84/0.97  
% 2.84/0.97  ------ General Options
% 2.84/0.97  
% 2.84/0.97  --fof                                   false
% 2.84/0.97  --time_out_real                         305.
% 2.84/0.97  --time_out_virtual                      -1.
% 2.84/0.97  --symbol_type_check                     false
% 2.84/0.97  --clausify_out                          false
% 2.84/0.97  --sig_cnt_out                           false
% 2.84/0.97  --trig_cnt_out                          false
% 2.84/0.97  --trig_cnt_out_tolerance                1.
% 2.84/0.97  --trig_cnt_out_sk_spl                   false
% 2.84/0.97  --abstr_cl_out                          false
% 2.84/0.97  
% 2.84/0.97  ------ Global Options
% 2.84/0.97  
% 2.84/0.97  --schedule                              default
% 2.84/0.97  --add_important_lit                     false
% 2.84/0.97  --prop_solver_per_cl                    1000
% 2.84/0.97  --min_unsat_core                        false
% 2.84/0.97  --soft_assumptions                      false
% 2.84/0.97  --soft_lemma_size                       3
% 2.84/0.97  --prop_impl_unit_size                   0
% 2.84/0.97  --prop_impl_unit                        []
% 2.84/0.97  --share_sel_clauses                     true
% 2.84/0.97  --reset_solvers                         false
% 2.84/0.97  --bc_imp_inh                            [conj_cone]
% 2.84/0.97  --conj_cone_tolerance                   3.
% 2.84/0.97  --extra_neg_conj                        none
% 2.84/0.97  --large_theory_mode                     true
% 2.84/0.97  --prolific_symb_bound                   200
% 2.84/0.97  --lt_threshold                          2000
% 2.84/0.97  --clause_weak_htbl                      true
% 2.84/0.97  --gc_record_bc_elim                     false
% 2.84/0.97  
% 2.84/0.97  ------ Preprocessing Options
% 2.84/0.97  
% 2.84/0.97  --preprocessing_flag                    true
% 2.84/0.97  --time_out_prep_mult                    0.1
% 2.84/0.97  --splitting_mode                        input
% 2.84/0.97  --splitting_grd                         true
% 2.84/0.97  --splitting_cvd                         false
% 2.84/0.97  --splitting_cvd_svl                     false
% 2.84/0.97  --splitting_nvd                         32
% 2.84/0.97  --sub_typing                            true
% 2.84/0.97  --prep_gs_sim                           true
% 2.84/0.97  --prep_unflatten                        true
% 2.84/0.97  --prep_res_sim                          true
% 2.84/0.97  --prep_upred                            true
% 2.84/0.97  --prep_sem_filter                       exhaustive
% 2.84/0.97  --prep_sem_filter_out                   false
% 2.84/0.97  --pred_elim                             true
% 2.84/0.97  --res_sim_input                         true
% 2.84/0.97  --eq_ax_congr_red                       true
% 2.84/0.97  --pure_diseq_elim                       true
% 2.84/0.97  --brand_transform                       false
% 2.84/0.97  --non_eq_to_eq                          false
% 2.84/0.97  --prep_def_merge                        true
% 2.84/0.97  --prep_def_merge_prop_impl              false
% 2.84/0.97  --prep_def_merge_mbd                    true
% 2.84/0.97  --prep_def_merge_tr_red                 false
% 2.84/0.97  --prep_def_merge_tr_cl                  false
% 2.84/0.97  --smt_preprocessing                     true
% 2.84/0.97  --smt_ac_axioms                         fast
% 2.84/0.97  --preprocessed_out                      false
% 2.84/0.97  --preprocessed_stats                    false
% 2.84/0.97  
% 2.84/0.97  ------ Abstraction refinement Options
% 2.84/0.97  
% 2.84/0.97  --abstr_ref                             []
% 2.84/0.97  --abstr_ref_prep                        false
% 2.84/0.97  --abstr_ref_until_sat                   false
% 2.84/0.97  --abstr_ref_sig_restrict                funpre
% 2.84/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.97  --abstr_ref_under                       []
% 2.84/0.97  
% 2.84/0.97  ------ SAT Options
% 2.84/0.97  
% 2.84/0.97  --sat_mode                              false
% 2.84/0.97  --sat_fm_restart_options                ""
% 2.84/0.97  --sat_gr_def                            false
% 2.84/0.97  --sat_epr_types                         true
% 2.84/0.97  --sat_non_cyclic_types                  false
% 2.84/0.97  --sat_finite_models                     false
% 2.84/0.97  --sat_fm_lemmas                         false
% 2.84/0.97  --sat_fm_prep                           false
% 2.84/0.97  --sat_fm_uc_incr                        true
% 2.84/0.97  --sat_out_model                         small
% 2.84/0.97  --sat_out_clauses                       false
% 2.84/0.97  
% 2.84/0.97  ------ QBF Options
% 2.84/0.97  
% 2.84/0.97  --qbf_mode                              false
% 2.84/0.97  --qbf_elim_univ                         false
% 2.84/0.97  --qbf_dom_inst                          none
% 2.84/0.97  --qbf_dom_pre_inst                      false
% 2.84/0.97  --qbf_sk_in                             false
% 2.84/0.97  --qbf_pred_elim                         true
% 2.84/0.97  --qbf_split                             512
% 2.84/0.97  
% 2.84/0.97  ------ BMC1 Options
% 2.84/0.97  
% 2.84/0.97  --bmc1_incremental                      false
% 2.84/0.97  --bmc1_axioms                           reachable_all
% 2.84/0.97  --bmc1_min_bound                        0
% 2.84/0.97  --bmc1_max_bound                        -1
% 2.84/0.97  --bmc1_max_bound_default                -1
% 2.84/0.97  --bmc1_symbol_reachability              true
% 2.84/0.97  --bmc1_property_lemmas                  false
% 2.84/0.97  --bmc1_k_induction                      false
% 2.84/0.97  --bmc1_non_equiv_states                 false
% 2.84/0.97  --bmc1_deadlock                         false
% 2.84/0.97  --bmc1_ucm                              false
% 2.84/0.97  --bmc1_add_unsat_core                   none
% 2.84/0.97  --bmc1_unsat_core_children              false
% 2.84/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.97  --bmc1_out_stat                         full
% 2.84/0.97  --bmc1_ground_init                      false
% 2.84/0.97  --bmc1_pre_inst_next_state              false
% 2.84/0.97  --bmc1_pre_inst_state                   false
% 2.84/0.97  --bmc1_pre_inst_reach_state             false
% 2.84/0.97  --bmc1_out_unsat_core                   false
% 2.84/0.97  --bmc1_aig_witness_out                  false
% 2.84/0.97  --bmc1_verbose                          false
% 2.84/0.97  --bmc1_dump_clauses_tptp                false
% 2.84/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.97  --bmc1_dump_file                        -
% 2.84/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.97  --bmc1_ucm_extend_mode                  1
% 2.84/0.97  --bmc1_ucm_init_mode                    2
% 2.84/0.97  --bmc1_ucm_cone_mode                    none
% 2.84/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.97  --bmc1_ucm_relax_model                  4
% 2.84/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.97  --bmc1_ucm_layered_model                none
% 2.84/0.97  --bmc1_ucm_max_lemma_size               10
% 2.84/0.97  
% 2.84/0.97  ------ AIG Options
% 2.84/0.97  
% 2.84/0.97  --aig_mode                              false
% 2.84/0.97  
% 2.84/0.97  ------ Instantiation Options
% 2.84/0.97  
% 2.84/0.97  --instantiation_flag                    true
% 2.84/0.97  --inst_sos_flag                         false
% 2.84/0.97  --inst_sos_phase                        true
% 2.84/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.97  --inst_lit_sel_side                     none
% 2.84/0.97  --inst_solver_per_active                1400
% 2.84/0.97  --inst_solver_calls_frac                1.
% 2.84/0.97  --inst_passive_queue_type               priority_queues
% 2.84/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.97  --inst_passive_queues_freq              [25;2]
% 2.84/0.97  --inst_dismatching                      true
% 2.84/0.97  --inst_eager_unprocessed_to_passive     true
% 2.84/0.97  --inst_prop_sim_given                   true
% 2.84/0.97  --inst_prop_sim_new                     false
% 2.84/0.97  --inst_subs_new                         false
% 2.84/0.97  --inst_eq_res_simp                      false
% 2.84/0.97  --inst_subs_given                       false
% 2.84/0.97  --inst_orphan_elimination               true
% 2.84/0.97  --inst_learning_loop_flag               true
% 2.84/0.97  --inst_learning_start                   3000
% 2.84/0.97  --inst_learning_factor                  2
% 2.84/0.97  --inst_start_prop_sim_after_learn       3
% 2.84/0.97  --inst_sel_renew                        solver
% 2.84/0.97  --inst_lit_activity_flag                true
% 2.84/0.97  --inst_restr_to_given                   false
% 2.84/0.97  --inst_activity_threshold               500
% 2.84/0.97  --inst_out_proof                        true
% 2.84/0.97  
% 2.84/0.97  ------ Resolution Options
% 2.84/0.97  
% 2.84/0.97  --resolution_flag                       false
% 2.84/0.97  --res_lit_sel                           adaptive
% 2.84/0.97  --res_lit_sel_side                      none
% 2.84/0.97  --res_ordering                          kbo
% 2.84/0.97  --res_to_prop_solver                    active
% 2.84/0.97  --res_prop_simpl_new                    false
% 2.84/0.97  --res_prop_simpl_given                  true
% 2.84/0.97  --res_passive_queue_type                priority_queues
% 2.84/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.97  --res_passive_queues_freq               [15;5]
% 2.84/0.97  --res_forward_subs                      full
% 2.84/0.97  --res_backward_subs                     full
% 2.84/0.97  --res_forward_subs_resolution           true
% 2.84/0.97  --res_backward_subs_resolution          true
% 2.84/0.97  --res_orphan_elimination                true
% 2.84/0.97  --res_time_limit                        2.
% 2.84/0.97  --res_out_proof                         true
% 2.84/0.97  
% 2.84/0.97  ------ Superposition Options
% 2.84/0.97  
% 2.84/0.97  --superposition_flag                    true
% 2.84/0.97  --sup_passive_queue_type                priority_queues
% 2.84/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.97  --demod_completeness_check              fast
% 2.84/0.97  --demod_use_ground                      true
% 2.84/0.97  --sup_to_prop_solver                    passive
% 2.84/0.97  --sup_prop_simpl_new                    true
% 2.84/0.97  --sup_prop_simpl_given                  true
% 2.84/0.97  --sup_fun_splitting                     false
% 2.84/0.97  --sup_smt_interval                      50000
% 2.84/0.97  
% 2.84/0.97  ------ Superposition Simplification Setup
% 2.84/0.97  
% 2.84/0.97  --sup_indices_passive                   []
% 2.84/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.97  --sup_full_bw                           [BwDemod]
% 2.84/0.97  --sup_immed_triv                        [TrivRules]
% 2.84/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.97  --sup_immed_bw_main                     []
% 2.84/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.97  
% 2.84/0.97  ------ Combination Options
% 2.84/0.97  
% 2.84/0.97  --comb_res_mult                         3
% 2.84/0.97  --comb_sup_mult                         2
% 2.84/0.97  --comb_inst_mult                        10
% 2.84/0.97  
% 2.84/0.97  ------ Debug Options
% 2.84/0.97  
% 2.84/0.97  --dbg_backtrace                         false
% 2.84/0.97  --dbg_dump_prop_clauses                 false
% 2.84/0.97  --dbg_dump_prop_clauses_file            -
% 2.84/0.97  --dbg_out_stat                          false
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  ------ Proving...
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  % SZS status Theorem for theBenchmark.p
% 2.84/0.97  
% 2.84/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/0.97  
% 2.84/0.97  fof(f7,axiom,(
% 2.84/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f57,plain,(
% 2.84/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.84/0.97    inference(cnf_transformation,[],[f7])).
% 2.84/0.97  
% 2.84/0.97  fof(f3,axiom,(
% 2.84/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f22,plain,(
% 2.84/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.84/0.97    inference(ennf_transformation,[],[f3])).
% 2.84/0.97  
% 2.84/0.97  fof(f53,plain,(
% 2.84/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.84/0.97    inference(cnf_transformation,[],[f22])).
% 2.84/0.97  
% 2.84/0.97  fof(f2,axiom,(
% 2.84/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f52,plain,(
% 2.84/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.84/0.97    inference(cnf_transformation,[],[f2])).
% 2.84/0.97  
% 2.84/0.97  fof(f5,axiom,(
% 2.84/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f24,plain,(
% 2.84/0.97    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.84/0.97    inference(ennf_transformation,[],[f5])).
% 2.84/0.97  
% 2.84/0.97  fof(f55,plain,(
% 2.84/0.97    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.84/0.97    inference(cnf_transformation,[],[f24])).
% 2.84/0.97  
% 2.84/0.97  fof(f18,conjecture,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f19,negated_conjecture,(
% 2.84/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 2.84/0.97    inference(negated_conjecture,[],[f18])).
% 2.84/0.97  
% 2.84/0.97  fof(f38,plain,(
% 2.84/0.97    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f19])).
% 2.84/0.97  
% 2.84/0.97  fof(f39,plain,(
% 2.84/0.97    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.84/0.97    inference(flattening,[],[f38])).
% 2.84/0.97  
% 2.84/0.97  fof(f44,plain,(
% 2.84/0.97    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.84/0.97    inference(nnf_transformation,[],[f39])).
% 2.84/0.97  
% 2.84/0.97  fof(f45,plain,(
% 2.84/0.97    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.84/0.97    inference(flattening,[],[f44])).
% 2.84/0.97  
% 2.84/0.97  fof(f47,plain,(
% 2.84/0.97    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.84/0.97    introduced(choice_axiom,[])).
% 2.84/0.97  
% 2.84/0.97  fof(f46,plain,(
% 2.84/0.97    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.84/0.97    introduced(choice_axiom,[])).
% 2.84/0.97  
% 2.84/0.97  fof(f48,plain,(
% 2.84/0.97    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.84/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).
% 2.84/0.97  
% 2.84/0.97  fof(f70,plain,(
% 2.84/0.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.84/0.97    inference(cnf_transformation,[],[f48])).
% 2.84/0.97  
% 2.84/0.97  fof(f10,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f27,plain,(
% 2.84/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f10])).
% 2.84/0.97  
% 2.84/0.97  fof(f59,plain,(
% 2.84/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f27])).
% 2.84/0.97  
% 2.84/0.97  fof(f9,axiom,(
% 2.84/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f26,plain,(
% 2.84/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f9])).
% 2.84/0.97  
% 2.84/0.97  fof(f58,plain,(
% 2.84/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f26])).
% 2.84/0.97  
% 2.84/0.97  fof(f69,plain,(
% 2.84/0.97    l1_pre_topc(sK0)),
% 2.84/0.97    inference(cnf_transformation,[],[f48])).
% 2.84/0.97  
% 2.84/0.97  fof(f12,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f30,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f12])).
% 2.84/0.97  
% 2.84/0.97  fof(f61,plain,(
% 2.84/0.97    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f30])).
% 2.84/0.97  
% 2.84/0.97  fof(f72,plain,(
% 2.84/0.97    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 2.84/0.97    inference(cnf_transformation,[],[f48])).
% 2.84/0.97  
% 2.84/0.97  fof(f13,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f31,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f13])).
% 2.84/0.97  
% 2.84/0.97  fof(f42,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(nnf_transformation,[],[f31])).
% 2.84/0.97  
% 2.84/0.97  fof(f62,plain,(
% 2.84/0.97    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f42])).
% 2.84/0.97  
% 2.84/0.97  fof(f16,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f34,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f16])).
% 2.84/0.97  
% 2.84/0.97  fof(f35,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(flattening,[],[f34])).
% 2.84/0.97  
% 2.84/0.97  fof(f67,plain,(
% 2.84/0.97    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f35])).
% 2.84/0.97  
% 2.84/0.97  fof(f4,axiom,(
% 2.84/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f23,plain,(
% 2.84/0.97    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.84/0.97    inference(ennf_transformation,[],[f4])).
% 2.84/0.97  
% 2.84/0.97  fof(f54,plain,(
% 2.84/0.97    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.84/0.97    inference(cnf_transformation,[],[f23])).
% 2.84/0.97  
% 2.84/0.97  fof(f1,axiom,(
% 2.84/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f40,plain,(
% 2.84/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.84/0.97    inference(nnf_transformation,[],[f1])).
% 2.84/0.97  
% 2.84/0.97  fof(f41,plain,(
% 2.84/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.84/0.97    inference(flattening,[],[f40])).
% 2.84/0.97  
% 2.84/0.97  fof(f49,plain,(
% 2.84/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.84/0.97    inference(cnf_transformation,[],[f41])).
% 2.84/0.97  
% 2.84/0.97  fof(f75,plain,(
% 2.84/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.84/0.97    inference(equality_resolution,[],[f49])).
% 2.84/0.97  
% 2.84/0.97  fof(f51,plain,(
% 2.84/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f41])).
% 2.84/0.97  
% 2.84/0.97  fof(f15,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f33,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f15])).
% 2.84/0.97  
% 2.84/0.97  fof(f43,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(nnf_transformation,[],[f33])).
% 2.84/0.97  
% 2.84/0.97  fof(f66,plain,(
% 2.84/0.97    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f43])).
% 2.84/0.97  
% 2.84/0.97  fof(f17,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f36,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f17])).
% 2.84/0.97  
% 2.84/0.97  fof(f37,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(flattening,[],[f36])).
% 2.84/0.97  
% 2.84/0.97  fof(f68,plain,(
% 2.84/0.97    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f37])).
% 2.84/0.97  
% 2.84/0.97  fof(f71,plain,(
% 2.84/0.97    v4_pre_topc(sK1,sK0)),
% 2.84/0.97    inference(cnf_transformation,[],[f48])).
% 2.84/0.97  
% 2.84/0.97  fof(f14,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f32,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f14])).
% 2.84/0.97  
% 2.84/0.97  fof(f64,plain,(
% 2.84/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f32])).
% 2.84/0.97  
% 2.84/0.97  fof(f11,axiom,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f20,plain,(
% 2.84/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 2.84/0.97    inference(pure_predicate_removal,[],[f11])).
% 2.84/0.97  
% 2.84/0.97  fof(f28,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(ennf_transformation,[],[f20])).
% 2.84/0.97  
% 2.84/0.97  fof(f29,plain,(
% 2.84/0.97    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.84/0.97    inference(flattening,[],[f28])).
% 2.84/0.97  
% 2.84/0.97  fof(f60,plain,(
% 2.84/0.97    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.84/0.97    inference(cnf_transformation,[],[f29])).
% 2.84/0.97  
% 2.84/0.97  fof(f6,axiom,(
% 2.84/0.97    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.84/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/0.97  
% 2.84/0.97  fof(f25,plain,(
% 2.84/0.97    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.84/0.97    inference(ennf_transformation,[],[f6])).
% 2.84/0.97  
% 2.84/0.97  fof(f56,plain,(
% 2.84/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.84/0.97    inference(cnf_transformation,[],[f25])).
% 2.84/0.97  
% 2.84/0.97  fof(f73,plain,(
% 2.84/0.97    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 2.84/0.97    inference(cnf_transformation,[],[f48])).
% 2.84/0.97  
% 2.84/0.97  cnf(c_8,plain,
% 2.84/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.84/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_840,plain,
% 2.84/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_4,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.84/0.97      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_844,plain,
% 2.84/0.97      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 2.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1592,plain,
% 2.84/0.97      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.84/0.97      inference(superposition,[status(thm)],[c_840,c_844]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_3,plain,
% 2.84/0.97      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.84/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1597,plain,
% 2.84/0.97      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_1592,c_3]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_6,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.84/0.97      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.84/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_842,plain,
% 2.84/0.97      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1332,plain,
% 2.84/0.97      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.84/0.97      inference(superposition,[status(thm)],[c_840,c_842]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1852,plain,
% 2.84/0.97      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.84/0.97      inference(demodulation,[status(thm)],[c_1597,c_1332]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_23,negated_conjecture,
% 2.84/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.84/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_839,plain,
% 2.84/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_10,plain,
% 2.84/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_9,plain,
% 2.84/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_319,plain,
% 2.84/0.97      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.84/0.97      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_24,negated_conjecture,
% 2.84/0.97      ( l1_pre_topc(sK0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_406,plain,
% 2.84/0.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_319,c_24]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_407,plain,
% 2.84/0.97      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_406]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_857,plain,
% 2.84/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_839,c_407]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_12,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_438,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 2.84/0.97      | sK0 != X1 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_439,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_438]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_837,plain,
% 2.84/0.97      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 2.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_896,plain,
% 2.84/0.97      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 2.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_837,c_407]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_995,plain,
% 2.84/0.97      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 2.84/0.97      inference(superposition,[status(thm)],[c_857,c_896]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_21,negated_conjecture,
% 2.84/0.97      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.84/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_191,plain,
% 2.84/0.97      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 2.84/0.97      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_14,plain,
% 2.84/0.97      ( ~ v1_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 2.84/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_18,plain,
% 2.84/0.97      ( ~ v3_tops_1(X0,X1)
% 2.84/0.97      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1) ),
% 2.84/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_378,plain,
% 2.84/0.97      ( ~ v3_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X3)
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | X1 != X3
% 2.84/0.97      | k2_pre_topc(X3,X2) = k2_struct_0(X3)
% 2.84/0.97      | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_379,plain,
% 2.84/0.97      ( ~ v3_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_378]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_5,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.84/0.97      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.84/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_393,plain,
% 2.84/0.97      ( ~ v3_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 2.84/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_379,c_5]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_411,plain,
% 2.84/0.97      ( ~ v3_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 2.84/0.97      | sK0 != X1 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_393,c_24]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_412,plain,
% 2.84/0.97      ( ~ v3_tops_1(X0,sK0)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_411]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_485,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | k2_tops_1(sK0,sK1) = sK1
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 2.84/0.97      | sK1 != X0
% 2.84/0.97      | sK0 != sK0 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_191,c_412]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_486,plain,
% 2.84/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | k2_tops_1(sK0,sK1) = sK1
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_485]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_488,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) = sK1
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_486,c_23]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_860,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) = sK1
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_488,c_407]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_2,plain,
% 2.84/0.97      ( r1_tarski(X0,X0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_80,plain,
% 2.84/0.97      ( r1_tarski(sK1,sK1) ),
% 2.84/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_79,plain,
% 2.84/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_81,plain,
% 2.84/0.97      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.84/0.97      inference(instantiation,[status(thm)],[c_79]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_0,plain,
% 2.84/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.84/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_84,plain,
% 2.84/0.97      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.84/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_16,plain,
% 2.84/0.97      ( v2_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.84/0.97      | ~ l1_pre_topc(X1) ),
% 2.84/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_19,plain,
% 2.84/0.97      ( v3_tops_1(X0,X1)
% 2.84/0.97      | ~ v2_tops_1(X0,X1)
% 2.84/0.97      | ~ v4_pre_topc(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1) ),
% 2.84/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_22,negated_conjecture,
% 2.84/0.97      ( v4_pre_topc(sK1,sK0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_333,plain,
% 2.84/0.97      ( v3_tops_1(X0,X1)
% 2.84/0.97      | ~ v2_tops_1(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | sK1 != X0
% 2.84/0.97      | sK0 != X1 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_334,plain,
% 2.84/0.97      ( v3_tops_1(sK1,sK0)
% 2.84/0.97      | ~ v2_tops_1(sK1,sK0)
% 2.84/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | ~ l1_pre_topc(sK0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_333]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_336,plain,
% 2.84/0.97      ( v3_tops_1(sK1,sK0) | ~ v2_tops_1(sK1,sK0) ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_334,c_24,c_23]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_360,plain,
% 2.84/0.97      ( v3_tops_1(sK1,sK0)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | sK1 != X0
% 2.84/0.97      | sK0 != X1 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_336]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_361,plain,
% 2.84/0.97      ( v3_tops_1(sK1,sK0)
% 2.84/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.84/0.97      | ~ l1_pre_topc(sK0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_360]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_363,plain,
% 2.84/0.97      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v3_tops_1(sK1,sK0) ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_361,c_24,c_23]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_364,plain,
% 2.84/0.97      ( v3_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 2.84/0.97      inference(renaming,[status(thm)],[c_363]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_471,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 2.84/0.97      | sK1 != X0
% 2.84/0.97      | sK0 != sK0 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_364,c_412]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_472,plain,
% 2.84/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_471]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_474,plain,
% 2.84/0.97      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.84/0.97      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_472,c_23]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_835,plain,
% 2.84/0.97      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 2.84/0.97      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_891,plain,
% 2.84/0.97      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 2.84/0.97      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_835,c_407]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_601,plain,
% 2.84/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.84/0.97      theory(equality) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_977,plain,
% 2.84/0.97      ( ~ r1_tarski(X0,X1)
% 2.84/0.97      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.84/0.97      | k2_tops_1(sK0,sK1) != X1
% 2.84/0.97      | sK1 != X0 ),
% 2.84/0.97      inference(instantiation,[status(thm)],[c_601]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_978,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) != X0
% 2.84/0.97      | sK1 != X1
% 2.84/0.97      | r1_tarski(X1,X0) != iProver_top
% 2.84/0.97      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_980,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) != sK1
% 2.84/0.97      | sK1 != sK1
% 2.84/0.97      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 2.84/0.97      | r1_tarski(sK1,sK1) != iProver_top ),
% 2.84/0.97      inference(instantiation,[status(thm)],[c_978]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1104,plain,
% 2.84/0.97      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_860,c_80,c_84,c_461,c_979]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1399,plain,
% 2.84/0.97      ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_995,c_1104]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1991,plain,
% 2.84/0.97      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.84/0.97      inference(demodulation,[status(thm)],[c_1852,c_1399]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_15,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.84/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_426,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.84/0.97      | sK0 != X1 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_427,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_426]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_838,plain,
% 2.84/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_901,plain,
% 2.84/0.97      ( k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.84/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_838,c_407]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_999,plain,
% 2.84/0.97      ( k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.84/0.97      inference(superposition,[status(thm)],[c_857,c_901]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_11,plain,
% 2.84/0.97      ( ~ v4_pre_topc(X0,X1)
% 2.84/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k2_pre_topc(X1,X0) = X0 ),
% 2.84/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_347,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.97      | ~ l1_pre_topc(X1)
% 2.84/0.97      | k2_pre_topc(X1,X0) = X0
% 2.84/0.97      | sK1 != X0
% 2.84/0.97      | sK0 != X1 ),
% 2.84/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_348,plain,
% 2.84/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.84/0.97      | ~ l1_pre_topc(sK0)
% 2.84/0.97      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.84/0.97      inference(unflattening,[status(thm)],[c_347]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_350,plain,
% 2.84/0.97      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_348,c_24,c_23]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1000,plain,
% 2.84/0.97      ( k7_subset_1(k2_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.84/0.97      inference(light_normalisation,[status(thm)],[c_999,c_350]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_2303,plain,
% 2.84/0.97      ( k7_subset_1(k2_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.84/0.97      inference(demodulation,[status(thm)],[c_1991,c_1000]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_7,plain,
% 2.84/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.84/0.97      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.84/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_841,plain,
% 2.84/0.97      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.84/0.97      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1868,plain,
% 2.84/0.97      ( k7_subset_1(k2_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 2.84/0.97      inference(superposition,[status(thm)],[c_857,c_841]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_2305,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) = sK1 ),
% 2.84/0.97      inference(demodulation,[status(thm)],[c_2303,c_3,c_1868]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_20,negated_conjecture,
% 2.84/0.97      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.84/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_189,plain,
% 2.84/0.97      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.84/0.97      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_461,plain,
% 2.84/0.97      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != sK1 ),
% 2.84/0.97      inference(resolution,[status(thm)],[c_364,c_189]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_836,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) != sK1
% 2.84/0.97      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 2.84/0.97      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_979,plain,
% 2.84/0.97      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 2.84/0.97      | ~ r1_tarski(sK1,sK1)
% 2.84/0.97      | k2_tops_1(sK0,sK1) != sK1
% 2.84/0.97      | sK1 != sK1 ),
% 2.84/0.97      inference(instantiation,[status(thm)],[c_977]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(c_1197,plain,
% 2.84/0.97      ( k2_tops_1(sK0,sK1) != sK1 ),
% 2.84/0.97      inference(global_propositional_subsumption,
% 2.84/0.97                [status(thm)],
% 2.84/0.97                [c_836,c_80,c_84,c_461,c_979]) ).
% 2.84/0.97  
% 2.84/0.97  cnf(contradiction,plain,
% 2.84/0.97      ( $false ),
% 2.84/0.97      inference(minisat,[status(thm)],[c_2305,c_1197]) ).
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/0.97  
% 2.84/0.97  ------                               Statistics
% 2.84/0.97  
% 2.84/0.97  ------ General
% 2.84/0.97  
% 2.84/0.97  abstr_ref_over_cycles:                  0
% 2.84/0.97  abstr_ref_under_cycles:                 0
% 2.84/0.97  gc_basic_clause_elim:                   0
% 2.84/0.97  forced_gc_time:                         0
% 2.84/0.97  parsing_time:                           0.01
% 2.84/0.97  unif_index_cands_time:                  0.
% 2.84/0.97  unif_index_add_time:                    0.
% 2.84/0.97  orderings_time:                         0.
% 2.84/0.97  out_proof_time:                         0.008
% 2.84/0.97  total_time:                             0.107
% 2.84/0.97  num_of_symbols:                         51
% 2.84/0.97  num_of_terms:                           2208
% 2.84/0.97  
% 2.84/0.97  ------ Preprocessing
% 2.84/0.97  
% 2.84/0.97  num_of_splits:                          0
% 2.84/0.97  num_of_split_atoms:                     0
% 2.84/0.97  num_of_reused_defs:                     0
% 2.84/0.97  num_eq_ax_congr_red:                    14
% 2.84/0.97  num_of_sem_filtered_clauses:            1
% 2.84/0.97  num_of_subtypes:                        0
% 2.84/0.97  monotx_restored_types:                  0
% 2.84/0.97  sat_num_of_epr_types:                   0
% 2.84/0.97  sat_num_of_non_cyclic_types:            0
% 2.84/0.97  sat_guarded_non_collapsed_types:        0
% 2.84/0.97  num_pure_diseq_elim:                    0
% 2.84/0.97  simp_replaced_by:                       0
% 2.84/0.97  res_preprocessed:                       99
% 2.84/0.97  prep_upred:                             0
% 2.84/0.97  prep_unflattend:                        14
% 2.84/0.97  smt_new_axioms:                         0
% 2.84/0.97  pred_elim_cands:                        2
% 2.84/0.97  pred_elim:                              6
% 2.84/0.97  pred_elim_cl:                           8
% 2.84/0.97  pred_elim_cycles:                       8
% 2.84/0.97  merged_defs:                            2
% 2.84/0.97  merged_defs_ncl:                        0
% 2.84/0.97  bin_hyper_res:                          2
% 2.84/0.97  prep_cycles:                            4
% 2.84/0.97  pred_elim_time:                         0.003
% 2.84/0.97  splitting_time:                         0.
% 2.84/0.97  sem_filter_time:                        0.
% 2.84/0.97  monotx_time:                            0.
% 2.84/0.97  subtype_inf_time:                       0.
% 2.84/0.97  
% 2.84/0.97  ------ Problem properties
% 2.84/0.97  
% 2.84/0.97  clauses:                                16
% 2.84/0.97  conjectures:                            1
% 2.84/0.97  epr:                                    2
% 2.84/0.97  horn:                                   15
% 2.84/0.97  ground:                                 6
% 2.84/0.97  unary:                                  6
% 2.84/0.97  binary:                                 9
% 2.84/0.97  lits:                                   27
% 2.84/0.97  lits_eq:                                13
% 2.84/0.97  fd_pure:                                0
% 2.84/0.97  fd_pseudo:                              0
% 2.84/0.97  fd_cond:                                0
% 2.84/0.97  fd_pseudo_cond:                         1
% 2.84/0.97  ac_symbols:                             0
% 2.84/0.97  
% 2.84/0.97  ------ Propositional Solver
% 2.84/0.97  
% 2.84/0.97  prop_solver_calls:                      27
% 2.84/0.97  prop_fast_solver_calls:                 515
% 2.84/0.97  smt_solver_calls:                       0
% 2.84/0.97  smt_fast_solver_calls:                  0
% 2.84/0.97  prop_num_of_clauses:                    877
% 2.84/0.97  prop_preprocess_simplified:             3246
% 2.84/0.97  prop_fo_subsumed:                       10
% 2.84/0.97  prop_solver_time:                       0.
% 2.84/0.97  smt_solver_time:                        0.
% 2.84/0.97  smt_fast_solver_time:                   0.
% 2.84/0.97  prop_fast_solver_time:                  0.
% 2.84/0.97  prop_unsat_core_time:                   0.
% 2.84/0.97  
% 2.84/0.97  ------ QBF
% 2.84/0.97  
% 2.84/0.97  qbf_q_res:                              0
% 2.84/0.97  qbf_num_tautologies:                    0
% 2.84/0.97  qbf_prep_cycles:                        0
% 2.84/0.97  
% 2.84/0.97  ------ BMC1
% 2.84/0.97  
% 2.84/0.97  bmc1_current_bound:                     -1
% 2.84/0.97  bmc1_last_solved_bound:                 -1
% 2.84/0.97  bmc1_unsat_core_size:                   -1
% 2.84/0.97  bmc1_unsat_core_parents_size:           -1
% 2.84/0.97  bmc1_merge_next_fun:                    0
% 2.84/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.84/0.97  
% 2.84/0.97  ------ Instantiation
% 2.84/0.97  
% 2.84/0.97  inst_num_of_clauses:                    269
% 2.84/0.97  inst_num_in_passive:                    92
% 2.84/0.97  inst_num_in_active:                     149
% 2.84/0.97  inst_num_in_unprocessed:                28
% 2.84/0.97  inst_num_of_loops:                      160
% 2.84/0.97  inst_num_of_learning_restarts:          0
% 2.84/0.97  inst_num_moves_active_passive:          8
% 2.84/0.97  inst_lit_activity:                      0
% 2.84/0.97  inst_lit_activity_moves:                0
% 2.84/0.97  inst_num_tautologies:                   0
% 2.84/0.97  inst_num_prop_implied:                  0
% 2.84/0.97  inst_num_existing_simplified:           0
% 2.84/0.97  inst_num_eq_res_simplified:             0
% 2.84/0.97  inst_num_child_elim:                    0
% 2.84/0.97  inst_num_of_dismatching_blockings:      69
% 2.84/0.97  inst_num_of_non_proper_insts:           247
% 2.84/0.97  inst_num_of_duplicates:                 0
% 2.84/0.97  inst_inst_num_from_inst_to_res:         0
% 2.84/0.97  inst_dismatching_checking_time:         0.
% 2.84/0.97  
% 2.84/0.97  ------ Resolution
% 2.84/0.97  
% 2.84/0.97  res_num_of_clauses:                     0
% 2.84/0.97  res_num_in_passive:                     0
% 2.84/0.97  res_num_in_active:                      0
% 2.84/0.97  res_num_of_loops:                       103
% 2.84/0.97  res_forward_subset_subsumed:            38
% 2.84/0.97  res_backward_subset_subsumed:           0
% 2.84/0.97  res_forward_subsumed:                   0
% 2.84/0.97  res_backward_subsumed:                  0
% 2.84/0.97  res_forward_subsumption_resolution:     1
% 2.84/0.97  res_backward_subsumption_resolution:    0
% 2.84/0.97  res_clause_to_clause_subsumption:       77
% 2.84/0.97  res_orphan_elimination:                 0
% 2.84/0.97  res_tautology_del:                      22
% 2.84/0.97  res_num_eq_res_simplified:              0
% 2.84/0.97  res_num_sel_changes:                    0
% 2.84/0.97  res_moves_from_active_to_pass:          0
% 2.84/0.97  
% 2.84/0.97  ------ Superposition
% 2.84/0.97  
% 2.84/0.97  sup_time_total:                         0.
% 2.84/0.97  sup_time_generating:                    0.
% 2.84/0.97  sup_time_sim_full:                      0.
% 2.84/0.97  sup_time_sim_immed:                     0.
% 2.84/0.97  
% 2.84/0.97  sup_num_of_clauses:                     41
% 2.84/0.97  sup_num_in_active:                      22
% 2.84/0.97  sup_num_in_passive:                     19
% 2.84/0.97  sup_num_of_loops:                       30
% 2.84/0.97  sup_fw_superposition:                   21
% 2.84/0.97  sup_bw_superposition:                   9
% 2.84/0.97  sup_immediate_simplified:               11
% 2.84/0.97  sup_given_eliminated:                   0
% 2.84/0.97  comparisons_done:                       0
% 2.84/0.97  comparisons_avoided:                    0
% 2.84/0.97  
% 2.84/0.97  ------ Simplifications
% 2.84/0.97  
% 2.84/0.97  
% 2.84/0.97  sim_fw_subset_subsumed:                 2
% 2.84/0.97  sim_bw_subset_subsumed:                 1
% 2.84/0.97  sim_fw_subsumed:                        1
% 2.84/0.97  sim_bw_subsumed:                        0
% 2.84/0.97  sim_fw_subsumption_res:                 0
% 2.84/0.97  sim_bw_subsumption_res:                 0
% 2.84/0.97  sim_tautology_del:                      0
% 2.84/0.97  sim_eq_tautology_del:                   0
% 2.84/0.97  sim_eq_res_simp:                        0
% 2.84/0.97  sim_fw_demodulated:                     3
% 2.84/0.97  sim_bw_demodulated:                     7
% 2.84/0.97  sim_light_normalised:                   11
% 2.84/0.97  sim_joinable_taut:                      0
% 2.84/0.97  sim_joinable_simp:                      0
% 2.84/0.97  sim_ac_normalised:                      0
% 2.84/0.97  sim_smt_subsumption:                    0
% 2.84/0.97  
%------------------------------------------------------------------------------
