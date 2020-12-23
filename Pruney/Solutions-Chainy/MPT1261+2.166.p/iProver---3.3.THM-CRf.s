%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:48 EST 2020

% Result     : Theorem 31.66s
% Output     : CNFRefutation 31.66s
% Verified   : 
% Statistics : Number of formulae       :  149 (1478 expanded)
%              Number of clauses        :   82 ( 395 expanded)
%              Number of leaves         :   19 ( 352 expanded)
%              Depth                    :   21
%              Number of atoms          :  353 (5633 expanded)
%              Number of equality atoms :  177 (2021 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f44,f42,f42])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_655,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_658,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1077,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_658])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_943,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1384,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_18,c_17,c_943])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_664,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_703,plain,
    ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_664,c_6])).

cnf(c_2106,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_655,c_703])).

cnf(c_2532,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1384,c_2106])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_687,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k6_subset_1(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_6])).

cnf(c_1228,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_687])).

cnf(c_3155,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2532,c_1228])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_656,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2520,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2106,c_656])).

cnf(c_6150,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3155,c_2520])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_659,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1927,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_659])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2942,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_21])).

cnf(c_2943,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2942])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_663,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_668,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_698,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_668,c_6])).

cnf(c_2080,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_698])).

cnf(c_9923,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2943,c_2080])).

cnf(c_9926,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9923,c_2532])).

cnf(c_10160,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6150,c_9926])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_666,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1811,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_666])).

cnf(c_9892,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2943,c_1811])).

cnf(c_10027,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6150,c_9892])).

cnf(c_46667,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_10160,c_10027])).

cnf(c_3,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_667,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2081,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_667,c_698])).

cnf(c_2090,plain,
    ( k3_subset_1(X0,k6_subset_1(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2081,c_1228])).

cnf(c_3686,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2532,c_2090])).

cnf(c_46668,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_46667,c_3686])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47374,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_46668,c_1])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_665,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2368,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_665])).

cnf(c_2701,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_2368])).

cnf(c_5555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_21])).

cnf(c_5556,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5555])).

cnf(c_5566,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_655,c_5556])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_660,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3408,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_660])).

cnf(c_938,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3922,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3408,c_18,c_17,c_938])).

cnf(c_5574,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5566,c_3922])).

cnf(c_48663,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_47374,c_5574])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_661,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3455,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_661])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_872,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_873,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_4025,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3455,c_20,c_21,c_22,c_873])).

cnf(c_49085,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_48663,c_4025])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_657,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2521,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2106,c_657])).

cnf(c_6151,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3155,c_2521])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49085,c_46668,c_6151])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:20:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.66/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.66/4.49  
% 31.66/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.66/4.49  
% 31.66/4.49  ------  iProver source info
% 31.66/4.49  
% 31.66/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.66/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.66/4.49  git: non_committed_changes: false
% 31.66/4.49  git: last_make_outside_of_git: false
% 31.66/4.49  
% 31.66/4.49  ------ 
% 31.66/4.49  ------ Parsing...
% 31.66/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.66/4.49  
% 31.66/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.66/4.49  
% 31.66/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.66/4.49  
% 31.66/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.66/4.49  ------ Proving...
% 31.66/4.49  ------ Problem Properties 
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  clauses                                 20
% 31.66/4.49  conjectures                             5
% 31.66/4.49  EPR                                     2
% 31.66/4.49  Horn                                    19
% 31.66/4.49  unary                                   8
% 31.66/4.49  binary                                  6
% 31.66/4.49  lits                                    40
% 31.66/4.49  lits eq                                 12
% 31.66/4.49  fd_pure                                 0
% 31.66/4.49  fd_pseudo                               0
% 31.66/4.49  fd_cond                                 0
% 31.66/4.49  fd_pseudo_cond                          0
% 31.66/4.49  AC symbols                              0
% 31.66/4.49  
% 31.66/4.49  ------ Input Options Time Limit: Unbounded
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  ------ 
% 31.66/4.49  Current options:
% 31.66/4.49  ------ 
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  ------ Proving...
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  % SZS status Theorem for theBenchmark.p
% 31.66/4.49  
% 31.66/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.66/4.49  
% 31.66/4.49  fof(f18,conjecture,(
% 31.66/4.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f19,negated_conjecture,(
% 31.66/4.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 31.66/4.49    inference(negated_conjecture,[],[f18])).
% 31.66/4.49  
% 31.66/4.49  fof(f35,plain,(
% 31.66/4.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 31.66/4.49    inference(ennf_transformation,[],[f19])).
% 31.66/4.49  
% 31.66/4.49  fof(f36,plain,(
% 31.66/4.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.66/4.49    inference(flattening,[],[f35])).
% 31.66/4.49  
% 31.66/4.49  fof(f37,plain,(
% 31.66/4.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.66/4.49    inference(nnf_transformation,[],[f36])).
% 31.66/4.49  
% 31.66/4.49  fof(f38,plain,(
% 31.66/4.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.66/4.49    inference(flattening,[],[f37])).
% 31.66/4.49  
% 31.66/4.49  fof(f40,plain,(
% 31.66/4.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.66/4.49    introduced(choice_axiom,[])).
% 31.66/4.49  
% 31.66/4.49  fof(f39,plain,(
% 31.66/4.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 31.66/4.49    introduced(choice_axiom,[])).
% 31.66/4.49  
% 31.66/4.49  fof(f41,plain,(
% 31.66/4.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 31.66/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 31.66/4.49  
% 31.66/4.49  fof(f61,plain,(
% 31.66/4.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.66/4.49    inference(cnf_transformation,[],[f41])).
% 31.66/4.49  
% 31.66/4.49  fof(f17,axiom,(
% 31.66/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f34,plain,(
% 31.66/4.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.49    inference(ennf_transformation,[],[f17])).
% 31.66/4.49  
% 31.66/4.49  fof(f58,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f34])).
% 31.66/4.49  
% 31.66/4.49  fof(f60,plain,(
% 31.66/4.49    l1_pre_topc(sK0)),
% 31.66/4.49    inference(cnf_transformation,[],[f41])).
% 31.66/4.49  
% 31.66/4.49  fof(f10,axiom,(
% 31.66/4.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f25,plain,(
% 31.66/4.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.66/4.49    inference(ennf_transformation,[],[f10])).
% 31.66/4.49  
% 31.66/4.49  fof(f51,plain,(
% 31.66/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f25])).
% 31.66/4.49  
% 31.66/4.49  fof(f1,axiom,(
% 31.66/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f42,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f1])).
% 31.66/4.49  
% 31.66/4.49  fof(f69,plain,(
% 31.66/4.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(definition_unfolding,[],[f51,f42])).
% 31.66/4.49  
% 31.66/4.49  fof(f9,axiom,(
% 31.66/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f50,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f9])).
% 31.66/4.49  
% 31.66/4.49  fof(f68,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 31.66/4.49    inference(definition_unfolding,[],[f50,f42])).
% 31.66/4.49  
% 31.66/4.49  fof(f3,axiom,(
% 31.66/4.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f44,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f3])).
% 31.66/4.49  
% 31.66/4.49  fof(f64,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 31.66/4.49    inference(definition_unfolding,[],[f44,f42,f42])).
% 31.66/4.49  
% 31.66/4.49  fof(f62,plain,(
% 31.66/4.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 31.66/4.49    inference(cnf_transformation,[],[f41])).
% 31.66/4.49  
% 31.66/4.49  fof(f16,axiom,(
% 31.66/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f32,plain,(
% 31.66/4.49    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.49    inference(ennf_transformation,[],[f16])).
% 31.66/4.49  
% 31.66/4.49  fof(f33,plain,(
% 31.66/4.49    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.49    inference(flattening,[],[f32])).
% 31.66/4.49  
% 31.66/4.49  fof(f57,plain,(
% 31.66/4.49    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f33])).
% 31.66/4.49  
% 31.66/4.49  fof(f12,axiom,(
% 31.66/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f20,plain,(
% 31.66/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 31.66/4.49    inference(unused_predicate_definition_removal,[],[f12])).
% 31.66/4.49  
% 31.66/4.49  fof(f26,plain,(
% 31.66/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 31.66/4.49    inference(ennf_transformation,[],[f20])).
% 31.66/4.49  
% 31.66/4.49  fof(f53,plain,(
% 31.66/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f26])).
% 31.66/4.49  
% 31.66/4.49  fof(f5,axiom,(
% 31.66/4.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f21,plain,(
% 31.66/4.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.66/4.49    inference(ennf_transformation,[],[f5])).
% 31.66/4.49  
% 31.66/4.49  fof(f46,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f21])).
% 31.66/4.49  
% 31.66/4.49  fof(f66,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(definition_unfolding,[],[f46,f42])).
% 31.66/4.49  
% 31.66/4.49  fof(f7,axiom,(
% 31.66/4.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f22,plain,(
% 31.66/4.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.66/4.49    inference(ennf_transformation,[],[f7])).
% 31.66/4.49  
% 31.66/4.49  fof(f48,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f22])).
% 31.66/4.49  
% 31.66/4.49  fof(f6,axiom,(
% 31.66/4.49    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f47,plain,(
% 31.66/4.49    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f6])).
% 31.66/4.49  
% 31.66/4.49  fof(f2,axiom,(
% 31.66/4.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f43,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 31.66/4.49    inference(cnf_transformation,[],[f2])).
% 31.66/4.49  
% 31.66/4.49  fof(f4,axiom,(
% 31.66/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f45,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f4])).
% 31.66/4.49  
% 31.66/4.49  fof(f65,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0) )),
% 31.66/4.49    inference(definition_unfolding,[],[f43,f45])).
% 31.66/4.49  
% 31.66/4.49  fof(f13,axiom,(
% 31.66/4.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f27,plain,(
% 31.66/4.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.66/4.49    inference(ennf_transformation,[],[f13])).
% 31.66/4.49  
% 31.66/4.49  fof(f28,plain,(
% 31.66/4.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.66/4.49    inference(flattening,[],[f27])).
% 31.66/4.49  
% 31.66/4.49  fof(f54,plain,(
% 31.66/4.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f28])).
% 31.66/4.49  
% 31.66/4.49  fof(f8,axiom,(
% 31.66/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f23,plain,(
% 31.66/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.66/4.49    inference(ennf_transformation,[],[f8])).
% 31.66/4.49  
% 31.66/4.49  fof(f24,plain,(
% 31.66/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.66/4.49    inference(flattening,[],[f23])).
% 31.66/4.49  
% 31.66/4.49  fof(f49,plain,(
% 31.66/4.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(cnf_transformation,[],[f24])).
% 31.66/4.49  
% 31.66/4.49  fof(f67,plain,(
% 31.66/4.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.49    inference(definition_unfolding,[],[f49,f45])).
% 31.66/4.49  
% 31.66/4.49  fof(f15,axiom,(
% 31.66/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f31,plain,(
% 31.66/4.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.49    inference(ennf_transformation,[],[f15])).
% 31.66/4.49  
% 31.66/4.49  fof(f56,plain,(
% 31.66/4.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f31])).
% 31.66/4.49  
% 31.66/4.49  fof(f14,axiom,(
% 31.66/4.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 31.66/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.66/4.49  
% 31.66/4.49  fof(f29,plain,(
% 31.66/4.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.66/4.49    inference(ennf_transformation,[],[f14])).
% 31.66/4.49  
% 31.66/4.49  fof(f30,plain,(
% 31.66/4.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.66/4.49    inference(flattening,[],[f29])).
% 31.66/4.49  
% 31.66/4.49  fof(f55,plain,(
% 31.66/4.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.66/4.49    inference(cnf_transformation,[],[f30])).
% 31.66/4.49  
% 31.66/4.49  fof(f59,plain,(
% 31.66/4.49    v2_pre_topc(sK0)),
% 31.66/4.49    inference(cnf_transformation,[],[f41])).
% 31.66/4.49  
% 31.66/4.49  fof(f63,plain,(
% 31.66/4.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 31.66/4.49    inference(cnf_transformation,[],[f41])).
% 31.66/4.49  
% 31.66/4.49  cnf(c_17,negated_conjecture,
% 31.66/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.66/4.49      inference(cnf_transformation,[],[f61]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_655,plain,
% 31.66/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_14,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.49      | ~ l1_pre_topc(X1)
% 31.66/4.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 31.66/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_658,plain,
% 31.66/4.49      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.66/4.49      | l1_pre_topc(X0) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_1077,plain,
% 31.66/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 31.66/4.49      | l1_pre_topc(sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_658]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_18,negated_conjecture,
% 31.66/4.49      ( l1_pre_topc(sK0) ),
% 31.66/4.49      inference(cnf_transformation,[],[f60]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_943,plain,
% 31.66/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.49      | ~ l1_pre_topc(sK0)
% 31.66/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(instantiation,[status(thm)],[c_14]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_1384,plain,
% 31.66/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(global_propositional_subsumption,
% 31.66/4.49                [status(thm)],
% 31.66/4.49                [c_1077,c_18,c_17,c_943]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_7,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.66/4.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 31.66/4.49      inference(cnf_transformation,[],[f69]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_664,plain,
% 31.66/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 31.66/4.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_6,plain,
% 31.66/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 31.66/4.49      inference(cnf_transformation,[],[f68]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_703,plain,
% 31.66/4.49      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.66/4.49      inference(light_normalisation,[status(thm)],[c_664,c_6]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2106,plain,
% 31.66/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_703]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2532,plain,
% 31.66/4.49      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_1384,c_2106]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_0,plain,
% 31.66/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 31.66/4.49      inference(cnf_transformation,[],[f64]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_687,plain,
% 31.66/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_subset_1(X0,X1))) = k3_xboole_0(X0,X1) ),
% 31.66/4.49      inference(light_normalisation,[status(thm)],[c_0,c_6]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_1228,plain,
% 31.66/4.49      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_xboole_0(X0,X1) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_6,c_687]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_3155,plain,
% 31.66/4.49      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_2532,c_1228]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_16,negated_conjecture,
% 31.66/4.49      ( v4_pre_topc(sK1,sK0)
% 31.66/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(cnf_transformation,[],[f62]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_656,plain,
% 31.66/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2520,plain,
% 31.66/4.49      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_2106,c_656]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_6150,plain,
% 31.66/4.49      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_3155,c_2520]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_13,plain,
% 31.66/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.66/4.49      | r1_tarski(k2_tops_1(X1,X0),X0)
% 31.66/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.49      | ~ l1_pre_topc(X1) ),
% 31.66/4.49      inference(cnf_transformation,[],[f57]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_659,plain,
% 31.66/4.49      ( v4_pre_topc(X0,X1) != iProver_top
% 31.66/4.49      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 31.66/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.66/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_1927,plain,
% 31.66/4.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 31.66/4.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 31.66/4.49      | l1_pre_topc(sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_659]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_21,plain,
% 31.66/4.49      ( l1_pre_topc(sK0) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2942,plain,
% 31.66/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(global_propositional_subsumption,
% 31.66/4.49                [status(thm)],
% 31.66/4.49                [c_1927,c_21]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2943,plain,
% 31.66/4.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 31.66/4.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.66/4.49      inference(renaming,[status(thm)],[c_2942]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_9,plain,
% 31.66/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.66/4.49      inference(cnf_transformation,[],[f53]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_663,plain,
% 31.66/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.66/4.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.66/4.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 31.66/4.49      inference(cnf_transformation,[],[f66]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_668,plain,
% 31.66/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_698,plain,
% 31.66/4.49      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_668,c_6]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2080,plain,
% 31.66/4.49      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 31.66/4.49      | r1_tarski(X1,X0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_663,c_698]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_9923,plain,
% 31.66/4.49      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_2943,c_2080]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_9926,plain,
% 31.66/4.49      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(light_normalisation,[status(thm)],[c_9923,c_2532]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_10160,plain,
% 31.66/4.49      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 31.66/4.49      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_6150,c_9926]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_4,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.66/4.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 31.66/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_666,plain,
% 31.66/4.49      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_1811,plain,
% 31.66/4.49      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 31.66/4.49      | r1_tarski(X1,X0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_663,c_666]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_9892,plain,
% 31.66/4.49      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_2943,c_1811]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_10027,plain,
% 31.66/4.49      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 31.66/4.49      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_6150,c_9892]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_46667,plain,
% 31.66/4.49      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 31.66/4.49      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_10160,c_10027]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_3,plain,
% 31.66/4.49      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 31.66/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_667,plain,
% 31.66/4.49      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2081,plain,
% 31.66/4.49      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_667,c_698]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2090,plain,
% 31.66/4.49      ( k3_subset_1(X0,k6_subset_1(X0,X1)) = k3_xboole_0(X0,X1) ),
% 31.66/4.49      inference(light_normalisation,[status(thm)],[c_2081,c_1228]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_3686,plain,
% 31.66/4.49      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_2532,c_2090]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_46668,plain,
% 31.66/4.49      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_46667,c_3686]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_1,plain,
% 31.66/4.49      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
% 31.66/4.49      inference(cnf_transformation,[],[f65]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_47374,plain,
% 31.66/4.49      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_46668,c_1]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_10,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.49      | ~ l1_pre_topc(X1) ),
% 31.66/4.49      inference(cnf_transformation,[],[f54]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_662,plain,
% 31.66/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.66/4.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 31.66/4.49      | l1_pre_topc(X1) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_5,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.66/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.66/4.49      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 31.66/4.49      inference(cnf_transformation,[],[f67]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_665,plain,
% 31.66/4.49      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 31.66/4.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2368,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 31.66/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_665]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2701,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 31.66/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.49      | l1_pre_topc(sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_662,c_2368]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_5555,plain,
% 31.66/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.49      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 31.66/4.49      inference(global_propositional_subsumption,
% 31.66/4.49                [status(thm)],
% 31.66/4.49                [c_2701,c_21]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_5556,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 31.66/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.66/4.49      inference(renaming,[status(thm)],[c_5555]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_5566,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_5556]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_12,plain,
% 31.66/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.49      | ~ l1_pre_topc(X1)
% 31.66/4.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 31.66/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_660,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.66/4.49      | l1_pre_topc(X0) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_3408,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 31.66/4.49      | l1_pre_topc(sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_660]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_938,plain,
% 31.66/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.49      | ~ l1_pre_topc(sK0)
% 31.66/4.49      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.66/4.49      inference(instantiation,[status(thm)],[c_12]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_3922,plain,
% 31.66/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.66/4.49      inference(global_propositional_subsumption,
% 31.66/4.49                [status(thm)],
% 31.66/4.49                [c_3408,c_18,c_17,c_938]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_5574,plain,
% 31.66/4.49      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 31.66/4.49      inference(light_normalisation,[status(thm)],[c_5566,c_3922]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_48663,plain,
% 31.66/4.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_47374,c_5574]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_11,plain,
% 31.66/4.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 31.66/4.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 31.66/4.49      | ~ v2_pre_topc(X0)
% 31.66/4.49      | ~ l1_pre_topc(X0) ),
% 31.66/4.49      inference(cnf_transformation,[],[f55]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_661,plain,
% 31.66/4.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 31.66/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.66/4.49      | v2_pre_topc(X0) != iProver_top
% 31.66/4.49      | l1_pre_topc(X0) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_3455,plain,
% 31.66/4.49      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 31.66/4.49      | v2_pre_topc(sK0) != iProver_top
% 31.66/4.49      | l1_pre_topc(sK0) != iProver_top ),
% 31.66/4.49      inference(superposition,[status(thm)],[c_655,c_661]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_19,negated_conjecture,
% 31.66/4.49      ( v2_pre_topc(sK0) ),
% 31.66/4.49      inference(cnf_transformation,[],[f59]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_20,plain,
% 31.66/4.49      ( v2_pre_topc(sK0) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_22,plain,
% 31.66/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_872,plain,
% 31.66/4.49      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 31.66/4.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.49      | ~ v2_pre_topc(sK0)
% 31.66/4.49      | ~ l1_pre_topc(sK0) ),
% 31.66/4.49      inference(instantiation,[status(thm)],[c_11]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_873,plain,
% 31.66/4.49      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 31.66/4.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.49      | v2_pre_topc(sK0) != iProver_top
% 31.66/4.49      | l1_pre_topc(sK0) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_4025,plain,
% 31.66/4.49      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 31.66/4.49      inference(global_propositional_subsumption,
% 31.66/4.49                [status(thm)],
% 31.66/4.49                [c_3455,c_20,c_21,c_22,c_873]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_49085,plain,
% 31.66/4.49      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_48663,c_4025]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_15,negated_conjecture,
% 31.66/4.49      ( ~ v4_pre_topc(sK1,sK0)
% 31.66/4.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 31.66/4.49      inference(cnf_transformation,[],[f63]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_657,plain,
% 31.66/4.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_2521,plain,
% 31.66/4.49      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_2106,c_657]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(c_6151,plain,
% 31.66/4.49      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 31.66/4.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 31.66/4.49      inference(demodulation,[status(thm)],[c_3155,c_2521]) ).
% 31.66/4.49  
% 31.66/4.49  cnf(contradiction,plain,
% 31.66/4.49      ( $false ),
% 31.66/4.49      inference(minisat,[status(thm)],[c_49085,c_46668,c_6151]) ).
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.66/4.49  
% 31.66/4.49  ------                               Statistics
% 31.66/4.49  
% 31.66/4.49  ------ Selected
% 31.66/4.49  
% 31.66/4.49  total_time:                             3.677
% 31.66/4.49  
%------------------------------------------------------------------------------
