%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:32 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 306 expanded)
%              Number of clauses        :   77 (  93 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   20
%              Number of atoms          :  370 (1342 expanded)
%              Number of equality atoms :  184 ( 463 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f41,f44,f49])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_548,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_540,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3655,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != k7_subset_1(X1,X3,X5)
    | k7_subset_1(X0,X2,X4) = X6 ),
    inference(resolution,[status(thm)],[c_548,c_540])).

cnf(c_539,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1431,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_540,c_539])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_3804,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
    inference(resolution,[status(thm)],[c_1431,c_305])).

cnf(c_13071,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_tops_1(sK0,X0)
    | X2 != k2_pre_topc(sK0,X0)
    | X3 != u1_struct_0(sK0)
    | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
    inference(resolution,[status(thm)],[c_3655,c_3804])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_129,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_264,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_265,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_17])).

cnf(c_270,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_270])).

cnf(c_387,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_389,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_16])).

cnf(c_463,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_389])).

cnf(c_464,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_463])).

cnf(c_13294,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_13071,c_464])).

cnf(c_13295,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK1) != sK1
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_13294])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_131,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_328,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_329,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_131,c_329])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_378,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_16])).

cnf(c_465,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_378])).

cnf(c_466,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_843,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_844,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_873,plain,
    ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_844,c_5])).

cnf(c_2659,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_843,c_873])).

cnf(c_2902,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_466,c_2659])).

cnf(c_3,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_846,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_1])).

cnf(c_842,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_3744,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0)) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_846,c_842])).

cnf(c_2,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1415,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_6893,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_3744,c_1415])).

cnf(c_11874,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2902,c_6893])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_845,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2680,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_845])).

cnf(c_9113,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_2680])).

cnf(c_9197,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_843,c_9113])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_841,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_1013,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_843,c_841])).

cnf(c_9204,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_9197,c_1013])).

cnf(c_11910,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_11874,c_9204])).

cnf(c_1523,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_2743,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1523])).

cnf(c_4812,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_1392,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13295,c_11910,c_4812,c_1392,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/1.00  
% 3.77/1.00  ------  iProver source info
% 3.77/1.00  
% 3.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/1.00  git: non_committed_changes: false
% 3.77/1.00  git: last_make_outside_of_git: false
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  ------ Parsing...
% 3.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/1.00  ------ Proving...
% 3.77/1.00  ------ Problem Properties 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  clauses                                 15
% 3.77/1.00  conjectures                             1
% 3.77/1.00  EPR                                     0
% 3.77/1.00  Horn                                    14
% 3.77/1.00  unary                                   5
% 3.77/1.00  binary                                  7
% 3.77/1.00  lits                                    28
% 3.77/1.00  lits eq                                 15
% 3.77/1.00  fd_pure                                 0
% 3.77/1.00  fd_pseudo                               0
% 3.77/1.00  fd_cond                                 0
% 3.77/1.00  fd_pseudo_cond                          0
% 3.77/1.00  AC symbols                              0
% 3.77/1.00  
% 3.77/1.00  ------ Input Options Time Limit: Unbounded
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  Current options:
% 3.77/1.00  ------ 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ Proving...
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS status Theorem for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  fof(f15,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f31,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f15])).
% 3.77/1.00  
% 3.77/1.00  fof(f55,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f31])).
% 3.77/1.00  
% 3.77/1.00  fof(f17,conjecture,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f18,negated_conjecture,(
% 3.77/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.77/1.00    inference(negated_conjecture,[],[f17])).
% 3.77/1.00  
% 3.77/1.00  fof(f33,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f18])).
% 3.77/1.00  
% 3.77/1.00  fof(f34,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f33])).
% 3.77/1.00  
% 3.77/1.00  fof(f35,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.77/1.00    inference(nnf_transformation,[],[f34])).
% 3.77/1.00  
% 3.77/1.00  fof(f36,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f35])).
% 3.77/1.00  
% 3.77/1.00  fof(f38,plain,(
% 3.77/1.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f37,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f39,plain,(
% 3.77/1.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 3.77/1.00  
% 3.77/1.00  fof(f58,plain,(
% 3.77/1.00    l1_pre_topc(sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f61,plain,(
% 3.77/1.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f12,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f25,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f12])).
% 3.77/1.00  
% 3.77/1.00  fof(f26,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f52,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f57,plain,(
% 3.77/1.00    v2_pre_topc(sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f59,plain,(
% 3.77/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.77/1.00    inference(cnf_transformation,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f60,plain,(
% 3.77/1.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f51,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f9,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f23,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f9])).
% 3.77/1.00  
% 3.77/1.00  fof(f48,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f23])).
% 3.77/1.00  
% 3.77/1.00  fof(f1,axiom,(
% 3.77/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f40,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f1])).
% 3.77/1.00  
% 3.77/1.00  fof(f10,axiom,(
% 3.77/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f49,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f10])).
% 3.77/1.00  
% 3.77/1.00  fof(f62,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.77/1.00    inference(definition_unfolding,[],[f40,f49])).
% 3.77/1.00  
% 3.77/1.00  fof(f67,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/1.00    inference(definition_unfolding,[],[f48,f62])).
% 3.77/1.00  
% 3.77/1.00  fof(f8,axiom,(
% 3.77/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f47,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f8])).
% 3.77/1.00  
% 3.77/1.00  fof(f66,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f47,f62])).
% 3.77/1.00  
% 3.77/1.00  fof(f6,axiom,(
% 3.77/1.00    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f45,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f6])).
% 3.77/1.00  
% 3.77/1.00  fof(f11,axiom,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f19,plain,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.77/1.00    inference(unused_predicate_definition_removal,[],[f11])).
% 3.77/1.00  
% 3.77/1.00  fof(f24,plain,(
% 3.77/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.77/1.00    inference(ennf_transformation,[],[f19])).
% 3.77/1.00  
% 3.77/1.00  fof(f50,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f24])).
% 3.77/1.00  
% 3.77/1.00  fof(f3,axiom,(
% 3.77/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f20,plain,(
% 3.77/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f3])).
% 3.77/1.00  
% 3.77/1.00  fof(f42,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f20])).
% 3.77/1.00  
% 3.77/1.00  fof(f64,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f42,f49])).
% 3.77/1.00  
% 3.77/1.00  fof(f4,axiom,(
% 3.77/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f43,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f4])).
% 3.77/1.00  
% 3.77/1.00  fof(f2,axiom,(
% 3.77/1.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f41,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.77/1.00    inference(cnf_transformation,[],[f2])).
% 3.77/1.00  
% 3.77/1.00  fof(f5,axiom,(
% 3.77/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f44,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f5])).
% 3.77/1.00  
% 3.77/1.00  fof(f63,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 3.77/1.00    inference(definition_unfolding,[],[f41,f44,f49])).
% 3.77/1.00  
% 3.77/1.00  fof(f13,axiom,(
% 3.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f27,plain,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f13])).
% 3.77/1.00  
% 3.77/1.00  fof(f28,plain,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f53,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f28])).
% 3.77/1.00  
% 3.77/1.00  fof(f7,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f21,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.77/1.00    inference(ennf_transformation,[],[f7])).
% 3.77/1.00  
% 3.77/1.00  fof(f22,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.77/1.00    inference(flattening,[],[f21])).
% 3.77/1.00  
% 3.77/1.00  fof(f46,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f65,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.77/1.00    inference(definition_unfolding,[],[f46,f44])).
% 3.77/1.00  
% 3.77/1.00  fof(f16,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f32,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f16])).
% 3.77/1.00  
% 3.77/1.00  fof(f56,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f32])).
% 3.77/1.00  
% 3.77/1.00  cnf(c_548,plain,
% 3.77/1.00      ( X0 != X1
% 3.77/1.00      | X2 != X3
% 3.77/1.00      | X4 != X5
% 3.77/1.00      | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
% 3.77/1.00      theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_540,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3655,plain,
% 3.77/1.00      ( X0 != X1
% 3.77/1.00      | X2 != X3
% 3.77/1.00      | X4 != X5
% 3.77/1.00      | X6 != k7_subset_1(X1,X3,X5)
% 3.77/1.00      | k7_subset_1(X0,X2,X4) = X6 ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_548,c_540]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_539,plain,( X0 = X0 ),theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1431,plain,
% 3.77/1.00      ( X0 != X1 | X1 = X0 ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_540,c_539]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_12,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_17,negated_conjecture,
% 3.77/1.00      ( l1_pre_topc(sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_304,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.77/1.00      | sK0 != X1 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_305,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_304]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3804,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_1431,c_305]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13071,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | X1 != k1_tops_1(sK0,X0)
% 3.77/1.00      | X2 != k2_pre_topc(sK0,X0)
% 3.77/1.00      | X3 != u1_struct_0(sK0)
% 3.77/1.00      | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_3655,c_3804]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_14,negated_conjecture,
% 3.77/1.00      ( ~ v4_pre_topc(sK1,sK0)
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_129,plain,
% 3.77/1.00      ( ~ v4_pre_topc(sK1,sK0)
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8,plain,
% 3.77/1.00      ( v4_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X1)
% 3.77/1.00      | k2_pre_topc(X1,X0) != X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_18,negated_conjecture,
% 3.77/1.00      ( v2_pre_topc(sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_264,plain,
% 3.77/1.00      ( v4_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | k2_pre_topc(X1,X0) != X0
% 3.77/1.00      | sK0 != X1 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_265,plain,
% 3.77/1.00      ( v4_pre_topc(X0,sK0)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | ~ l1_pre_topc(sK0)
% 3.77/1.00      | k2_pre_topc(sK0,X0) != X0 ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_264]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_269,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | v4_pre_topc(X0,sK0)
% 3.77/1.00      | k2_pre_topc(sK0,X0) != X0 ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_265,c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_270,plain,
% 3.77/1.00      ( v4_pre_topc(X0,sK0)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k2_pre_topc(sK0,X0) != X0 ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_269]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_386,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,X0) != X0
% 3.77/1.00      | sK1 != X0
% 3.77/1.00      | sK0 != sK0 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_129,c_270]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_387,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_16,negated_conjecture,
% 3.77/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_389,plain,
% 3.77/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_387,c_16]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_463,plain,
% 3.77/1.00      ( k2_pre_topc(sK0,sK1) != sK1
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(prop_impl,[status(thm)],[c_389]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_464,plain,
% 3.77/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_463]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13294,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) != sK1
% 3.77/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.77/1.00      | sK1 != k2_pre_topc(sK0,sK1) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_13071,c_464]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13295,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k2_pre_topc(sK0,sK1) != sK1
% 3.77/1.00      | sK1 != k2_pre_topc(sK0,sK1) ),
% 3.77/1.00      inference(equality_resolution_simp,[status(thm)],[c_13294]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15,negated_conjecture,
% 3.77/1.00      ( v4_pre_topc(sK1,sK0)
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_131,plain,
% 3.77/1.00      ( v4_pre_topc(sK1,sK0)
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(prop_impl,[status(thm)],[c_15]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9,plain,
% 3.77/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_328,plain,
% 3.77/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | k2_pre_topc(X1,X0) = X0
% 3.77/1.00      | sK0 != X1 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_329,plain,
% 3.77/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k2_pre_topc(sK0,X0) = X0 ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_328]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_375,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,X0) = X0
% 3.77/1.00      | sK1 != X0
% 3.77/1.00      | sK0 != sK0 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_131,c_329]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_376,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_378,plain,
% 3.77/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_376,c_16]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_465,plain,
% 3.77/1.00      ( k2_pre_topc(sK0,sK1) = sK1
% 3.77/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(prop_impl,[status(thm)],[c_378]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_466,plain,
% 3.77/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.77/1.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_465]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_843,plain,
% 3.77/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_844,plain,
% 3.77/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.77/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5,plain,
% 3.77/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_873,plain,
% 3.77/1.00      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
% 3.77/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_844,c_5]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2659,plain,
% 3.77/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_843,c_873]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2902,plain,
% 3.77/1.00      ( k2_pre_topc(sK0,sK1) = sK1
% 3.77/1.00      | k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_466,c_2659]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3,plain,
% 3.77/1.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_846,plain,
% 3.77/1.00      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_232,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/1.00      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_7,c_1]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_842,plain,
% 3.77/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 3.77/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_232]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3744,plain,
% 3.77/1.00      ( k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0)) = k6_subset_1(X0,X1) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_846,c_842]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2,plain,
% 3.77/1.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_0,plain,
% 3.77/1.00      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1415,plain,
% 3.77/1.00      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6893,plain,
% 3.77/1.00      ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_3744,c_1415]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11874,plain,
% 3.77/1.00      ( k2_pre_topc(sK0,sK1) = sK1
% 3.77/1.00      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2902,c_6893]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_316,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | sK0 != X1 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_317,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_316]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_839,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/1.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.77/1.00      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_845,plain,
% 3.77/1.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.77/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2680,plain,
% 3.77/1.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
% 3.77/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_839,c_845]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9113,plain,
% 3.77/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.77/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_843,c_2680]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9197,plain,
% 3.77/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_843,c_9113]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_292,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.77/1.00      | sK0 != X1 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_293,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/1.00      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_292]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_841,plain,
% 3.77/1.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.77/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1013,plain,
% 3.77/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_843,c_841]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9204,plain,
% 3.77/1.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_9197,c_1013]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11910,plain,
% 3.77/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_11874,c_9204]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1523,plain,
% 3.77/1.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_540]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2743,plain,
% 3.77/1.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1523]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4812,plain,
% 3.77/1.00      ( k2_pre_topc(sK0,sK1) != sK1
% 3.77/1.00      | sK1 = k2_pre_topc(sK0,sK1)
% 3.77/1.00      | sK1 != sK1 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_2743]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1392,plain,
% 3.77/1.00      ( sK1 = sK1 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_539]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(contradiction,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(minisat,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_13295,c_11910,c_4812,c_1392,c_16]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ Selected
% 3.77/1.00  
% 3.77/1.00  total_time:                             0.476
% 3.77/1.00  
%------------------------------------------------------------------------------
