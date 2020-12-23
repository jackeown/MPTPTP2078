%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:01 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  138 (1364 expanded)
%              Number of clauses        :   86 ( 493 expanded)
%              Number of leaves         :   15 ( 289 expanded)
%              Depth                    :   24
%              Number of atoms          :  348 (4776 expanded)
%              Number of equality atoms :  188 (1807 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k1_xboole_0 != k1_tops_1(X0,sK1)
          | ~ v2_tops_1(sK1,X0) )
        & ( k1_xboole_0 = k1_tops_1(X0,sK1)
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_642,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_651,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1017,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_651])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_653,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1151,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1017,c_653])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_643,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_657,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1388,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_643,c_657])).

cnf(c_1483,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1151,c_1388])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1882,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_656])).

cnf(c_1484,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1151,c_643])).

cnf(c_2613,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_1484])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_652,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2026,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_652])).

cnf(c_2044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2026,c_1151])).

cnf(c_18,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2626,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_18])).

cnf(c_2627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2626])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_655,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2635,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_655])).

cnf(c_7130,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_2613,c_2635])).

cnf(c_15,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_644,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_646,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1480,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1388,c_646])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1750,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_18,c_19])).

cnf(c_1754,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1750,c_1151])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_648,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2065,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_648])).

cnf(c_2792,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2065,c_18])).

cnf(c_2793,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2792])).

cnf(c_2804,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2613,c_2793])).

cnf(c_3882,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_2804])).

cnf(c_3887,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_644,c_3882])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_650,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3113,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_650])).

cnf(c_3117,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3113,c_1151])).

cnf(c_3654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3117,c_18])).

cnf(c_3655,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3654])).

cnf(c_3664,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1484,c_3655])).

cnf(c_3675,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3664,c_1483])).

cnf(c_3995,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3887,c_3675])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_658,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1387,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_657])).

cnf(c_3423,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_658,c_1387])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3424,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3423,c_1])).

cnf(c_1234,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_655])).

cnf(c_3256,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_658,c_1234])).

cnf(c_3427,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3424,c_3256])).

cnf(c_5159,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3995,c_3427])).

cnf(c_5161,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5159,c_3675])).

cnf(c_7146,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7130,c_5161])).

cnf(c_7147,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_7146,c_3424])).

cnf(c_10,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_649,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7337,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7147,c_649])).

cnf(c_7349,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7337,c_1151])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_645,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5163,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5159,c_645])).

cnf(c_5164,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5163])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_647,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1866,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_647])).

cnf(c_1871,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1866,c_1151])).

cnf(c_2943,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1871,c_18])).

cnf(c_2944,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2943])).

cnf(c_2953,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2944])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7349,c_5164,c_2953,c_1882,c_1484,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.54/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.99  
% 3.54/0.99  ------  iProver source info
% 3.54/0.99  
% 3.54/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.99  git: non_committed_changes: false
% 3.54/0.99  git: last_make_outside_of_git: false
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  ------ Parsing...
% 3.54/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.99  ------ Proving...
% 3.54/0.99  ------ Problem Properties 
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  clauses                                 18
% 3.54/0.99  conjectures                             4
% 3.54/0.99  EPR                                     3
% 3.54/0.99  Horn                                    17
% 3.54/0.99  unary                                   4
% 3.54/0.99  binary                                  8
% 3.54/0.99  lits                                    42
% 3.54/0.99  lits eq                                 9
% 3.54/0.99  fd_pure                                 0
% 3.54/0.99  fd_pseudo                               0
% 3.54/0.99  fd_cond                                 0
% 3.54/0.99  fd_pseudo_cond                          0
% 3.54/0.99  AC symbols                              0
% 3.54/0.99  
% 3.54/0.99  ------ Input Options Time Limit: Unbounded
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  Current options:
% 3.54/0.99  ------ 
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ Proving...
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS status Theorem for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  fof(f13,conjecture,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f14,negated_conjecture,(
% 3.54/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.54/0.99    inference(negated_conjecture,[],[f13])).
% 3.54/0.99  
% 3.54/0.99  fof(f27,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f14])).
% 3.54/0.99  
% 3.54/0.99  fof(f30,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.54/0.99    inference(nnf_transformation,[],[f27])).
% 3.54/0.99  
% 3.54/0.99  fof(f31,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.54/0.99    inference(flattening,[],[f30])).
% 3.54/0.99  
% 3.54/0.99  fof(f33,plain,(
% 3.54/0.99    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f32,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f34,plain,(
% 3.54/0.99    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.54/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 3.54/0.99  
% 3.54/0.99  fof(f49,plain,(
% 3.54/0.99    l1_pre_topc(sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f34])).
% 3.54/0.99  
% 3.54/0.99  fof(f9,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f23,plain,(
% 3.54/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f9])).
% 3.54/0.99  
% 3.54/0.99  fof(f43,plain,(
% 3.54/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f23])).
% 3.54/0.99  
% 3.54/0.99  fof(f7,axiom,(
% 3.54/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f20,plain,(
% 3.54/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f7])).
% 3.54/0.99  
% 3.54/0.99  fof(f41,plain,(
% 3.54/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f20])).
% 3.54/0.99  
% 3.54/0.99  fof(f50,plain,(
% 3.54/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.54/0.99    inference(cnf_transformation,[],[f34])).
% 3.54/0.99  
% 3.54/0.99  fof(f3,axiom,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f16,plain,(
% 3.54/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f3])).
% 3.54/0.99  
% 3.54/0.99  fof(f37,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f16])).
% 3.54/0.99  
% 3.54/0.99  fof(f4,axiom,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f17,plain,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f4])).
% 3.54/0.99  
% 3.54/0.99  fof(f38,plain,(
% 3.54/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f17])).
% 3.54/0.99  
% 3.54/0.99  fof(f8,axiom,(
% 3.54/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f21,plain,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f8])).
% 3.54/0.99  
% 3.54/0.99  fof(f22,plain,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(flattening,[],[f21])).
% 3.54/0.99  
% 3.54/0.99  fof(f42,plain,(
% 3.54/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f22])).
% 3.54/0.99  
% 3.54/0.99  fof(f5,axiom,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f18,plain,(
% 3.54/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f5])).
% 3.54/0.99  
% 3.54/0.99  fof(f39,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f18])).
% 3.54/0.99  
% 3.54/0.99  fof(f51,plain,(
% 3.54/0.99    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f34])).
% 3.54/0.99  
% 3.54/0.99  fof(f12,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f26,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f12])).
% 3.54/0.99  
% 3.54/0.99  fof(f29,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(nnf_transformation,[],[f26])).
% 3.54/0.99  
% 3.54/0.99  fof(f47,plain,(
% 3.54/0.99    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f29])).
% 3.54/0.99  
% 3.54/0.99  fof(f11,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f25,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f11])).
% 3.54/0.99  
% 3.54/0.99  fof(f28,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(nnf_transformation,[],[f25])).
% 3.54/0.99  
% 3.54/0.99  fof(f45,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f28])).
% 3.54/0.99  
% 3.54/0.99  fof(f10,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f24,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f10])).
% 3.54/0.99  
% 3.54/0.99  fof(f44,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f24])).
% 3.54/0.99  
% 3.54/0.99  fof(f1,axiom,(
% 3.54/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f35,plain,(
% 3.54/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f1])).
% 3.54/0.99  
% 3.54/0.99  fof(f6,axiom,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f15,plain,(
% 3.54/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.54/0.99    inference(unused_predicate_definition_removal,[],[f6])).
% 3.54/0.99  
% 3.54/0.99  fof(f19,plain,(
% 3.54/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.54/0.99    inference(ennf_transformation,[],[f15])).
% 3.54/0.99  
% 3.54/0.99  fof(f40,plain,(
% 3.54/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f19])).
% 3.54/0.99  
% 3.54/0.99  fof(f2,axiom,(
% 3.54/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f36,plain,(
% 3.54/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.54/0.99    inference(cnf_transformation,[],[f2])).
% 3.54/0.99  
% 3.54/0.99  fof(f46,plain,(
% 3.54/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f28])).
% 3.54/0.99  
% 3.54/0.99  fof(f52,plain,(
% 3.54/0.99    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f34])).
% 3.54/0.99  
% 3.54/0.99  fof(f48,plain,(
% 3.54/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f29])).
% 3.54/0.99  
% 3.54/0.99  cnf(c_17,negated_conjecture,
% 3.54/0.99      ( l1_pre_topc(sK0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_642,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8,plain,
% 3.54/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_651,plain,
% 3.54/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1017,plain,
% 3.54/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_642,c_651]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6,plain,
% 3.54/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_653,plain,
% 3.54/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.54/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1151,plain,
% 3.54/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1017,c_653]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_16,negated_conjecture,
% 3.54/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.54/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_643,plain,
% 3.54/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_657,plain,
% 3.54/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.54/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1388,plain,
% 3.54/0.99      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_643,c_657]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1483,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_1151,c_1388]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_656,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1882,plain,
% 3.54/0.99      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.54/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1483,c_656]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1484,plain,
% 3.54/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_1151,c_643]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2613,plain,
% 3.54/0.99      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_1882,c_1484]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_652,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.54/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2026,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.54/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1151,c_652]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2044,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_2026,c_1151]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_18,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2626,plain,
% 3.54/0.99      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2044,c_18]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2627,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_2626]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_655,plain,
% 3.54/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.54/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2635,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2627,c_655]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7130,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2613,c_2635]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_15,negated_conjecture,
% 3.54/0.99      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_644,plain,
% 3.54/0.99      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 3.54/0.99      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_13,plain,
% 3.54/0.99      ( ~ v2_tops_1(X0,X1)
% 3.54/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.54/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_646,plain,
% 3.54/0.99      ( v2_tops_1(X0,X1) != iProver_top
% 3.54/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1480,plain,
% 3.54/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.54/0.99      | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 3.54/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1388,c_646]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_19,plain,
% 3.54/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1750,plain,
% 3.54/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.54/0.99      | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_1480,c_18,c_19]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1754,plain,
% 3.54/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.54/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1750,c_1151]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11,plain,
% 3.54/0.99      ( ~ v1_tops_1(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_648,plain,
% 3.54/0.99      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 3.54/0.99      | v1_tops_1(X1,X0) != iProver_top
% 3.54/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2065,plain,
% 3.54/0.99      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.54/0.99      | v1_tops_1(X0,sK0) != iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1151,c_648]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2792,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | v1_tops_1(X0,sK0) != iProver_top
% 3.54/0.99      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2065,c_18]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2793,plain,
% 3.54/0.99      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.54/0.99      | v1_tops_1(X0,sK0) != iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_2792]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2804,plain,
% 3.54/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.54/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2613,c_2793]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3882,plain,
% 3.54/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.54/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1754,c_2804]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3887,plain,
% 3.54/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.54/0.99      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_644,c_3882]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9,plain,
% 3.54/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_650,plain,
% 3.54/0.99      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 3.54/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3113,plain,
% 3.54/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1151,c_650]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3117,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_3113,c_1151]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3654,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_3117,c_18]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3655,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_3654]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3664,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1484,c_3655]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3675,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_3664,c_1483]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3995,plain,
% 3.54/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.54/0.99      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_3887,c_3675]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_0,plain,
% 3.54/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_658,plain,
% 3.54/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_654,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.54/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1387,plain,
% 3.54/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.54/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_654,c_657]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3423,plain,
% 3.54/0.99      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_658,c_1387]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3424,plain,
% 3.54/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_3423,c_1]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1234,plain,
% 3.54/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.54/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_654,c_655]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3256,plain,
% 3.54/0.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_658,c_1234]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3427,plain,
% 3.54/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_3424,c_3256]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5159,plain,
% 3.54/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_3995,c_3427]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5161,plain,
% 3.54/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_5159,c_3675]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7146,plain,
% 3.54/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_7130,c_5161]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7147,plain,
% 3.54/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_7146,c_3424]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10,plain,
% 3.54/0.99      ( v1_tops_1(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_649,plain,
% 3.54/0.99      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 3.54/0.99      | v1_tops_1(X1,X0) = iProver_top
% 3.54/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7337,plain,
% 3.54/0.99      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.54/0.99      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_7147,c_649]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7349,plain,
% 3.54/0.99      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.54/0.99      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_7337,c_1151]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_14,negated_conjecture,
% 3.54/0.99      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_645,plain,
% 3.54/0.99      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 3.54/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5163,plain,
% 3.54/0.99      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_5159,c_645]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5164,plain,
% 3.54/0.99      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 3.54/0.99      inference(equality_resolution_simp,[status(thm)],[c_5163]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_12,plain,
% 3.54/0.99      ( v2_tops_1(X0,X1)
% 3.54/0.99      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.54/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_647,plain,
% 3.54/0.99      ( v2_tops_1(X0,X1) = iProver_top
% 3.54/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1866,plain,
% 3.54/0.99      ( v2_tops_1(X0,sK0) = iProver_top
% 3.54/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1151,c_647]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1871,plain,
% 3.54/0.99      ( v2_tops_1(X0,sK0) = iProver_top
% 3.54/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1866,c_1151]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2943,plain,
% 3.54/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.54/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.54/0.99      | v2_tops_1(X0,sK0) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_1871,c_18]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2944,plain,
% 3.54/0.99      ( v2_tops_1(X0,sK0) = iProver_top
% 3.54/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.54/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_2943]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2953,plain,
% 3.54/0.99      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.54/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.54/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1483,c_2944]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(contradiction,plain,
% 3.54/0.99      ( $false ),
% 3.54/0.99      inference(minisat,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_7349,c_5164,c_2953,c_1882,c_1484,c_18]) ).
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  ------                               Statistics
% 3.54/0.99  
% 3.54/0.99  ------ Selected
% 3.54/0.99  
% 3.54/0.99  total_time:                             0.233
% 3.54/0.99  
%------------------------------------------------------------------------------
