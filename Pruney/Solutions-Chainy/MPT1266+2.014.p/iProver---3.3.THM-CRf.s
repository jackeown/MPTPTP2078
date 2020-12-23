%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:00 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  145 (1492 expanded)
%              Number of clauses        :   86 ( 528 expanded)
%              Number of leaves         :   18 ( 322 expanded)
%              Depth                    :   27
%              Number of atoms          :  356 (5196 expanded)
%              Number of equality atoms :  205 (2002 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_609,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_618,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1210,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_618])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_620,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1301,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1210,c_620])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_610,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1413,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1301,c_610])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_624,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2037,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1413,c_624])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_622,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2533,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_622])).

cnf(c_2754,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2533,c_1413])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_619,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2288,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_619])).

cnf(c_2306,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2288,c_1301])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2767,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_19])).

cnf(c_2768,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2767])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_621,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2776,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2768,c_621])).

cnf(c_6891,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_2754,c_2776])).

cnf(c_16,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_611,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_613,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1419,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_613])).

cnf(c_1420,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1419,c_1301])).

cnf(c_1666,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1420,c_19])).

cnf(c_1667,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1666])).

cnf(c_2534,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_1667])).

cnf(c_2982,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2534,c_1413])).

cnf(c_2983,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2982])).

cnf(c_12,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_615,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2327,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_615])).

cnf(c_3083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2327,c_19])).

cnf(c_3084,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3083])).

cnf(c_3096,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_3084])).

cnf(c_5490,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_3096])).

cnf(c_5495,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_611,c_5490])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_617,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3263,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_617])).

cnf(c_3267,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3263,c_1301])).

cnf(c_3584,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_19])).

cnf(c_3585,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3584])).

cnf(c_3594,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1413,c_3585])).

cnf(c_3605,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3594,c_2037])).

cnf(c_5645,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5495,c_3605])).

cnf(c_4,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_623,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_623,c_2])).

cnf(c_2036,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_635,c_624])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_961,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_2041,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2036,c_961])).

cnf(c_5648,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5645,c_2041])).

cnf(c_5651,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5648,c_3605])).

cnf(c_6898,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6891,c_5651])).

cnf(c_6899,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_6898,c_2])).

cnf(c_11,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_616,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7022,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6899,c_616])).

cnf(c_7034,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7022,c_1301])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_612,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5653,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5648,c_612])).

cnf(c_5654,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5653])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_614,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1854,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_614])).

cnf(c_1859,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1854,c_1301])).

cnf(c_3871,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1859,c_19])).

cnf(c_3872,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3871])).

cnf(c_3883,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_3872])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7034,c_5654,c_3883,c_2533,c_1413,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.71/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/0.98  
% 3.71/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.98  
% 3.71/0.98  ------  iProver source info
% 3.71/0.98  
% 3.71/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.98  git: non_committed_changes: false
% 3.71/0.98  git: last_make_outside_of_git: false
% 3.71/0.98  
% 3.71/0.98  ------ 
% 3.71/0.98  ------ Parsing...
% 3.71/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.98  
% 3.71/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.71/0.98  
% 3.71/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.98  
% 3.71/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.98  ------ Proving...
% 3.71/0.98  ------ Problem Properties 
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  clauses                                 19
% 3.71/0.98  conjectures                             4
% 3.71/0.98  EPR                                     2
% 3.71/0.98  Horn                                    18
% 3.71/0.98  unary                                   6
% 3.71/0.98  binary                                  7
% 3.71/0.98  lits                                    42
% 3.71/0.98  lits eq                                 11
% 3.71/0.98  fd_pure                                 0
% 3.71/0.98  fd_pseudo                               0
% 3.71/0.98  fd_cond                                 0
% 3.71/0.98  fd_pseudo_cond                          0
% 3.71/0.98  AC symbols                              0
% 3.71/0.98  
% 3.71/0.98  ------ Input Options Time Limit: Unbounded
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  ------ 
% 3.71/0.98  Current options:
% 3.71/0.98  ------ 
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  ------ Proving...
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  % SZS status Theorem for theBenchmark.p
% 3.71/0.98  
% 3.71/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.98  
% 3.71/0.98  fof(f16,conjecture,(
% 3.71/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f17,negated_conjecture,(
% 3.71/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.71/0.98    inference(negated_conjecture,[],[f16])).
% 3.71/0.98  
% 3.71/0.98  fof(f28,plain,(
% 3.71/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.71/0.98    inference(ennf_transformation,[],[f17])).
% 3.71/0.98  
% 3.71/0.98  fof(f31,plain,(
% 3.71/0.98    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.71/0.98    inference(nnf_transformation,[],[f28])).
% 3.71/0.98  
% 3.71/0.98  fof(f32,plain,(
% 3.71/0.98    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.71/0.98    inference(flattening,[],[f31])).
% 3.71/0.98  
% 3.71/0.98  fof(f34,plain,(
% 3.71/0.98    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.71/0.98    introduced(choice_axiom,[])).
% 3.71/0.98  
% 3.71/0.98  fof(f33,plain,(
% 3.71/0.98    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.71/0.98    introduced(choice_axiom,[])).
% 3.71/0.98  
% 3.71/0.98  fof(f35,plain,(
% 3.71/0.98    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.71/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 3.71/0.98  
% 3.71/0.98  fof(f53,plain,(
% 3.71/0.98    l1_pre_topc(sK0)),
% 3.71/0.98    inference(cnf_transformation,[],[f35])).
% 3.71/0.98  
% 3.71/0.98  fof(f12,axiom,(
% 3.71/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f24,plain,(
% 3.71/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(ennf_transformation,[],[f12])).
% 3.71/0.98  
% 3.71/0.98  fof(f47,plain,(
% 3.71/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f24])).
% 3.71/0.98  
% 3.71/0.98  fof(f10,axiom,(
% 3.71/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f21,plain,(
% 3.71/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.71/0.98    inference(ennf_transformation,[],[f10])).
% 3.71/0.98  
% 3.71/0.98  fof(f45,plain,(
% 3.71/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f21])).
% 3.71/0.98  
% 3.71/0.98  fof(f54,plain,(
% 3.71/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.71/0.98    inference(cnf_transformation,[],[f35])).
% 3.71/0.98  
% 3.71/0.98  fof(f5,axiom,(
% 3.71/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f18,plain,(
% 3.71/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.71/0.98    inference(ennf_transformation,[],[f5])).
% 3.71/0.98  
% 3.71/0.98  fof(f40,plain,(
% 3.71/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.71/0.98    inference(cnf_transformation,[],[f18])).
% 3.71/0.98  
% 3.71/0.98  fof(f7,axiom,(
% 3.71/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f19,plain,(
% 3.71/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.71/0.98    inference(ennf_transformation,[],[f7])).
% 3.71/0.98  
% 3.71/0.98  fof(f42,plain,(
% 3.71/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.71/0.98    inference(cnf_transformation,[],[f19])).
% 3.71/0.98  
% 3.71/0.98  fof(f11,axiom,(
% 3.71/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f22,plain,(
% 3.71/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.71/0.98    inference(ennf_transformation,[],[f11])).
% 3.71/0.98  
% 3.71/0.98  fof(f23,plain,(
% 3.71/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(flattening,[],[f22])).
% 3.71/0.98  
% 3.71/0.98  fof(f46,plain,(
% 3.71/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f23])).
% 3.71/0.98  
% 3.71/0.98  fof(f8,axiom,(
% 3.71/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f20,plain,(
% 3.71/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.71/0.98    inference(ennf_transformation,[],[f8])).
% 3.71/0.98  
% 3.71/0.98  fof(f43,plain,(
% 3.71/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.71/0.98    inference(cnf_transformation,[],[f20])).
% 3.71/0.98  
% 3.71/0.98  fof(f55,plain,(
% 3.71/0.98    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 3.71/0.98    inference(cnf_transformation,[],[f35])).
% 3.71/0.98  
% 3.71/0.98  fof(f15,axiom,(
% 3.71/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f27,plain,(
% 3.71/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(ennf_transformation,[],[f15])).
% 3.71/0.98  
% 3.71/0.98  fof(f30,plain,(
% 3.71/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(nnf_transformation,[],[f27])).
% 3.71/0.98  
% 3.71/0.98  fof(f51,plain,(
% 3.71/0.98    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f30])).
% 3.71/0.98  
% 3.71/0.98  fof(f14,axiom,(
% 3.71/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f26,plain,(
% 3.71/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(ennf_transformation,[],[f14])).
% 3.71/0.98  
% 3.71/0.98  fof(f29,plain,(
% 3.71/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(nnf_transformation,[],[f26])).
% 3.71/0.98  
% 3.71/0.98  fof(f49,plain,(
% 3.71/0.98    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f29])).
% 3.71/0.98  
% 3.71/0.98  fof(f13,axiom,(
% 3.71/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f25,plain,(
% 3.71/0.98    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.71/0.98    inference(ennf_transformation,[],[f13])).
% 3.71/0.98  
% 3.71/0.98  fof(f48,plain,(
% 3.71/0.98    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f25])).
% 3.71/0.98  
% 3.71/0.98  fof(f6,axiom,(
% 3.71/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f41,plain,(
% 3.71/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.71/0.98    inference(cnf_transformation,[],[f6])).
% 3.71/0.98  
% 3.71/0.98  fof(f9,axiom,(
% 3.71/0.98    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f44,plain,(
% 3.71/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.71/0.98    inference(cnf_transformation,[],[f9])).
% 3.71/0.98  
% 3.71/0.98  fof(f3,axiom,(
% 3.71/0.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f38,plain,(
% 3.71/0.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f3])).
% 3.71/0.98  
% 3.71/0.98  fof(f57,plain,(
% 3.71/0.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.71/0.98    inference(definition_unfolding,[],[f44,f38])).
% 3.71/0.98  
% 3.71/0.98  fof(f59,plain,(
% 3.71/0.98    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.71/0.98    inference(definition_unfolding,[],[f41,f57])).
% 3.71/0.98  
% 3.71/0.98  fof(f4,axiom,(
% 3.71/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f39,plain,(
% 3.71/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.71/0.98    inference(cnf_transformation,[],[f4])).
% 3.71/0.98  
% 3.71/0.98  fof(f58,plain,(
% 3.71/0.98    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.71/0.98    inference(definition_unfolding,[],[f39,f57])).
% 3.71/0.98  
% 3.71/0.98  fof(f1,axiom,(
% 3.71/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f36,plain,(
% 3.71/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.71/0.98    inference(cnf_transformation,[],[f1])).
% 3.71/0.98  
% 3.71/0.98  fof(f2,axiom,(
% 3.71/0.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.71/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.98  
% 3.71/0.98  fof(f37,plain,(
% 3.71/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.71/0.98    inference(cnf_transformation,[],[f2])).
% 3.71/0.98  
% 3.71/0.98  fof(f50,plain,(
% 3.71/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f29])).
% 3.71/0.98  
% 3.71/0.98  fof(f56,plain,(
% 3.71/0.98    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 3.71/0.98    inference(cnf_transformation,[],[f35])).
% 3.71/0.98  
% 3.71/0.98  fof(f52,plain,(
% 3.71/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.71/0.98    inference(cnf_transformation,[],[f30])).
% 3.71/0.98  
% 3.71/0.98  cnf(c_18,negated_conjecture,
% 3.71/0.98      ( l1_pre_topc(sK0) ),
% 3.71/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_609,plain,
% 3.71/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_9,plain,
% 3.71/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.71/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_618,plain,
% 3.71/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1210,plain,
% 3.71/0.98      ( l1_struct_0(sK0) = iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_609,c_618]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_7,plain,
% 3.71/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.71/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_620,plain,
% 3.71/0.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.71/0.98      | l1_struct_0(X0) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1301,plain,
% 3.71/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1210,c_620]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_17,negated_conjecture,
% 3.71/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.71/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_610,plain,
% 3.71/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1413,plain,
% 3.71/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.71/0.98      inference(demodulation,[status(thm)],[c_1301,c_610]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3,plain,
% 3.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.71/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.71/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_624,plain,
% 3.71/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.71/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2037,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1413,c_624]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5,plain,
% 3.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.71/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.71/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_622,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.71/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2533,plain,
% 3.71/0.98      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.71/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2037,c_622]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2754,plain,
% 3.71/0.98      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_2533,c_1413]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_8,plain,
% 3.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | ~ l1_pre_topc(X1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_619,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.71/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.71/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2288,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.71/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1301,c_619]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2306,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_2288,c_1301]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_19,plain,
% 3.71/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2767,plain,
% 3.71/0.98      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_2306,c_19]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2768,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.71/0.98      inference(renaming,[status(thm)],[c_2767]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_6,plain,
% 3.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.71/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.71/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_621,plain,
% 3.71/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.71/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2776,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2768,c_621]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_6891,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2754,c_2776]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_16,negated_conjecture,
% 3.71/0.98      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_611,plain,
% 3.71/0.98      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 3.71/0.98      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_14,plain,
% 3.71/0.98      ( ~ v2_tops_1(X0,X1)
% 3.71/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.71/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | ~ l1_pre_topc(X1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_613,plain,
% 3.71/0.98      ( v2_tops_1(X0,X1) != iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.71/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1419,plain,
% 3.71/0.98      ( v2_tops_1(X0,sK0) != iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1301,c_613]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1420,plain,
% 3.71/0.98      ( v2_tops_1(X0,sK0) != iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_1419,c_1301]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1666,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.71/0.98      | v2_tops_1(X0,sK0) != iProver_top ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_1420,c_19]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1667,plain,
% 3.71/0.98      ( v2_tops_1(X0,sK0) != iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(renaming,[status(thm)],[c_1666]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2534,plain,
% 3.71/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.71/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.71/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2037,c_1667]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2982,plain,
% 3.71/0.98      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.71/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_2534,c_1413]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2983,plain,
% 3.71/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.71/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.71/0.98      inference(renaming,[status(thm)],[c_2982]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_12,plain,
% 3.71/0.98      ( ~ v1_tops_1(X0,X1)
% 3.71/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | ~ l1_pre_topc(X1)
% 3.71/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_615,plain,
% 3.71/0.98      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 3.71/0.98      | v1_tops_1(X1,X0) != iProver_top
% 3.71/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2327,plain,
% 3.71/0.98      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.71/0.98      | v1_tops_1(X0,sK0) != iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1301,c_615]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3083,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | v1_tops_1(X0,sK0) != iProver_top
% 3.71/0.98      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_2327,c_19]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3084,plain,
% 3.71/0.98      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.71/0.98      | v1_tops_1(X0,sK0) != iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(renaming,[status(thm)],[c_3083]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3096,plain,
% 3.71/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.71/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2754,c_3084]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5490,plain,
% 3.71/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.71/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2983,c_3096]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5495,plain,
% 3.71/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.71/0.98      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_611,c_5490]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_10,plain,
% 3.71/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | ~ l1_pre_topc(X1)
% 3.71/0.98      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.71/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_617,plain,
% 3.71/0.98      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 3.71/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3263,plain,
% 3.71/0.98      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1301,c_617]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3267,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_3263,c_1301]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3584,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_3267,c_19]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3585,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(renaming,[status(thm)],[c_3584]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3594,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1413,c_3585]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3605,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_3594,c_2037]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5645,plain,
% 3.71/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.71/0.98      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_5495,c_3605]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_4,plain,
% 3.71/0.98      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 3.71/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_623,plain,
% 3.71/0.98      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2,plain,
% 3.71/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.71/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_635,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_623,c_2]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2036,plain,
% 3.71/0.98      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_635,c_624]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_0,plain,
% 3.71/0.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.71/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1,plain,
% 3.71/0.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.71/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_961,plain,
% 3.71/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_2041,plain,
% 3.71/0.98      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_2036,c_961]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5648,plain,
% 3.71/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.71/0.98      inference(demodulation,[status(thm)],[c_5645,c_2041]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5651,plain,
% 3.71/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 3.71/0.98      inference(demodulation,[status(thm)],[c_5648,c_3605]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_6898,plain,
% 3.71/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_6891,c_5651]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_6899,plain,
% 3.71/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.71/0.98      inference(demodulation,[status(thm)],[c_6898,c_2]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_11,plain,
% 3.71/0.98      ( v1_tops_1(X0,X1)
% 3.71/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | ~ l1_pre_topc(X1)
% 3.71/0.98      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_616,plain,
% 3.71/0.98      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 3.71/0.98      | v1_tops_1(X1,X0) = iProver_top
% 3.71/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_7022,plain,
% 3.71/0.98      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.71/0.98      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_6899,c_616]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_7034,plain,
% 3.71/0.98      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.71/0.98      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_7022,c_1301]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_15,negated_conjecture,
% 3.71/0.98      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_612,plain,
% 3.71/0.98      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 3.71/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5653,plain,
% 3.71/0.98      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.71/0.98      inference(demodulation,[status(thm)],[c_5648,c_612]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_5654,plain,
% 3.71/0.98      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 3.71/0.98      inference(equality_resolution_simp,[status(thm)],[c_5653]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_13,plain,
% 3.71/0.98      ( v2_tops_1(X0,X1)
% 3.71/0.98      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.71/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/0.98      | ~ l1_pre_topc(X1) ),
% 3.71/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_614,plain,
% 3.71/0.98      ( v2_tops_1(X0,X1) = iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.71/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.71/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1854,plain,
% 3.71/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_1301,c_614]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_1859,plain,
% 3.71/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.71/0.98      inference(light_normalisation,[status(thm)],[c_1854,c_1301]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3871,plain,
% 3.71/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.71/0.98      | v2_tops_1(X0,sK0) = iProver_top ),
% 3.71/0.98      inference(global_propositional_subsumption,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_1859,c_19]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3872,plain,
% 3.71/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.71/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.71/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(renaming,[status(thm)],[c_3871]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(c_3883,plain,
% 3.71/0.98      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.71/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.71/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.71/0.98      inference(superposition,[status(thm)],[c_2037,c_3872]) ).
% 3.71/0.98  
% 3.71/0.98  cnf(contradiction,plain,
% 3.71/0.98      ( $false ),
% 3.71/0.98      inference(minisat,
% 3.71/0.98                [status(thm)],
% 3.71/0.98                [c_7034,c_5654,c_3883,c_2533,c_1413,c_19]) ).
% 3.71/0.98  
% 3.71/0.98  
% 3.71/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/0.98  
% 3.71/0.98  ------                               Statistics
% 3.71/0.98  
% 3.71/0.98  ------ Selected
% 3.71/0.98  
% 3.71/0.98  total_time:                             0.239
% 3.71/0.98  
%------------------------------------------------------------------------------
