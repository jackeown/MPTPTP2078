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
% DateTime   : Thu Dec  3 12:15:00 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.28s
% Verified   : 
% Statistics : Number of formulae       :  137 (1693 expanded)
%              Number of clauses        :   86 ( 613 expanded)
%              Number of leaves         :   15 ( 358 expanded)
%              Depth                    :   29
%              Number of atoms          :  357 (5941 expanded)
%              Number of equality atoms :  211 (2269 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f33,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f50,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f53,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_575,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_563,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_561,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_570,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_952,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_561,c_570])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_572,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1051,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_952,c_572])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_562,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1528,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1051,c_562])).

cnf(c_11,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_565,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1534,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_565])).

cnf(c_1535,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1534,c_1051])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1778,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1535,c_16])).

cnf(c_1779,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1778])).

cnf(c_9,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_567,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2543,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_567])).

cnf(c_2702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2543,c_16])).

cnf(c_2703,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2702])).

cnf(c_2711,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_575,c_2703])).

cnf(c_11273,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_2711])).

cnf(c_14965,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_11273])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_571,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2385,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_571])).

cnf(c_2396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2385,c_1051])).

cnf(c_2689,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2396,c_16])).

cnf(c_2690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2689])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_574,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2697,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_574])).

cnf(c_3105,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_575,c_2697])).

cnf(c_12222,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_1528,c_3105])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_569,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3202,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_569])).

cnf(c_3206,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3202,c_1051])).

cnf(c_4110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3206,c_16])).

cnf(c_4111,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4110])).

cnf(c_4121,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1528,c_4111])).

cnf(c_12255,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_12222,c_4121])).

cnf(c_15035,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14965,c_12255])).

cnf(c_15072,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_563,c_15035])).

cnf(c_4450,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4121,c_575])).

cnf(c_4475,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_4450])).

cnf(c_6578,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_575,c_4475])).

cnf(c_7251,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6578,c_1528])).

cnf(c_7257,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7251,c_574])).

cnf(c_15338,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_15072,c_7257])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_573,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1211,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_573,c_574])).

cnf(c_0,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1216,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1211,c_0])).

cnf(c_15341,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15338,c_1216])).

cnf(c_8,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_568,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12588,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12255,c_568])).

cnf(c_12611,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12588,c_1051])).

cnf(c_12947,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12611,c_16])).

cnf(c_12948,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12947])).

cnf(c_15346,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15341,c_12948])).

cnf(c_15367,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15346,c_0])).

cnf(c_15368,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15367])).

cnf(c_15624,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_575,c_15368])).

cnf(c_17007,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15624,c_1528])).

cnf(c_10,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_566,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2184,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_566])).

cnf(c_2189,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2184,c_1051])).

cnf(c_2842,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_16])).

cnf(c_2843,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2842])).

cnf(c_17013,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17007,c_2843])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_564,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15354,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15341,c_564])).

cnf(c_15355,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15354])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17013,c_15355,c_1528])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:46:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.28/2.08  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.08  
% 8.28/2.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.28/2.08  
% 8.28/2.08  ------  iProver source info
% 8.28/2.08  
% 8.28/2.08  git: date: 2020-06-30 10:37:57 +0100
% 8.28/2.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.28/2.08  git: non_committed_changes: false
% 8.28/2.08  git: last_make_outside_of_git: false
% 8.28/2.08  
% 8.28/2.08  ------ 
% 8.28/2.08  ------ Parsing...
% 8.28/2.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.28/2.08  
% 8.28/2.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.28/2.08  
% 8.28/2.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.28/2.08  
% 8.28/2.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.28/2.08  ------ Proving...
% 8.28/2.08  ------ Problem Properties 
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  clauses                                 16
% 8.28/2.08  conjectures                             4
% 8.28/2.08  EPR                                     2
% 8.28/2.08  Horn                                    15
% 8.28/2.08  unary                                   4
% 8.28/2.08  binary                                  6
% 8.28/2.08  lits                                    38
% 8.28/2.08  lits eq                                 8
% 8.28/2.08  fd_pure                                 0
% 8.28/2.08  fd_pseudo                               0
% 8.28/2.08  fd_cond                                 0
% 8.28/2.08  fd_pseudo_cond                          0
% 8.28/2.08  AC symbols                              0
% 8.28/2.08  
% 8.28/2.08  ------ Input Options Time Limit: Unbounded
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  ------ 
% 8.28/2.08  Current options:
% 8.28/2.08  ------ 
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  ------ Proving...
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  % SZS status Theorem for theBenchmark.p
% 8.28/2.08  
% 8.28/2.08  % SZS output start CNFRefutation for theBenchmark.p
% 8.28/2.08  
% 8.28/2.08  fof(f3,axiom,(
% 8.28/2.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f17,plain,(
% 8.28/2.08    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.28/2.08    inference(ennf_transformation,[],[f3])).
% 8.28/2.08  
% 8.28/2.08  fof(f36,plain,(
% 8.28/2.08    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.28/2.08    inference(cnf_transformation,[],[f17])).
% 8.28/2.08  
% 8.28/2.08  fof(f14,conjecture,(
% 8.28/2.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f15,negated_conjecture,(
% 8.28/2.08    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 8.28/2.08    inference(negated_conjecture,[],[f14])).
% 8.28/2.08  
% 8.28/2.08  fof(f26,plain,(
% 8.28/2.08    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.28/2.08    inference(ennf_transformation,[],[f15])).
% 8.28/2.08  
% 8.28/2.08  fof(f29,plain,(
% 8.28/2.08    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.28/2.08    inference(nnf_transformation,[],[f26])).
% 8.28/2.08  
% 8.28/2.08  fof(f30,plain,(
% 8.28/2.08    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.28/2.08    inference(flattening,[],[f29])).
% 8.28/2.08  
% 8.28/2.08  fof(f32,plain,(
% 8.28/2.08    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.28/2.08    introduced(choice_axiom,[])).
% 8.28/2.08  
% 8.28/2.08  fof(f31,plain,(
% 8.28/2.08    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 8.28/2.08    introduced(choice_axiom,[])).
% 8.28/2.08  
% 8.28/2.08  fof(f33,plain,(
% 8.28/2.08    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 8.28/2.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 8.28/2.08  
% 8.28/2.08  fof(f50,plain,(
% 8.28/2.08    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 8.28/2.08    inference(cnf_transformation,[],[f33])).
% 8.28/2.08  
% 8.28/2.08  fof(f48,plain,(
% 8.28/2.08    l1_pre_topc(sK0)),
% 8.28/2.08    inference(cnf_transformation,[],[f33])).
% 8.28/2.08  
% 8.28/2.08  fof(f10,axiom,(
% 8.28/2.08    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f22,plain,(
% 8.28/2.08    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(ennf_transformation,[],[f10])).
% 8.28/2.08  
% 8.28/2.08  fof(f42,plain,(
% 8.28/2.08    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f22])).
% 8.28/2.08  
% 8.28/2.08  fof(f8,axiom,(
% 8.28/2.08    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f19,plain,(
% 8.28/2.08    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 8.28/2.08    inference(ennf_transformation,[],[f8])).
% 8.28/2.08  
% 8.28/2.08  fof(f40,plain,(
% 8.28/2.08    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f19])).
% 8.28/2.08  
% 8.28/2.08  fof(f49,plain,(
% 8.28/2.08    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.28/2.08    inference(cnf_transformation,[],[f33])).
% 8.28/2.08  
% 8.28/2.08  fof(f13,axiom,(
% 8.28/2.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f25,plain,(
% 8.28/2.08    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(ennf_transformation,[],[f13])).
% 8.28/2.08  
% 8.28/2.08  fof(f28,plain,(
% 8.28/2.08    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(nnf_transformation,[],[f25])).
% 8.28/2.08  
% 8.28/2.08  fof(f46,plain,(
% 8.28/2.08    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f28])).
% 8.28/2.08  
% 8.28/2.08  fof(f12,axiom,(
% 8.28/2.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f24,plain,(
% 8.28/2.08    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(ennf_transformation,[],[f12])).
% 8.28/2.08  
% 8.28/2.08  fof(f27,plain,(
% 8.28/2.08    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(nnf_transformation,[],[f24])).
% 8.28/2.08  
% 8.28/2.08  fof(f44,plain,(
% 8.28/2.08    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f27])).
% 8.28/2.08  
% 8.28/2.08  fof(f9,axiom,(
% 8.28/2.08    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f20,plain,(
% 8.28/2.08    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.28/2.08    inference(ennf_transformation,[],[f9])).
% 8.28/2.08  
% 8.28/2.08  fof(f21,plain,(
% 8.28/2.08    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(flattening,[],[f20])).
% 8.28/2.08  
% 8.28/2.08  fof(f41,plain,(
% 8.28/2.08    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f21])).
% 8.28/2.08  
% 8.28/2.08  fof(f4,axiom,(
% 8.28/2.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f18,plain,(
% 8.28/2.08    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.28/2.08    inference(ennf_transformation,[],[f4])).
% 8.28/2.08  
% 8.28/2.08  fof(f37,plain,(
% 8.28/2.08    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.28/2.08    inference(cnf_transformation,[],[f18])).
% 8.28/2.08  
% 8.28/2.08  fof(f11,axiom,(
% 8.28/2.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f23,plain,(
% 8.28/2.08    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.28/2.08    inference(ennf_transformation,[],[f11])).
% 8.28/2.08  
% 8.28/2.08  fof(f43,plain,(
% 8.28/2.08    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f23])).
% 8.28/2.08  
% 8.28/2.08  fof(f6,axiom,(
% 8.28/2.08    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f39,plain,(
% 8.28/2.08    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.28/2.08    inference(cnf_transformation,[],[f6])).
% 8.28/2.08  
% 8.28/2.08  fof(f2,axiom,(
% 8.28/2.08    ! [X0] : k2_subset_1(X0) = X0),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f35,plain,(
% 8.28/2.08    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 8.28/2.08    inference(cnf_transformation,[],[f2])).
% 8.28/2.08  
% 8.28/2.08  fof(f5,axiom,(
% 8.28/2.08    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f38,plain,(
% 8.28/2.08    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 8.28/2.08    inference(cnf_transformation,[],[f5])).
% 8.28/2.08  
% 8.28/2.08  fof(f1,axiom,(
% 8.28/2.08    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 8.28/2.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.28/2.08  
% 8.28/2.08  fof(f34,plain,(
% 8.28/2.08    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 8.28/2.08    inference(cnf_transformation,[],[f1])).
% 8.28/2.08  
% 8.28/2.08  fof(f52,plain,(
% 8.28/2.08    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 8.28/2.08    inference(definition_unfolding,[],[f38,f34])).
% 8.28/2.08  
% 8.28/2.08  fof(f53,plain,(
% 8.28/2.08    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 8.28/2.08    inference(definition_unfolding,[],[f35,f52])).
% 8.28/2.08  
% 8.28/2.08  fof(f45,plain,(
% 8.28/2.08    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f27])).
% 8.28/2.08  
% 8.28/2.08  fof(f47,plain,(
% 8.28/2.08    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.28/2.08    inference(cnf_transformation,[],[f28])).
% 8.28/2.08  
% 8.28/2.08  fof(f51,plain,(
% 8.28/2.08    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 8.28/2.08    inference(cnf_transformation,[],[f33])).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1,plain,
% 8.28/2.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.28/2.08      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 8.28/2.08      inference(cnf_transformation,[],[f36]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_575,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_13,negated_conjecture,
% 8.28/2.08      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f50]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_563,plain,
% 8.28/2.08      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 8.28/2.08      | v2_tops_1(sK1,sK0) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15,negated_conjecture,
% 8.28/2.08      ( l1_pre_topc(sK0) ),
% 8.28/2.08      inference(cnf_transformation,[],[f48]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_561,plain,
% 8.28/2.08      ( l1_pre_topc(sK0) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_6,plain,
% 8.28/2.08      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 8.28/2.08      inference(cnf_transformation,[],[f42]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_570,plain,
% 8.28/2.08      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_952,plain,
% 8.28/2.08      ( l1_struct_0(sK0) = iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_561,c_570]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_4,plain,
% 8.28/2.08      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 8.28/2.08      inference(cnf_transformation,[],[f40]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_572,plain,
% 8.28/2.08      ( u1_struct_0(X0) = k2_struct_0(X0)
% 8.28/2.08      | l1_struct_0(X0) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1051,plain,
% 8.28/2.08      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_952,c_572]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_14,negated_conjecture,
% 8.28/2.08      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.28/2.08      inference(cnf_transformation,[],[f49]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_562,plain,
% 8.28/2.08      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1528,plain,
% 8.28/2.08      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 8.28/2.08      inference(demodulation,[status(thm)],[c_1051,c_562]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_11,plain,
% 8.28/2.08      ( ~ v2_tops_1(X0,X1)
% 8.28/2.08      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 8.28/2.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | ~ l1_pre_topc(X1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f46]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_565,plain,
% 8.28/2.08      ( v2_tops_1(X0,X1) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.28/2.08      | l1_pre_topc(X1) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1534,plain,
% 8.28/2.08      ( v2_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1051,c_565]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1535,plain,
% 8.28/2.08      ( v2_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_1534,c_1051]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_16,plain,
% 8.28/2.08      ( l1_pre_topc(sK0) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1778,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 8.28/2.08      | v2_tops_1(X0,sK0) != iProver_top ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_1535,c_16]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1779,plain,
% 8.28/2.08      ( v2_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(renaming,[status(thm)],[c_1778]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_9,plain,
% 8.28/2.08      ( ~ v1_tops_1(X0,X1)
% 8.28/2.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | ~ l1_pre_topc(X1)
% 8.28/2.08      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f44]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_567,plain,
% 8.28/2.08      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 8.28/2.08      | v1_tops_1(X1,X0) != iProver_top
% 8.28/2.08      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(X0) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2543,plain,
% 8.28/2.08      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1051,c_567]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2702,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | v1_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_2543,c_16]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2703,plain,
% 8.28/2.08      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(renaming,[status(thm)],[c_2702]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2711,plain,
% 8.28/2.08      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_575,c_2703]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_11273,plain,
% 8.28/2.08      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 8.28/2.08      | v2_tops_1(X0,sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1779,c_2711]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_14965,plain,
% 8.28/2.08      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 8.28/2.08      | v2_tops_1(sK1,sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1528,c_11273]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_5,plain,
% 8.28/2.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | ~ l1_pre_topc(X1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f41]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_571,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.28/2.08      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.28/2.08      | l1_pre_topc(X1) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2385,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.28/2.08      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1051,c_571]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2396,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_2385,c_1051]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2689,plain,
% 8.28/2.08      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_2396,c_16]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2690,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 8.28/2.08      inference(renaming,[status(thm)],[c_2689]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2,plain,
% 8.28/2.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.28/2.08      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 8.28/2.08      inference(cnf_transformation,[],[f37]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_574,plain,
% 8.28/2.08      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 8.28/2.08      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2697,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_2690,c_574]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_3105,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_575,c_2697]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12222,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1528,c_3105]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_7,plain,
% 8.28/2.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | ~ l1_pre_topc(X1)
% 8.28/2.08      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 8.28/2.08      inference(cnf_transformation,[],[f43]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_569,plain,
% 8.28/2.08      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 8.28/2.08      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(X0) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_3202,plain,
% 8.28/2.08      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1051,c_569]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_3206,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_3202,c_1051]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_4110,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_3206,c_16]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_4111,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(renaming,[status(thm)],[c_4110]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_4121,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1528,c_4111]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12255,plain,
% 8.28/2.08      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_12222,c_4121]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15035,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_struct_0(sK0)
% 8.28/2.08      | v2_tops_1(sK1,sK0) != iProver_top ),
% 8.28/2.08      inference(demodulation,[status(thm)],[c_14965,c_12255]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15072,plain,
% 8.28/2.08      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 8.28/2.08      | k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_struct_0(sK0) ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_563,c_15035]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_4450,plain,
% 8.28/2.08      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 8.28/2.08      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_4121,c_575]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_4475,plain,
% 8.28/2.08      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_2690,c_4450]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_6578,plain,
% 8.28/2.08      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 8.28/2.08      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_575,c_4475]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_7251,plain,
% 8.28/2.08      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_6578,c_1528]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_7257,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_7251,c_574]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15338,plain,
% 8.28/2.08      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 8.28/2.08      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_15072,c_7257]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_3,plain,
% 8.28/2.08      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 8.28/2.08      inference(cnf_transformation,[],[f39]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_573,plain,
% 8.28/2.08      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1211,plain,
% 8.28/2.08      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_573,c_574]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_0,plain,
% 8.28/2.08      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 8.28/2.08      inference(cnf_transformation,[],[f53]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_1216,plain,
% 8.28/2.08      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_1211,c_0]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15341,plain,
% 8.28/2.08      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 8.28/2.08      inference(demodulation,[status(thm)],[c_15338,c_1216]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_8,plain,
% 8.28/2.08      ( v1_tops_1(X0,X1)
% 8.28/2.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | ~ l1_pre_topc(X1)
% 8.28/2.08      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f45]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_568,plain,
% 8.28/2.08      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 8.28/2.08      | v1_tops_1(X1,X0) = iProver_top
% 8.28/2.08      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(X0) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12588,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_12255,c_568]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12611,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_12588,c_1051]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12947,plain,
% 8.28/2.08      ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0) ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_12611,c_16]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12948,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) != k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(renaming,[status(thm)],[c_12947]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15346,plain,
% 8.28/2.08      ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) != k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(demodulation,[status(thm)],[c_15341,c_12948]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15367,plain,
% 8.28/2.08      ( k2_struct_0(sK0) != k2_struct_0(sK0)
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(demodulation,[status(thm)],[c_15346,c_0]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15368,plain,
% 8.28/2.08      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(equality_resolution_simp,[status(thm)],[c_15367]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15624,plain,
% 8.28/2.08      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_575,c_15368]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_17007,plain,
% 8.28/2.08      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_15624,c_1528]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_10,plain,
% 8.28/2.08      ( v2_tops_1(X0,X1)
% 8.28/2.08      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 8.28/2.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.28/2.08      | ~ l1_pre_topc(X1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f47]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_566,plain,
% 8.28/2.08      ( v2_tops_1(X0,X1) = iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.28/2.08      | l1_pre_topc(X1) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2184,plain,
% 8.28/2.08      ( v2_tops_1(X0,sK0) = iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_1051,c_566]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2189,plain,
% 8.28/2.08      ( v2_tops_1(X0,sK0) = iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | l1_pre_topc(sK0) != iProver_top ),
% 8.28/2.08      inference(light_normalisation,[status(thm)],[c_2184,c_1051]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2842,plain,
% 8.28/2.08      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 8.28/2.08      | v2_tops_1(X0,sK0) = iProver_top ),
% 8.28/2.08      inference(global_propositional_subsumption,
% 8.28/2.08                [status(thm)],
% 8.28/2.08                [c_2189,c_16]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_2843,plain,
% 8.28/2.08      ( v2_tops_1(X0,sK0) = iProver_top
% 8.28/2.08      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 8.28/2.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(renaming,[status(thm)],[c_2842]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_17013,plain,
% 8.28/2.08      ( v2_tops_1(sK1,sK0) = iProver_top
% 8.28/2.08      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 8.28/2.08      inference(superposition,[status(thm)],[c_17007,c_2843]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_12,negated_conjecture,
% 8.28/2.08      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 8.28/2.08      inference(cnf_transformation,[],[f51]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_564,plain,
% 8.28/2.08      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 8.28/2.08      | v2_tops_1(sK1,sK0) != iProver_top ),
% 8.28/2.08      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15354,plain,
% 8.28/2.08      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 8.28/2.08      inference(demodulation,[status(thm)],[c_15341,c_564]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(c_15355,plain,
% 8.28/2.08      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 8.28/2.08      inference(equality_resolution_simp,[status(thm)],[c_15354]) ).
% 8.28/2.08  
% 8.28/2.08  cnf(contradiction,plain,
% 8.28/2.08      ( $false ),
% 8.28/2.08      inference(minisat,[status(thm)],[c_17013,c_15355,c_1528]) ).
% 8.28/2.08  
% 8.28/2.08  
% 8.28/2.08  % SZS output end CNFRefutation for theBenchmark.p
% 8.28/2.08  
% 8.28/2.08  ------                               Statistics
% 8.28/2.08  
% 8.28/2.08  ------ Selected
% 8.28/2.08  
% 8.28/2.08  total_time:                             1.509
% 8.28/2.08  
%------------------------------------------------------------------------------
