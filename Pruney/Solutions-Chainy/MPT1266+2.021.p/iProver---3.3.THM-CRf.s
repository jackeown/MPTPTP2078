%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:01 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  130 (1329 expanded)
%              Number of clauses        :   82 ( 478 expanded)
%              Number of leaves         :   14 ( 284 expanded)
%              Depth                    :   24
%              Number of atoms          :  332 (4706 expanded)
%              Number of equality atoms :  182 (1787 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
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

fof(f49,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_594,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_603,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_989,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_603])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_605,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1098,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_989,c_605])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_595,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_609,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1234,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_595,c_609])).

cnf(c_1507,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1098,c_1234])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_608,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2008,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_608])).

cnf(c_1508,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1098,c_595])).

cnf(c_2712,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2008,c_1508])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_604])).

cnf(c_2323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2305,c_1098])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2725,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2323,c_17])).

cnf(c_2726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2725])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_607,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2734,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2726,c_607])).

cnf(c_6009,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_2712,c_2734])).

cnf(c_14,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_596,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_598,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1504,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_598])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1783,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_17,c_18])).

cnf(c_1787,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1783,c_1098])).

cnf(c_10,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_600,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2344,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_600])).

cnf(c_2823,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2344,c_17])).

cnf(c_2824,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2823])).

cnf(c_2835,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_2824])).

cnf(c_5591,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_2835])).

cnf(c_5596,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_596,c_5591])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_602,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3215,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_602])).

cnf(c_3219,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3215,c_1098])).

cnf(c_3695,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3219,c_17])).

cnf(c_3696,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3695])).

cnf(c_3705,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1508,c_3696])).

cnf(c_3720,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3705,c_1507])).

cnf(c_5679,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5596,c_3720])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_606,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1223,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_607])).

cnf(c_1233,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_606,c_609])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1238,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1233,c_0])).

cnf(c_3324,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1223,c_1238])).

cnf(c_5682,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5679,c_3324])).

cnf(c_5685,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5682,c_3720])).

cnf(c_9296,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6009,c_5685])).

cnf(c_9297,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_9296,c_1238])).

cnf(c_9,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_601,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9304,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9297,c_601])).

cnf(c_9316,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9304,c_1098])).

cnf(c_13,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_597,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5687,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5682,c_597])).

cnf(c_5688,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5687])).

cnf(c_11,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_599,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1980,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_599])).

cnf(c_1985,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1980,c_1098])).

cnf(c_2971,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1985,c_17])).

cnf(c_2972,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2971])).

cnf(c_2982,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_2972])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9316,c_5688,c_2982,c_2008,c_1508,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:11:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.65/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.98  
% 3.65/0.98  ------  iProver source info
% 3.65/0.98  
% 3.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.98  git: non_committed_changes: false
% 3.65/0.98  git: last_make_outside_of_git: false
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  ------ Parsing...
% 3.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.98  ------ Proving...
% 3.65/0.98  ------ Problem Properties 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  clauses                                 17
% 3.65/0.98  conjectures                             4
% 3.65/0.98  EPR                                     2
% 3.65/0.98  Horn                                    16
% 3.65/0.98  unary                                   4
% 3.65/0.98  binary                                  7
% 3.65/0.98  lits                                    40
% 3.65/0.98  lits eq                                 9
% 3.65/0.98  fd_pure                                 0
% 3.65/0.98  fd_pseudo                               0
% 3.65/0.98  fd_cond                                 0
% 3.65/0.98  fd_pseudo_cond                          0
% 3.65/0.98  AC symbols                              0
% 3.65/0.98  
% 3.65/0.98  ------ Input Options Time Limit: Unbounded
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  Current options:
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ Proving...
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS status Theorem for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  fof(f13,conjecture,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f14,negated_conjecture,(
% 3.65/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.65/0.98    inference(negated_conjecture,[],[f13])).
% 3.65/0.98  
% 3.65/0.98  fof(f26,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f14])).
% 3.65/0.98  
% 3.65/0.98  fof(f29,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f26])).
% 3.65/0.98  
% 3.65/0.98  fof(f30,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f29])).
% 3.65/0.98  
% 3.65/0.98  fof(f32,plain,(
% 3.65/0.98    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f31,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f33,plain,(
% 3.65/0.98    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 3.65/0.98  
% 3.65/0.98  fof(f47,plain,(
% 3.65/0.98    l1_pre_topc(sK0)),
% 3.65/0.98    inference(cnf_transformation,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f9,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f22,plain,(
% 3.65/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f9])).
% 3.65/0.98  
% 3.65/0.98  fof(f41,plain,(
% 3.65/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f22])).
% 3.65/0.98  
% 3.65/0.98  fof(f7,axiom,(
% 3.65/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f19,plain,(
% 3.65/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f7])).
% 3.65/0.98  
% 3.65/0.98  fof(f39,plain,(
% 3.65/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f19])).
% 3.65/0.98  
% 3.65/0.98  fof(f48,plain,(
% 3.65/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.65/0.98    inference(cnf_transformation,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f2,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f16,plain,(
% 3.65/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f2])).
% 3.65/0.98  
% 3.65/0.98  fof(f35,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f16])).
% 3.65/0.98  
% 3.65/0.98  fof(f3,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f17,plain,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f3])).
% 3.65/0.98  
% 3.65/0.98  fof(f36,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f17])).
% 3.65/0.98  
% 3.65/0.98  fof(f8,axiom,(
% 3.65/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f20,plain,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f8])).
% 3.65/0.98  
% 3.65/0.98  fof(f21,plain,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f20])).
% 3.65/0.98  
% 3.65/0.98  fof(f40,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f21])).
% 3.65/0.98  
% 3.65/0.98  fof(f4,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f18,plain,(
% 3.65/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f4])).
% 3.65/0.98  
% 3.65/0.98  fof(f37,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f18])).
% 3.65/0.98  
% 3.65/0.98  fof(f49,plain,(
% 3.65/0.98    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 3.65/0.98    inference(cnf_transformation,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f12,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f25,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f12])).
% 3.65/0.98  
% 3.65/0.98  fof(f28,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f25])).
% 3.65/0.98  
% 3.65/0.98  fof(f45,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f28])).
% 3.65/0.98  
% 3.65/0.98  fof(f11,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f24,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f11])).
% 3.65/0.98  
% 3.65/0.98  fof(f27,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f24])).
% 3.65/0.98  
% 3.65/0.98  fof(f43,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f10,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f23,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f10])).
% 3.65/0.98  
% 3.65/0.98  fof(f42,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f23])).
% 3.65/0.98  
% 3.65/0.98  fof(f5,axiom,(
% 3.65/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f38,plain,(
% 3.65/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f5])).
% 3.65/0.98  
% 3.65/0.98  fof(f1,axiom,(
% 3.65/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f34,plain,(
% 3.65/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f1])).
% 3.65/0.98  
% 3.65/0.98  fof(f44,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f50,plain,(
% 3.65/0.98    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 3.65/0.98    inference(cnf_transformation,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f46,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f28])).
% 3.65/0.98  
% 3.65/0.98  cnf(c_16,negated_conjecture,
% 3.65/0.98      ( l1_pre_topc(sK0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_594,plain,
% 3.65/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7,plain,
% 3.65/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_603,plain,
% 3.65/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_989,plain,
% 3.65/0.98      ( l1_struct_0(sK0) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_594,c_603]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5,plain,
% 3.65/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_605,plain,
% 3.65/0.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.65/0.98      | l1_struct_0(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1098,plain,
% 3.65/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_989,c_605]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_15,negated_conjecture,
% 3.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.65/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_595,plain,
% 3.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_609,plain,
% 3.65/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1234,plain,
% 3.65/0.98      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_595,c_609]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1507,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_1098,c_1234]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_608,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.65/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2008,plain,
% 3.65/0.98      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.65/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1507,c_608]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1508,plain,
% 3.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_1098,c_595]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2712,plain,
% 3.65/0.98      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_2008,c_1508]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_604,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2305,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1098,c_604]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2323,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_2305,c_1098]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_17,plain,
% 3.65/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2725,plain,
% 3.65/0.98      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_2323,c_17]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2726,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_2725]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_607,plain,
% 3.65/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2734,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2726,c_607]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6009,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2712,c_2734]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_14,negated_conjecture,
% 3.65/0.98      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_596,plain,
% 3.65/0.98      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 3.65/0.98      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12,plain,
% 3.65/0.98      ( ~ v2_tops_1(X0,X1)
% 3.65/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_598,plain,
% 3.65/0.98      ( v2_tops_1(X0,X1) != iProver_top
% 3.65/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1504,plain,
% 3.65/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.65/0.98      | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 3.65/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1234,c_598]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_18,plain,
% 3.65/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1783,plain,
% 3.65/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.65/0.98      | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_1504,c_17,c_18]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1787,plain,
% 3.65/0.98      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.65/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_1783,c_1098]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_10,plain,
% 3.65/0.98      ( ~ v1_tops_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_600,plain,
% 3.65/0.98      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 3.65/0.98      | v1_tops_1(X1,X0) != iProver_top
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2344,plain,
% 3.65/0.98      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.65/0.98      | v1_tops_1(X0,sK0) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1098,c_600]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2823,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | v1_tops_1(X0,sK0) != iProver_top
% 3.65/0.98      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_2344,c_17]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2824,plain,
% 3.65/0.98      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.65/0.98      | v1_tops_1(X0,sK0) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_2823]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2835,plain,
% 3.65/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.65/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2712,c_2824]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5591,plain,
% 3.65/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.65/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1787,c_2835]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5596,plain,
% 3.65/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.65/0.98      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_596,c_5591]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_602,plain,
% 3.65/0.98      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3215,plain,
% 3.65/0.98      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1098,c_602]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3219,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_3215,c_1098]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3695,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3219,c_17]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3696,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_3695]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3705,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1508,c_3696]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3720,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_3705,c_1507]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5679,plain,
% 3.65/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.65/0.98      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_5596,c_3720]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4,plain,
% 3.65/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_606,plain,
% 3.65/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1223,plain,
% 3.65/0.98      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_606,c_607]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1233,plain,
% 3.65/0.98      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_606,c_609]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_0,plain,
% 3.65/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1238,plain,
% 3.65/0.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_1233,c_0]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3324,plain,
% 3.65/0.98      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_1223,c_1238]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5682,plain,
% 3.65/0.98      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_5679,c_3324]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5685,plain,
% 3.65/0.98      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_5682,c_3720]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9296,plain,
% 3.65/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_6009,c_5685]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9297,plain,
% 3.65/0.98      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_9296,c_1238]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9,plain,
% 3.65/0.98      ( v1_tops_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_601,plain,
% 3.65/0.98      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 3.65/0.98      | v1_tops_1(X1,X0) = iProver_top
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9304,plain,
% 3.65/0.98      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.65/0.98      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_9297,c_601]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9316,plain,
% 3.65/0.98      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.65/0.98      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_9304,c_1098]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13,negated_conjecture,
% 3.65/0.98      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_597,plain,
% 3.65/0.98      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 3.65/0.98      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5687,plain,
% 3.65/0.98      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_5682,c_597]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5688,plain,
% 3.65/0.98      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 3.65/0.98      inference(equality_resolution_simp,[status(thm)],[c_5687]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11,plain,
% 3.65/0.98      ( v2_tops_1(X0,X1)
% 3.65/0.98      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_599,plain,
% 3.65/0.98      ( v2_tops_1(X0,X1) = iProver_top
% 3.65/0.98      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1980,plain,
% 3.65/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.65/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1098,c_599]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1985,plain,
% 3.65/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.65/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_1980,c_1098]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2971,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.65/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.65/0.98      | v2_tops_1(X0,sK0) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_1985,c_17]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2972,plain,
% 3.65/0.98      ( v2_tops_1(X0,sK0) = iProver_top
% 3.65/0.98      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_2971]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2982,plain,
% 3.65/0.98      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.65/0.98      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.65/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1507,c_2972]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(contradiction,plain,
% 3.65/0.98      ( $false ),
% 3.65/0.98      inference(minisat,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_9316,c_5688,c_2982,c_2008,c_1508,c_17]) ).
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  ------                               Statistics
% 3.65/0.98  
% 3.65/0.98  ------ Selected
% 3.65/0.98  
% 3.65/0.98  total_time:                             0.283
% 3.65/0.98  
%------------------------------------------------------------------------------
