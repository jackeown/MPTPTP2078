%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:43 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 226 expanded)
%              Number of clauses        :   59 ( 107 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  210 ( 480 expanded)
%              Number of equality atoms :  101 ( 177 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_607,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_613,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_613])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1323,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_609])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_617,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2399,plain,
    ( k2_pre_topc(X0,X1) = X1
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(k2_pre_topc(X0,X1),X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_617])).

cnf(c_3147,plain,
    ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_2399])).

cnf(c_788,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1184,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1186,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1184])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1185,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1190,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1185])).

cnf(c_5803,plain,
    ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3147,c_1186,c_1190])).

cnf(c_5811,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_607,c_5803])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_615,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_608,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1119,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),k1_xboole_0))) = k1_tops_1(X0,k1_xboole_0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_608])).

cnf(c_1126,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_613])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_104])).

cnf(c_128,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_105])).

cnf(c_606,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_128])).

cnf(c_1895,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1126,c_606])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1897,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1895,c_3])).

cnf(c_2263,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0))) = k1_tops_1(X0,k1_xboole_0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1119,c_1897])).

cnf(c_2269,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) = k1_tops_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_607,c_2263])).

cnf(c_5818,plain,
    ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_tops_1(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5811,c_2269])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_105])).

cnf(c_605,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_1614,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1126,c_605])).

cnf(c_616,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1894,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_616,c_606])).

cnf(c_2051,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1614,c_1894,c_1897])).

cnf(c_2054,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2051,c_1894])).

cnf(c_5820,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5818,c_2054])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_610,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_826,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_610])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_612,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1002,plain,
    ( k1_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_826,c_612])).

cnf(c_14,negated_conjecture,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1342,plain,
    ( k1_tops_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1002,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5820,c_1342])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.52/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/1.01  
% 3.52/1.01  ------  iProver source info
% 3.52/1.01  
% 3.52/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.52/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/1.01  git: non_committed_changes: false
% 3.52/1.01  git: last_make_outside_of_git: false
% 3.52/1.01  
% 3.52/1.01  ------ 
% 3.52/1.01  ------ Parsing...
% 3.52/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.01  ------ Proving...
% 3.52/1.01  ------ Problem Properties 
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  clauses                                 15
% 3.52/1.01  conjectures                             2
% 3.52/1.01  EPR                                     4
% 3.52/1.01  Horn                                    15
% 3.52/1.01  unary                                   5
% 3.52/1.01  binary                                  6
% 3.52/1.01  lits                                    29
% 3.52/1.01  lits eq                                 7
% 3.52/1.01  fd_pure                                 0
% 3.52/1.01  fd_pseudo                               0
% 3.52/1.01  fd_cond                                 0
% 3.52/1.01  fd_pseudo_cond                          1
% 3.52/1.01  AC symbols                              0
% 3.52/1.01  
% 3.52/1.01  ------ Input Options Time Limit: Unbounded
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  ------ 
% 3.52/1.01  Current options:
% 3.52/1.01  ------ 
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  ------ Proving...
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  % SZS status Theorem for theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  fof(f13,conjecture,(
% 3.52/1.01    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f14,negated_conjecture,(
% 3.52/1.01    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 3.52/1.01    inference(negated_conjecture,[],[f13])).
% 3.52/1.01  
% 3.52/1.01  fof(f24,plain,(
% 3.52/1.01    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 3.52/1.01    inference(ennf_transformation,[],[f14])).
% 3.52/1.01  
% 3.52/1.01  fof(f28,plain,(
% 3.52/1.01    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 3.52/1.01    introduced(choice_axiom,[])).
% 3.52/1.01  
% 3.52/1.01  fof(f29,plain,(
% 3.52/1.01    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 3.52/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).
% 3.52/1.01  
% 3.52/1.01  fof(f44,plain,(
% 3.52/1.01    l1_pre_topc(sK0)),
% 3.52/1.01    inference(cnf_transformation,[],[f29])).
% 3.52/1.01  
% 3.52/1.01  fof(f9,axiom,(
% 3.52/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f19,plain,(
% 3.52/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.52/1.01    inference(ennf_transformation,[],[f9])).
% 3.52/1.01  
% 3.52/1.01  fof(f20,plain,(
% 3.52/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.52/1.01    inference(flattening,[],[f19])).
% 3.52/1.01  
% 3.52/1.01  fof(f40,plain,(
% 3.52/1.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f20])).
% 3.52/1.01  
% 3.52/1.01  fof(f6,axiom,(
% 3.52/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f27,plain,(
% 3.52/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.52/1.01    inference(nnf_transformation,[],[f6])).
% 3.52/1.01  
% 3.52/1.01  fof(f37,plain,(
% 3.52/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f27])).
% 3.52/1.01  
% 3.52/1.01  fof(f38,plain,(
% 3.52/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f27])).
% 3.52/1.01  
% 3.52/1.01  fof(f11,axiom,(
% 3.52/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f22,plain,(
% 3.52/1.01    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.52/1.01    inference(ennf_transformation,[],[f11])).
% 3.52/1.01  
% 3.52/1.01  fof(f42,plain,(
% 3.52/1.01    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f22])).
% 3.52/1.01  
% 3.52/1.01  fof(f1,axiom,(
% 3.52/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f25,plain,(
% 3.52/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/1.01    inference(nnf_transformation,[],[f1])).
% 3.52/1.01  
% 3.52/1.01  fof(f26,plain,(
% 3.52/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/1.01    inference(flattening,[],[f25])).
% 3.52/1.01  
% 3.52/1.01  fof(f32,plain,(
% 3.52/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f26])).
% 3.52/1.01  
% 3.52/1.01  fof(f30,plain,(
% 3.52/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.52/1.01    inference(cnf_transformation,[],[f26])).
% 3.52/1.01  
% 3.52/1.01  fof(f47,plain,(
% 3.52/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/1.01    inference(equality_resolution,[],[f30])).
% 3.52/1.01  
% 3.52/1.01  fof(f5,axiom,(
% 3.52/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f36,plain,(
% 3.52/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f5])).
% 3.52/1.01  
% 3.52/1.01  fof(f12,axiom,(
% 3.52/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f23,plain,(
% 3.52/1.01    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.52/1.01    inference(ennf_transformation,[],[f12])).
% 3.52/1.01  
% 3.52/1.01  fof(f43,plain,(
% 3.52/1.01    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f23])).
% 3.52/1.01  
% 3.52/1.01  fof(f3,axiom,(
% 3.52/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f16,plain,(
% 3.52/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/1.01    inference(ennf_transformation,[],[f3])).
% 3.52/1.01  
% 3.52/1.01  fof(f34,plain,(
% 3.52/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f16])).
% 3.52/1.01  
% 3.52/1.01  fof(f2,axiom,(
% 3.52/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f33,plain,(
% 3.52/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.52/1.01    inference(cnf_transformation,[],[f2])).
% 3.52/1.01  
% 3.52/1.01  fof(f4,axiom,(
% 3.52/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f17,plain,(
% 3.52/1.01    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/1.01    inference(ennf_transformation,[],[f4])).
% 3.52/1.01  
% 3.52/1.01  fof(f35,plain,(
% 3.52/1.01    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f17])).
% 3.52/1.01  
% 3.52/1.01  fof(f10,axiom,(
% 3.52/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f21,plain,(
% 3.52/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.52/1.01    inference(ennf_transformation,[],[f10])).
% 3.52/1.01  
% 3.52/1.01  fof(f41,plain,(
% 3.52/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f21])).
% 3.52/1.01  
% 3.52/1.01  fof(f8,axiom,(
% 3.52/1.01    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 3.52/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f18,plain,(
% 3.52/1.01    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.52/1.01    inference(ennf_transformation,[],[f8])).
% 3.52/1.01  
% 3.52/1.01  fof(f39,plain,(
% 3.52/1.01    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f18])).
% 3.52/1.01  
% 3.52/1.01  fof(f45,plain,(
% 3.52/1.01    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 3.52/1.01    inference(cnf_transformation,[],[f29])).
% 3.52/1.01  
% 3.52/1.01  cnf(c_15,negated_conjecture,
% 3.52/1.01      ( l1_pre_topc(sK0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_607,plain,
% 3.52/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_10,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/1.01      | ~ l1_pre_topc(X1) ),
% 3.52/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_611,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.52/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.52/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_8,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.52/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_613,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.52/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1703,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.52/1.01      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
% 3.52/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_611,c_613]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_7,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_614,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.52/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_12,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.52/1.01      | ~ l1_pre_topc(X1) ),
% 3.52/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_609,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.52/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 3.52/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1323,plain,
% 3.52/1.01      ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 3.52/1.01      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.52/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_614,c_609]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_0,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.52/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_617,plain,
% 3.52/1.01      ( X0 = X1
% 3.52/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.52/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2399,plain,
% 3.52/1.01      ( k2_pre_topc(X0,X1) = X1
% 3.52/1.01      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 3.52/1.01      | r1_tarski(k2_pre_topc(X0,X1),X1) != iProver_top
% 3.52/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1323,c_617]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3147,plain,
% 3.52/1.01      ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
% 3.52/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.52/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top
% 3.52/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1703,c_2399]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_788,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/1.01      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1184,plain,
% 3.52/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.52/1.01      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_788]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1186,plain,
% 3.52/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.52/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_1184]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2,plain,
% 3.52/1.01      ( r1_tarski(X0,X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1185,plain,
% 3.52/1.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1190,plain,
% 3.52/1.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_1185]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5803,plain,
% 3.52/1.01      ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
% 3.52/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.52/1.01      inference(global_propositional_subsumption,
% 3.52/1.01                [status(thm)],
% 3.52/1.01                [c_3147,c_1186,c_1190]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5811,plain,
% 3.52/1.01      ( k2_pre_topc(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_607,c_5803]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_6,plain,
% 3.52/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.52/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_615,plain,
% 3.52/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_13,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/1.01      | ~ l1_pre_topc(X1)
% 3.52/1.01      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_608,plain,
% 3.52/1.01      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 3.52/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.52/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1119,plain,
% 3.52/1.01      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),k1_xboole_0))) = k1_tops_1(X0,k1_xboole_0)
% 3.52/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_615,c_608]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1126,plain,
% 3.52/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_615,c_613]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/1.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_104,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.52/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_105,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.52/1.01      inference(renaming,[status(thm)],[c_104]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_128,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.52/1.01      inference(bin_hyper_res,[status(thm)],[c_4,c_105]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_606,plain,
% 3.52/1.01      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.52/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_128]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1895,plain,
% 3.52/1.01      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1126,c_606]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3,plain,
% 3.52/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1897,plain,
% 3.52/1.01      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_1895,c_3]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2263,plain,
% 3.52/1.01      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0))) = k1_tops_1(X0,k1_xboole_0)
% 3.52/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_1119,c_1897]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2269,plain,
% 3.52/1.01      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) = k1_tops_1(sK0,k1_xboole_0) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_607,c_2263]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5818,plain,
% 3.52/1.01      ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_tops_1(sK0,k1_xboole_0) ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_5811,c_2269]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/1.01      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_129,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.52/1.01      inference(bin_hyper_res,[status(thm)],[c_5,c_105]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_605,plain,
% 3.52/1.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.52/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1614,plain,
% 3.52/1.01      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1126,c_605]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_616,plain,
% 3.52/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1894,plain,
% 3.52/1.01      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_616,c_606]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2051,plain,
% 3.52/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_1614,c_1894,c_1897]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2054,plain,
% 3.52/1.01      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_2051,c_1894]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5820,plain,
% 3.52/1.01      ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_5818,c_2054]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_11,plain,
% 3.52/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_610,plain,
% 3.52/1.01      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_826,plain,
% 3.52/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_607,c_610]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_9,plain,
% 3.52/1.01      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_612,plain,
% 3.52/1.01      ( k1_struct_0(X0) = k1_xboole_0 | l1_struct_0(X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1002,plain,
% 3.52/1.01      ( k1_struct_0(sK0) = k1_xboole_0 ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_826,c_612]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_14,negated_conjecture,
% 3.52/1.01      ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
% 3.52/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1342,plain,
% 3.52/1.01      ( k1_tops_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_1002,c_14]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(contradiction,plain,
% 3.52/1.01      ( $false ),
% 3.52/1.01      inference(minisat,[status(thm)],[c_5820,c_1342]) ).
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  ------                               Statistics
% 3.52/1.01  
% 3.52/1.01  ------ Selected
% 3.52/1.01  
% 3.52/1.01  total_time:                             0.202
% 3.52/1.01  
%------------------------------------------------------------------------------
