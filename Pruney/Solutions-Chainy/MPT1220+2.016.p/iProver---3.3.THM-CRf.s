%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:27 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 123 expanded)
%              Number of clauses        :   48 (  56 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 ( 268 expanded)
%              Number of equality atoms :   81 ( 112 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,
    ( ? [X0] :
        ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f25])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_559,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_562,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_897,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_559,c_562])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_567,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_578,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_567,c_3])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_561,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1975,plain,
    ( k4_subset_1(u1_struct_0(X0),u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),u1_struct_0(X0))) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_561])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_568,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_96,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_95])).

cnf(c_118,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_96])).

cnf(c_558,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_595,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_558,c_3])).

cnf(c_1130,plain,
    ( k4_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_568,c_595])).

cnf(c_1978,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1975,c_1130])).

cnf(c_2525,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_897,c_1978])).

cnf(c_13,negated_conjecture,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2527,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) != u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2525,c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_563,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_564,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1948,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_564])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1010,plain,
    ( r1_tarski(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_560])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_569,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1480,plain,
    ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
    | r1_tarski(k2_pre_topc(X0,u1_struct_0(X0)),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_569])).

cnf(c_2186,plain,
    ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1948,c_1480])).

cnf(c_2188,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) = u1_struct_0(sK1)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_1053,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1058,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_1060,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_759,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1052,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1054,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_1056,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_15,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2527,c_2188,c_1060,c_1056,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:35:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.76/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/0.98  
% 2.76/0.98  ------  iProver source info
% 2.76/0.98  
% 2.76/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.76/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/0.98  git: non_committed_changes: false
% 2.76/0.98  git: last_make_outside_of_git: false
% 2.76/0.98  
% 2.76/0.98  ------ 
% 2.76/0.98  ------ Parsing...
% 2.76/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/0.98  ------ Proving...
% 2.76/0.98  ------ Problem Properties 
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  clauses                                 14
% 2.76/0.98  conjectures                             2
% 2.76/0.98  EPR                                     4
% 2.76/0.98  Horn                                    14
% 2.76/0.98  unary                                   6
% 2.76/0.98  binary                                  4
% 2.76/0.98  lits                                    26
% 2.76/0.98  lits eq                                 5
% 2.76/0.98  fd_pure                                 0
% 2.76/0.98  fd_pseudo                               0
% 2.76/0.98  fd_cond                                 0
% 2.76/0.98  fd_pseudo_cond                          1
% 2.76/0.98  AC symbols                              0
% 2.76/0.98  
% 2.76/0.98  ------ Input Options Time Limit: Unbounded
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  ------ 
% 2.76/0.98  Current options:
% 2.76/0.98  ------ 
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  ------ Proving...
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  % SZS status Theorem for theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  fof(f11,conjecture,(
% 2.76/0.98    ! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f12,negated_conjecture,(
% 2.76/0.98    ~! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 2.76/0.98    inference(negated_conjecture,[],[f11])).
% 2.76/0.98  
% 2.76/0.98  fof(f19,plain,(
% 2.76/0.98    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0))),
% 2.76/0.98    inference(ennf_transformation,[],[f12])).
% 2.76/0.98  
% 2.76/0.98  fof(f25,plain,(
% 2.76/0.98    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0)) => (k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) & l1_pre_topc(sK1))),
% 2.76/0.98    introduced(choice_axiom,[])).
% 2.76/0.98  
% 2.76/0.98  fof(f26,plain,(
% 2.76/0.98    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) & l1_pre_topc(sK1)),
% 2.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f25])).
% 2.76/0.98  
% 2.76/0.98  fof(f40,plain,(
% 2.76/0.98    l1_pre_topc(sK1)),
% 2.76/0.98    inference(cnf_transformation,[],[f26])).
% 2.76/0.98  
% 2.76/0.98  fof(f8,axiom,(
% 2.76/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f16,plain,(
% 2.76/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.76/0.98    inference(ennf_transformation,[],[f8])).
% 2.76/0.98  
% 2.76/0.98  fof(f37,plain,(
% 2.76/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f16])).
% 2.76/0.98  
% 2.76/0.98  fof(f3,axiom,(
% 2.76/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f31,plain,(
% 2.76/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f3])).
% 2.76/0.98  
% 2.76/0.98  fof(f2,axiom,(
% 2.76/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f30,plain,(
% 2.76/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.76/0.98    inference(cnf_transformation,[],[f2])).
% 2.76/0.98  
% 2.76/0.98  fof(f9,axiom,(
% 2.76/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f17,plain,(
% 2.76/0.98    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 2.76/0.98    inference(ennf_transformation,[],[f9])).
% 2.76/0.98  
% 2.76/0.98  fof(f38,plain,(
% 2.76/0.98    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f17])).
% 2.76/0.98  
% 2.76/0.98  fof(f1,axiom,(
% 2.76/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f20,plain,(
% 2.76/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.98    inference(nnf_transformation,[],[f1])).
% 2.76/0.98  
% 2.76/0.98  fof(f21,plain,(
% 2.76/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.98    inference(flattening,[],[f20])).
% 2.76/0.98  
% 2.76/0.98  fof(f27,plain,(
% 2.76/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.76/0.98    inference(cnf_transformation,[],[f21])).
% 2.76/0.98  
% 2.76/0.98  fof(f43,plain,(
% 2.76/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.76/0.98    inference(equality_resolution,[],[f27])).
% 2.76/0.98  
% 2.76/0.98  fof(f5,axiom,(
% 2.76/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f13,plain,(
% 2.76/0.98    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.76/0.98    inference(ennf_transformation,[],[f5])).
% 2.76/0.98  
% 2.76/0.98  fof(f33,plain,(
% 2.76/0.98    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f13])).
% 2.76/0.98  
% 2.76/0.98  fof(f6,axiom,(
% 2.76/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f24,plain,(
% 2.76/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.76/0.98    inference(nnf_transformation,[],[f6])).
% 2.76/0.98  
% 2.76/0.98  fof(f35,plain,(
% 2.76/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f24])).
% 2.76/0.98  
% 2.76/0.98  fof(f41,plain,(
% 2.76/0.98    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)),
% 2.76/0.98    inference(cnf_transformation,[],[f26])).
% 2.76/0.98  
% 2.76/0.98  fof(f7,axiom,(
% 2.76/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f14,plain,(
% 2.76/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.76/0.99    inference(ennf_transformation,[],[f7])).
% 2.76/0.99  
% 2.76/0.99  fof(f15,plain,(
% 2.76/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.76/0.99    inference(flattening,[],[f14])).
% 2.76/0.99  
% 2.76/0.99  fof(f36,plain,(
% 2.76/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f15])).
% 2.76/0.99  
% 2.76/0.99  fof(f34,plain,(
% 2.76/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f24])).
% 2.76/0.99  
% 2.76/0.99  fof(f10,axiom,(
% 2.76/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f18,plain,(
% 2.76/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.76/0.99    inference(ennf_transformation,[],[f10])).
% 2.76/0.99  
% 2.76/0.99  fof(f39,plain,(
% 2.76/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f18])).
% 2.76/0.99  
% 2.76/0.99  fof(f29,plain,(
% 2.76/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f21])).
% 2.76/0.99  
% 2.76/0.99  cnf(c_14,negated_conjecture,
% 2.76/0.99      ( l1_pre_topc(sK1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_559,plain,
% 2.76/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_10,plain,
% 2.76/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_562,plain,
% 2.76/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_897,plain,
% 2.76/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_559,c_562]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4,plain,
% 2.76/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.76/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_567,plain,
% 2.76/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3,plain,
% 2.76/0.99      ( k2_subset_1(X0) = X0 ),
% 2.76/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_578,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.76/0.99      inference(light_normalisation,[status(thm)],[c_567,c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_11,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/0.99      | ~ l1_struct_0(X1)
% 2.76/0.99      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_561,plain,
% 2.76/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
% 2.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.76/0.99      | l1_struct_0(X0) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1975,plain,
% 2.76/0.99      ( k4_subset_1(u1_struct_0(X0),u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),u1_struct_0(X0))) = k2_struct_0(X0)
% 2.76/0.99      | l1_struct_0(X0) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_578,c_561]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2,plain,
% 2.76/0.99      ( r1_tarski(X0,X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_568,plain,
% 2.76/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_6,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.99      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_7,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_95,plain,
% 2.76/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.76/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_96,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.76/0.99      inference(renaming,[status(thm)],[c_95]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_118,plain,
% 2.76/0.99      ( ~ r1_tarski(X0,X1)
% 2.76/0.99      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 2.76/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_96]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_558,plain,
% 2.76/0.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 2.76/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_118]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_595,plain,
% 2.76/0.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 2.76/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.76/0.99      inference(light_normalisation,[status(thm)],[c_558,c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1130,plain,
% 2.76/0.99      ( k4_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0 ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_568,c_595]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1978,plain,
% 2.76/0.99      ( k2_struct_0(X0) = u1_struct_0(X0)
% 2.76/0.99      | l1_struct_0(X0) != iProver_top ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_1975,c_1130]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2525,plain,
% 2.76/0.99      ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_897,c_1978]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_13,negated_conjecture,
% 2.76/0.99      ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2527,plain,
% 2.76/0.99      ( k2_pre_topc(sK1,u1_struct_0(sK1)) != u1_struct_0(sK1) ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_2525,c_13]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_9,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/0.99      | ~ l1_pre_topc(X1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_563,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.76/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.76/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_8,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_564,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.76/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1948,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.76/0.99      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
% 2.76/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_563,c_564]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_12,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.76/0.99      | ~ l1_pre_topc(X1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_560,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.76/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 2.76/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1010,plain,
% 2.76/0.99      ( r1_tarski(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0))) = iProver_top
% 2.76/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_578,c_560]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_0,plain,
% 2.76/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.76/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_569,plain,
% 2.76/0.99      ( X0 = X1
% 2.76/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.76/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1480,plain,
% 2.76/0.99      ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
% 2.76/0.99      | r1_tarski(k2_pre_topc(X0,u1_struct_0(X0)),u1_struct_0(X0)) != iProver_top
% 2.76/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1010,c_569]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2186,plain,
% 2.76/0.99      ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
% 2.76/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.76/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1948,c_1480]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2188,plain,
% 2.76/0.99      ( k2_pre_topc(sK1,u1_struct_0(sK1)) = u1_struct_0(sK1)
% 2.76/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.76/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2186]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1053,plain,
% 2.76/0.99      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1058,plain,
% 2.76/0.99      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1060,plain,
% 2.76/0.99      ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1058]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_759,plain,
% 2.76/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/0.99      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1052,plain,
% 2.76/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.76/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_759]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1054,plain,
% 2.76/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.76/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1056,plain,
% 2.76/0.99      ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.76/0.99      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1054]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_15,plain,
% 2.76/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(contradiction,plain,
% 2.76/0.99      ( $false ),
% 2.76/0.99      inference(minisat,[status(thm)],[c_2527,c_2188,c_1060,c_1056,c_15]) ).
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/0.99  
% 2.76/0.99  ------                               Statistics
% 2.76/0.99  
% 2.76/0.99  ------ Selected
% 2.76/0.99  
% 2.76/0.99  total_time:                             0.112
% 2.76/0.99  
%------------------------------------------------------------------------------
