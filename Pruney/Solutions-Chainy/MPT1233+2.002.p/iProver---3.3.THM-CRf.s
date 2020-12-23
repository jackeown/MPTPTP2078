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
% DateTime   : Thu Dec  3 12:13:36 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 171 expanded)
%              Number of clauses        :   46 (  55 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  225 ( 373 expanded)
%              Number of equality atoms :   83 ( 148 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_757,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_756,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1173,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_757,c_756])).

cnf(c_8,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_753,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_772,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_753,c_6])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_754,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1096,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_772,c_754])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_751,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_1097,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_772,c_751])).

cnf(c_1101,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_1096,c_1097])).

cnf(c_1218,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_1173,c_1101])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_244,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_245,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_257,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_245,c_9])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_268,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_18])).

cnf(c_269,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_271,plain,
    ( v4_pre_topc(k1_xboole_0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_269,c_17])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_319,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_320,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_320])).

cnf(c_344,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_350,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_344,c_9])).

cnf(c_1219,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1218,c_350])).

cnf(c_1220,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1219,c_6])).

cnf(c_16,negated_conjecture,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_230,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_302,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_17])).

cnf(c_303,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_769,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_16,c_303])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1220,c_769])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:36:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.40/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/0.99  
% 1.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.40/0.99  
% 1.40/0.99  ------  iProver source info
% 1.40/0.99  
% 1.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.40/0.99  git: non_committed_changes: false
% 1.40/0.99  git: last_make_outside_of_git: false
% 1.40/0.99  
% 1.40/0.99  ------ 
% 1.40/0.99  
% 1.40/0.99  ------ Input Options
% 1.40/0.99  
% 1.40/0.99  --out_options                           all
% 1.40/0.99  --tptp_safe_out                         true
% 1.40/0.99  --problem_path                          ""
% 1.40/0.99  --include_path                          ""
% 1.40/0.99  --clausifier                            res/vclausify_rel
% 1.40/0.99  --clausifier_options                    --mode clausify
% 1.40/0.99  --stdin                                 false
% 1.40/0.99  --stats_out                             all
% 1.40/0.99  
% 1.40/0.99  ------ General Options
% 1.40/0.99  
% 1.40/0.99  --fof                                   false
% 1.40/0.99  --time_out_real                         305.
% 1.40/0.99  --time_out_virtual                      -1.
% 1.40/0.99  --symbol_type_check                     false
% 1.40/0.99  --clausify_out                          false
% 1.40/0.99  --sig_cnt_out                           false
% 1.40/0.99  --trig_cnt_out                          false
% 1.40/0.99  --trig_cnt_out_tolerance                1.
% 1.40/0.99  --trig_cnt_out_sk_spl                   false
% 1.40/0.99  --abstr_cl_out                          false
% 1.40/0.99  
% 1.40/0.99  ------ Global Options
% 1.40/0.99  
% 1.40/0.99  --schedule                              default
% 1.40/0.99  --add_important_lit                     false
% 1.40/0.99  --prop_solver_per_cl                    1000
% 1.40/0.99  --min_unsat_core                        false
% 1.40/0.99  --soft_assumptions                      false
% 1.40/0.99  --soft_lemma_size                       3
% 1.40/0.99  --prop_impl_unit_size                   0
% 1.40/0.99  --prop_impl_unit                        []
% 1.40/0.99  --share_sel_clauses                     true
% 1.40/0.99  --reset_solvers                         false
% 1.40/0.99  --bc_imp_inh                            [conj_cone]
% 1.40/0.99  --conj_cone_tolerance                   3.
% 1.40/0.99  --extra_neg_conj                        none
% 1.40/0.99  --large_theory_mode                     true
% 1.40/0.99  --prolific_symb_bound                   200
% 1.40/0.99  --lt_threshold                          2000
% 1.40/0.99  --clause_weak_htbl                      true
% 1.40/0.99  --gc_record_bc_elim                     false
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing Options
% 1.40/0.99  
% 1.40/0.99  --preprocessing_flag                    true
% 1.40/0.99  --time_out_prep_mult                    0.1
% 1.40/0.99  --splitting_mode                        input
% 1.40/0.99  --splitting_grd                         true
% 1.40/0.99  --splitting_cvd                         false
% 1.40/0.99  --splitting_cvd_svl                     false
% 1.40/0.99  --splitting_nvd                         32
% 1.40/0.99  --sub_typing                            true
% 1.40/0.99  --prep_gs_sim                           true
% 1.40/0.99  --prep_unflatten                        true
% 1.40/0.99  --prep_res_sim                          true
% 1.40/0.99  --prep_upred                            true
% 1.40/0.99  --prep_sem_filter                       exhaustive
% 1.40/0.99  --prep_sem_filter_out                   false
% 1.40/0.99  --pred_elim                             true
% 1.40/0.99  --res_sim_input                         true
% 1.40/0.99  --eq_ax_congr_red                       true
% 1.40/0.99  --pure_diseq_elim                       true
% 1.40/0.99  --brand_transform                       false
% 1.40/0.99  --non_eq_to_eq                          false
% 1.40/0.99  --prep_def_merge                        true
% 1.40/0.99  --prep_def_merge_prop_impl              false
% 1.40/0.99  --prep_def_merge_mbd                    true
% 1.40/0.99  --prep_def_merge_tr_red                 false
% 1.40/0.99  --prep_def_merge_tr_cl                  false
% 1.40/0.99  --smt_preprocessing                     true
% 1.40/0.99  --smt_ac_axioms                         fast
% 1.40/0.99  --preprocessed_out                      false
% 1.40/0.99  --preprocessed_stats                    false
% 1.40/0.99  
% 1.40/0.99  ------ Abstraction refinement Options
% 1.40/0.99  
% 1.40/0.99  --abstr_ref                             []
% 1.40/0.99  --abstr_ref_prep                        false
% 1.40/0.99  --abstr_ref_until_sat                   false
% 1.40/0.99  --abstr_ref_sig_restrict                funpre
% 1.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/0.99  --abstr_ref_under                       []
% 1.40/0.99  
% 1.40/0.99  ------ SAT Options
% 1.40/0.99  
% 1.40/0.99  --sat_mode                              false
% 1.40/0.99  --sat_fm_restart_options                ""
% 1.40/0.99  --sat_gr_def                            false
% 1.40/0.99  --sat_epr_types                         true
% 1.40/0.99  --sat_non_cyclic_types                  false
% 1.40/0.99  --sat_finite_models                     false
% 1.40/0.99  --sat_fm_lemmas                         false
% 1.40/0.99  --sat_fm_prep                           false
% 1.40/0.99  --sat_fm_uc_incr                        true
% 1.40/0.99  --sat_out_model                         small
% 1.40/0.99  --sat_out_clauses                       false
% 1.40/0.99  
% 1.40/0.99  ------ QBF Options
% 1.40/0.99  
% 1.40/0.99  --qbf_mode                              false
% 1.40/0.99  --qbf_elim_univ                         false
% 1.40/0.99  --qbf_dom_inst                          none
% 1.40/0.99  --qbf_dom_pre_inst                      false
% 1.40/0.99  --qbf_sk_in                             false
% 1.40/0.99  --qbf_pred_elim                         true
% 1.40/0.99  --qbf_split                             512
% 1.40/0.99  
% 1.40/0.99  ------ BMC1 Options
% 1.40/0.99  
% 1.40/0.99  --bmc1_incremental                      false
% 1.40/0.99  --bmc1_axioms                           reachable_all
% 1.40/0.99  --bmc1_min_bound                        0
% 1.40/0.99  --bmc1_max_bound                        -1
% 1.40/0.99  --bmc1_max_bound_default                -1
% 1.40/0.99  --bmc1_symbol_reachability              true
% 1.40/0.99  --bmc1_property_lemmas                  false
% 1.40/0.99  --bmc1_k_induction                      false
% 1.40/0.99  --bmc1_non_equiv_states                 false
% 1.40/0.99  --bmc1_deadlock                         false
% 1.40/0.99  --bmc1_ucm                              false
% 1.40/0.99  --bmc1_add_unsat_core                   none
% 1.40/0.99  --bmc1_unsat_core_children              false
% 1.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/0.99  --bmc1_out_stat                         full
% 1.40/0.99  --bmc1_ground_init                      false
% 1.40/0.99  --bmc1_pre_inst_next_state              false
% 1.40/0.99  --bmc1_pre_inst_state                   false
% 1.40/0.99  --bmc1_pre_inst_reach_state             false
% 1.40/0.99  --bmc1_out_unsat_core                   false
% 1.40/0.99  --bmc1_aig_witness_out                  false
% 1.40/0.99  --bmc1_verbose                          false
% 1.40/0.99  --bmc1_dump_clauses_tptp                false
% 1.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.40/0.99  --bmc1_dump_file                        -
% 1.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.40/0.99  --bmc1_ucm_extend_mode                  1
% 1.40/0.99  --bmc1_ucm_init_mode                    2
% 1.40/0.99  --bmc1_ucm_cone_mode                    none
% 1.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.40/0.99  --bmc1_ucm_relax_model                  4
% 1.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/0.99  --bmc1_ucm_layered_model                none
% 1.40/0.99  --bmc1_ucm_max_lemma_size               10
% 1.40/0.99  
% 1.40/0.99  ------ AIG Options
% 1.40/0.99  
% 1.40/0.99  --aig_mode                              false
% 1.40/0.99  
% 1.40/0.99  ------ Instantiation Options
% 1.40/0.99  
% 1.40/0.99  --instantiation_flag                    true
% 1.40/0.99  --inst_sos_flag                         false
% 1.40/0.99  --inst_sos_phase                        true
% 1.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel_side                     num_symb
% 1.40/0.99  --inst_solver_per_active                1400
% 1.40/0.99  --inst_solver_calls_frac                1.
% 1.40/0.99  --inst_passive_queue_type               priority_queues
% 1.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/0.99  --inst_passive_queues_freq              [25;2]
% 1.40/0.99  --inst_dismatching                      true
% 1.40/0.99  --inst_eager_unprocessed_to_passive     true
% 1.40/0.99  --inst_prop_sim_given                   true
% 1.40/0.99  --inst_prop_sim_new                     false
% 1.40/0.99  --inst_subs_new                         false
% 1.40/0.99  --inst_eq_res_simp                      false
% 1.40/0.99  --inst_subs_given                       false
% 1.40/0.99  --inst_orphan_elimination               true
% 1.40/0.99  --inst_learning_loop_flag               true
% 1.40/0.99  --inst_learning_start                   3000
% 1.40/0.99  --inst_learning_factor                  2
% 1.40/0.99  --inst_start_prop_sim_after_learn       3
% 1.40/0.99  --inst_sel_renew                        solver
% 1.40/0.99  --inst_lit_activity_flag                true
% 1.40/0.99  --inst_restr_to_given                   false
% 1.40/0.99  --inst_activity_threshold               500
% 1.40/0.99  --inst_out_proof                        true
% 1.40/0.99  
% 1.40/0.99  ------ Resolution Options
% 1.40/0.99  
% 1.40/0.99  --resolution_flag                       true
% 1.40/0.99  --res_lit_sel                           adaptive
% 1.40/0.99  --res_lit_sel_side                      none
% 1.40/0.99  --res_ordering                          kbo
% 1.40/0.99  --res_to_prop_solver                    active
% 1.40/0.99  --res_prop_simpl_new                    false
% 1.40/0.99  --res_prop_simpl_given                  true
% 1.40/0.99  --res_passive_queue_type                priority_queues
% 1.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/0.99  --res_passive_queues_freq               [15;5]
% 1.40/0.99  --res_forward_subs                      full
% 1.40/0.99  --res_backward_subs                     full
% 1.40/0.99  --res_forward_subs_resolution           true
% 1.40/0.99  --res_backward_subs_resolution          true
% 1.40/0.99  --res_orphan_elimination                true
% 1.40/0.99  --res_time_limit                        2.
% 1.40/0.99  --res_out_proof                         true
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Options
% 1.40/0.99  
% 1.40/0.99  --superposition_flag                    true
% 1.40/0.99  --sup_passive_queue_type                priority_queues
% 1.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.40/0.99  --demod_completeness_check              fast
% 1.40/0.99  --demod_use_ground                      true
% 1.40/0.99  --sup_to_prop_solver                    passive
% 1.40/0.99  --sup_prop_simpl_new                    true
% 1.40/0.99  --sup_prop_simpl_given                  true
% 1.40/0.99  --sup_fun_splitting                     false
% 1.40/0.99  --sup_smt_interval                      50000
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Simplification Setup
% 1.40/0.99  
% 1.40/0.99  --sup_indices_passive                   []
% 1.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_full_bw                           [BwDemod]
% 1.40/0.99  --sup_immed_triv                        [TrivRules]
% 1.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_immed_bw_main                     []
% 1.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  
% 1.40/0.99  ------ Combination Options
% 1.40/0.99  
% 1.40/0.99  --comb_res_mult                         3
% 1.40/0.99  --comb_sup_mult                         2
% 1.40/0.99  --comb_inst_mult                        10
% 1.40/0.99  
% 1.40/0.99  ------ Debug Options
% 1.40/0.99  
% 1.40/0.99  --dbg_backtrace                         false
% 1.40/0.99  --dbg_dump_prop_clauses                 false
% 1.40/0.99  --dbg_dump_prop_clauses_file            -
% 1.40/0.99  --dbg_out_stat                          false
% 1.40/0.99  ------ Parsing...
% 1.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.40/0.99  ------ Proving...
% 1.40/0.99  ------ Problem Properties 
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  clauses                                 12
% 1.40/0.99  conjectures                             1
% 1.40/0.99  EPR                                     2
% 1.40/0.99  Horn                                    12
% 1.40/0.99  unary                                   7
% 1.40/0.99  binary                                  4
% 1.40/0.99  lits                                    18
% 1.40/0.99  lits eq                                 9
% 1.40/0.99  fd_pure                                 0
% 1.40/0.99  fd_pseudo                               0
% 1.40/0.99  fd_cond                                 0
% 1.40/0.99  fd_pseudo_cond                          1
% 1.40/0.99  AC symbols                              0
% 1.40/0.99  
% 1.40/0.99  ------ Schedule dynamic 5 is on 
% 1.40/0.99  
% 1.40/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  ------ 
% 1.40/0.99  Current options:
% 1.40/0.99  ------ 
% 1.40/0.99  
% 1.40/0.99  ------ Input Options
% 1.40/0.99  
% 1.40/0.99  --out_options                           all
% 1.40/0.99  --tptp_safe_out                         true
% 1.40/0.99  --problem_path                          ""
% 1.40/0.99  --include_path                          ""
% 1.40/0.99  --clausifier                            res/vclausify_rel
% 1.40/0.99  --clausifier_options                    --mode clausify
% 1.40/0.99  --stdin                                 false
% 1.40/0.99  --stats_out                             all
% 1.40/0.99  
% 1.40/0.99  ------ General Options
% 1.40/0.99  
% 1.40/0.99  --fof                                   false
% 1.40/0.99  --time_out_real                         305.
% 1.40/0.99  --time_out_virtual                      -1.
% 1.40/0.99  --symbol_type_check                     false
% 1.40/0.99  --clausify_out                          false
% 1.40/0.99  --sig_cnt_out                           false
% 1.40/0.99  --trig_cnt_out                          false
% 1.40/0.99  --trig_cnt_out_tolerance                1.
% 1.40/0.99  --trig_cnt_out_sk_spl                   false
% 1.40/0.99  --abstr_cl_out                          false
% 1.40/0.99  
% 1.40/0.99  ------ Global Options
% 1.40/0.99  
% 1.40/0.99  --schedule                              default
% 1.40/0.99  --add_important_lit                     false
% 1.40/0.99  --prop_solver_per_cl                    1000
% 1.40/0.99  --min_unsat_core                        false
% 1.40/0.99  --soft_assumptions                      false
% 1.40/0.99  --soft_lemma_size                       3
% 1.40/0.99  --prop_impl_unit_size                   0
% 1.40/0.99  --prop_impl_unit                        []
% 1.40/0.99  --share_sel_clauses                     true
% 1.40/0.99  --reset_solvers                         false
% 1.40/0.99  --bc_imp_inh                            [conj_cone]
% 1.40/0.99  --conj_cone_tolerance                   3.
% 1.40/0.99  --extra_neg_conj                        none
% 1.40/0.99  --large_theory_mode                     true
% 1.40/0.99  --prolific_symb_bound                   200
% 1.40/0.99  --lt_threshold                          2000
% 1.40/0.99  --clause_weak_htbl                      true
% 1.40/0.99  --gc_record_bc_elim                     false
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing Options
% 1.40/0.99  
% 1.40/0.99  --preprocessing_flag                    true
% 1.40/0.99  --time_out_prep_mult                    0.1
% 1.40/0.99  --splitting_mode                        input
% 1.40/0.99  --splitting_grd                         true
% 1.40/0.99  --splitting_cvd                         false
% 1.40/0.99  --splitting_cvd_svl                     false
% 1.40/0.99  --splitting_nvd                         32
% 1.40/0.99  --sub_typing                            true
% 1.40/0.99  --prep_gs_sim                           true
% 1.40/0.99  --prep_unflatten                        true
% 1.40/0.99  --prep_res_sim                          true
% 1.40/0.99  --prep_upred                            true
% 1.40/0.99  --prep_sem_filter                       exhaustive
% 1.40/0.99  --prep_sem_filter_out                   false
% 1.40/0.99  --pred_elim                             true
% 1.40/0.99  --res_sim_input                         true
% 1.40/0.99  --eq_ax_congr_red                       true
% 1.40/0.99  --pure_diseq_elim                       true
% 1.40/0.99  --brand_transform                       false
% 1.40/0.99  --non_eq_to_eq                          false
% 1.40/0.99  --prep_def_merge                        true
% 1.40/0.99  --prep_def_merge_prop_impl              false
% 1.40/0.99  --prep_def_merge_mbd                    true
% 1.40/0.99  --prep_def_merge_tr_red                 false
% 1.40/0.99  --prep_def_merge_tr_cl                  false
% 1.40/0.99  --smt_preprocessing                     true
% 1.40/0.99  --smt_ac_axioms                         fast
% 1.40/0.99  --preprocessed_out                      false
% 1.40/0.99  --preprocessed_stats                    false
% 1.40/0.99  
% 1.40/0.99  ------ Abstraction refinement Options
% 1.40/0.99  
% 1.40/0.99  --abstr_ref                             []
% 1.40/0.99  --abstr_ref_prep                        false
% 1.40/0.99  --abstr_ref_until_sat                   false
% 1.40/0.99  --abstr_ref_sig_restrict                funpre
% 1.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/0.99  --abstr_ref_under                       []
% 1.40/0.99  
% 1.40/0.99  ------ SAT Options
% 1.40/0.99  
% 1.40/0.99  --sat_mode                              false
% 1.40/0.99  --sat_fm_restart_options                ""
% 1.40/0.99  --sat_gr_def                            false
% 1.40/0.99  --sat_epr_types                         true
% 1.40/0.99  --sat_non_cyclic_types                  false
% 1.40/0.99  --sat_finite_models                     false
% 1.40/0.99  --sat_fm_lemmas                         false
% 1.40/0.99  --sat_fm_prep                           false
% 1.40/0.99  --sat_fm_uc_incr                        true
% 1.40/0.99  --sat_out_model                         small
% 1.40/0.99  --sat_out_clauses                       false
% 1.40/0.99  
% 1.40/0.99  ------ QBF Options
% 1.40/0.99  
% 1.40/0.99  --qbf_mode                              false
% 1.40/0.99  --qbf_elim_univ                         false
% 1.40/0.99  --qbf_dom_inst                          none
% 1.40/0.99  --qbf_dom_pre_inst                      false
% 1.40/0.99  --qbf_sk_in                             false
% 1.40/0.99  --qbf_pred_elim                         true
% 1.40/0.99  --qbf_split                             512
% 1.40/0.99  
% 1.40/0.99  ------ BMC1 Options
% 1.40/0.99  
% 1.40/0.99  --bmc1_incremental                      false
% 1.40/0.99  --bmc1_axioms                           reachable_all
% 1.40/0.99  --bmc1_min_bound                        0
% 1.40/0.99  --bmc1_max_bound                        -1
% 1.40/0.99  --bmc1_max_bound_default                -1
% 1.40/0.99  --bmc1_symbol_reachability              true
% 1.40/0.99  --bmc1_property_lemmas                  false
% 1.40/0.99  --bmc1_k_induction                      false
% 1.40/0.99  --bmc1_non_equiv_states                 false
% 1.40/0.99  --bmc1_deadlock                         false
% 1.40/0.99  --bmc1_ucm                              false
% 1.40/0.99  --bmc1_add_unsat_core                   none
% 1.40/0.99  --bmc1_unsat_core_children              false
% 1.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/0.99  --bmc1_out_stat                         full
% 1.40/0.99  --bmc1_ground_init                      false
% 1.40/0.99  --bmc1_pre_inst_next_state              false
% 1.40/0.99  --bmc1_pre_inst_state                   false
% 1.40/0.99  --bmc1_pre_inst_reach_state             false
% 1.40/0.99  --bmc1_out_unsat_core                   false
% 1.40/0.99  --bmc1_aig_witness_out                  false
% 1.40/0.99  --bmc1_verbose                          false
% 1.40/0.99  --bmc1_dump_clauses_tptp                false
% 1.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.40/0.99  --bmc1_dump_file                        -
% 1.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.40/0.99  --bmc1_ucm_extend_mode                  1
% 1.40/0.99  --bmc1_ucm_init_mode                    2
% 1.40/0.99  --bmc1_ucm_cone_mode                    none
% 1.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.40/0.99  --bmc1_ucm_relax_model                  4
% 1.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/0.99  --bmc1_ucm_layered_model                none
% 1.40/0.99  --bmc1_ucm_max_lemma_size               10
% 1.40/0.99  
% 1.40/0.99  ------ AIG Options
% 1.40/0.99  
% 1.40/0.99  --aig_mode                              false
% 1.40/0.99  
% 1.40/0.99  ------ Instantiation Options
% 1.40/0.99  
% 1.40/0.99  --instantiation_flag                    true
% 1.40/0.99  --inst_sos_flag                         false
% 1.40/0.99  --inst_sos_phase                        true
% 1.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/0.99  --inst_lit_sel_side                     none
% 1.40/0.99  --inst_solver_per_active                1400
% 1.40/0.99  --inst_solver_calls_frac                1.
% 1.40/0.99  --inst_passive_queue_type               priority_queues
% 1.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/0.99  --inst_passive_queues_freq              [25;2]
% 1.40/0.99  --inst_dismatching                      true
% 1.40/0.99  --inst_eager_unprocessed_to_passive     true
% 1.40/0.99  --inst_prop_sim_given                   true
% 1.40/0.99  --inst_prop_sim_new                     false
% 1.40/0.99  --inst_subs_new                         false
% 1.40/0.99  --inst_eq_res_simp                      false
% 1.40/0.99  --inst_subs_given                       false
% 1.40/0.99  --inst_orphan_elimination               true
% 1.40/0.99  --inst_learning_loop_flag               true
% 1.40/0.99  --inst_learning_start                   3000
% 1.40/0.99  --inst_learning_factor                  2
% 1.40/0.99  --inst_start_prop_sim_after_learn       3
% 1.40/0.99  --inst_sel_renew                        solver
% 1.40/0.99  --inst_lit_activity_flag                true
% 1.40/0.99  --inst_restr_to_given                   false
% 1.40/0.99  --inst_activity_threshold               500
% 1.40/0.99  --inst_out_proof                        true
% 1.40/0.99  
% 1.40/0.99  ------ Resolution Options
% 1.40/0.99  
% 1.40/0.99  --resolution_flag                       false
% 1.40/0.99  --res_lit_sel                           adaptive
% 1.40/0.99  --res_lit_sel_side                      none
% 1.40/0.99  --res_ordering                          kbo
% 1.40/0.99  --res_to_prop_solver                    active
% 1.40/0.99  --res_prop_simpl_new                    false
% 1.40/0.99  --res_prop_simpl_given                  true
% 1.40/0.99  --res_passive_queue_type                priority_queues
% 1.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/0.99  --res_passive_queues_freq               [15;5]
% 1.40/0.99  --res_forward_subs                      full
% 1.40/0.99  --res_backward_subs                     full
% 1.40/0.99  --res_forward_subs_resolution           true
% 1.40/0.99  --res_backward_subs_resolution          true
% 1.40/0.99  --res_orphan_elimination                true
% 1.40/0.99  --res_time_limit                        2.
% 1.40/0.99  --res_out_proof                         true
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Options
% 1.40/0.99  
% 1.40/0.99  --superposition_flag                    true
% 1.40/0.99  --sup_passive_queue_type                priority_queues
% 1.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.40/0.99  --demod_completeness_check              fast
% 1.40/0.99  --demod_use_ground                      true
% 1.40/0.99  --sup_to_prop_solver                    passive
% 1.40/0.99  --sup_prop_simpl_new                    true
% 1.40/0.99  --sup_prop_simpl_given                  true
% 1.40/0.99  --sup_fun_splitting                     false
% 1.40/0.99  --sup_smt_interval                      50000
% 1.40/0.99  
% 1.40/0.99  ------ Superposition Simplification Setup
% 1.40/0.99  
% 1.40/0.99  --sup_indices_passive                   []
% 1.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_full_bw                           [BwDemod]
% 1.40/0.99  --sup_immed_triv                        [TrivRules]
% 1.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_immed_bw_main                     []
% 1.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/0.99  
% 1.40/0.99  ------ Combination Options
% 1.40/0.99  
% 1.40/0.99  --comb_res_mult                         3
% 1.40/0.99  --comb_sup_mult                         2
% 1.40/0.99  --comb_inst_mult                        10
% 1.40/0.99  
% 1.40/0.99  ------ Debug Options
% 1.40/0.99  
% 1.40/0.99  --dbg_backtrace                         false
% 1.40/0.99  --dbg_dump_prop_clauses                 false
% 1.40/0.99  --dbg_dump_prop_clauses_file            -
% 1.40/0.99  --dbg_out_stat                          false
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  ------ Proving...
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  % SZS status Theorem for theBenchmark.p
% 1.40/0.99  
% 1.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.40/0.99  
% 1.40/0.99  fof(f2,axiom,(
% 1.40/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f29,plain,(
% 1.40/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.99    inference(nnf_transformation,[],[f2])).
% 1.40/0.99  
% 1.40/0.99  fof(f30,plain,(
% 1.40/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.99    inference(flattening,[],[f29])).
% 1.40/0.99  
% 1.40/0.99  fof(f35,plain,(
% 1.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.40/0.99    inference(cnf_transformation,[],[f30])).
% 1.40/0.99  
% 1.40/0.99  fof(f59,plain,(
% 1.40/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.99    inference(equality_resolution,[],[f35])).
% 1.40/0.99  
% 1.40/0.99  fof(f3,axiom,(
% 1.40/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f31,plain,(
% 1.40/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.40/0.99    inference(nnf_transformation,[],[f3])).
% 1.40/0.99  
% 1.40/0.99  fof(f39,plain,(
% 1.40/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f31])).
% 1.40/0.99  
% 1.40/0.99  fof(f7,axiom,(
% 1.40/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f43,plain,(
% 1.40/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.40/0.99    inference(cnf_transformation,[],[f7])).
% 1.40/0.99  
% 1.40/0.99  fof(f8,axiom,(
% 1.40/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f44,plain,(
% 1.40/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.40/0.99    inference(cnf_transformation,[],[f8])).
% 1.40/0.99  
% 1.40/0.99  fof(f4,axiom,(
% 1.40/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f40,plain,(
% 1.40/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f4])).
% 1.40/0.99  
% 1.40/0.99  fof(f55,plain,(
% 1.40/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.40/0.99    inference(definition_unfolding,[],[f44,f40])).
% 1.40/0.99  
% 1.40/0.99  fof(f57,plain,(
% 1.40/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.40/0.99    inference(definition_unfolding,[],[f43,f55])).
% 1.40/0.99  
% 1.40/0.99  fof(f5,axiom,(
% 1.40/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f41,plain,(
% 1.40/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.40/0.99    inference(cnf_transformation,[],[f5])).
% 1.40/0.99  
% 1.40/0.99  fof(f56,plain,(
% 1.40/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.40/0.99    inference(definition_unfolding,[],[f41,f55])).
% 1.40/0.99  
% 1.40/0.99  fof(f6,axiom,(
% 1.40/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f19,plain,(
% 1.40/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f6])).
% 1.40/0.99  
% 1.40/0.99  fof(f42,plain,(
% 1.40/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.99    inference(cnf_transformation,[],[f19])).
% 1.40/0.99  
% 1.40/0.99  fof(f15,axiom,(
% 1.40/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f26,plain,(
% 1.40/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.99    inference(ennf_transformation,[],[f15])).
% 1.40/0.99  
% 1.40/0.99  fof(f51,plain,(
% 1.40/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f26])).
% 1.40/0.99  
% 1.40/0.99  fof(f16,conjecture,(
% 1.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f17,negated_conjecture,(
% 1.40/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.40/0.99    inference(negated_conjecture,[],[f16])).
% 1.40/0.99  
% 1.40/0.99  fof(f27,plain,(
% 1.40/0.99    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f17])).
% 1.40/0.99  
% 1.40/0.99  fof(f28,plain,(
% 1.40/0.99    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.40/0.99    inference(flattening,[],[f27])).
% 1.40/0.99  
% 1.40/0.99  fof(f32,plain,(
% 1.40/0.99    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.40/0.99    introduced(choice_axiom,[])).
% 1.40/0.99  
% 1.40/0.99  fof(f33,plain,(
% 1.40/0.99    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).
% 1.40/0.99  
% 1.40/0.99  fof(f53,plain,(
% 1.40/0.99    l1_pre_topc(sK0)),
% 1.40/0.99    inference(cnf_transformation,[],[f33])).
% 1.40/0.99  
% 1.40/0.99  fof(f1,axiom,(
% 1.40/0.99    v1_xboole_0(k1_xboole_0)),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f34,plain,(
% 1.40/0.99    v1_xboole_0(k1_xboole_0)),
% 1.40/0.99    inference(cnf_transformation,[],[f1])).
% 1.40/0.99  
% 1.40/0.99  fof(f11,axiom,(
% 1.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f20,plain,(
% 1.40/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.40/0.99    inference(ennf_transformation,[],[f11])).
% 1.40/0.99  
% 1.40/0.99  fof(f21,plain,(
% 1.40/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.40/0.99    inference(flattening,[],[f20])).
% 1.40/0.99  
% 1.40/0.99  fof(f46,plain,(
% 1.40/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f21])).
% 1.40/0.99  
% 1.40/0.99  fof(f9,axiom,(
% 1.40/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f45,plain,(
% 1.40/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.99    inference(cnf_transformation,[],[f9])).
% 1.40/0.99  
% 1.40/0.99  fof(f52,plain,(
% 1.40/0.99    v2_pre_topc(sK0)),
% 1.40/0.99    inference(cnf_transformation,[],[f33])).
% 1.40/0.99  
% 1.40/0.99  fof(f14,axiom,(
% 1.40/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f24,plain,(
% 1.40/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.99    inference(ennf_transformation,[],[f14])).
% 1.40/0.99  
% 1.40/0.99  fof(f25,plain,(
% 1.40/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.99    inference(flattening,[],[f24])).
% 1.40/0.99  
% 1.40/0.99  fof(f49,plain,(
% 1.40/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f25])).
% 1.40/0.99  
% 1.40/0.99  fof(f54,plain,(
% 1.40/0.99    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.40/0.99    inference(cnf_transformation,[],[f33])).
% 1.40/0.99  
% 1.40/0.99  fof(f13,axiom,(
% 1.40/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f23,plain,(
% 1.40/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.40/0.99    inference(ennf_transformation,[],[f13])).
% 1.40/0.99  
% 1.40/0.99  fof(f48,plain,(
% 1.40/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f23])).
% 1.40/0.99  
% 1.40/0.99  fof(f12,axiom,(
% 1.40/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.40/0.99  
% 1.40/0.99  fof(f22,plain,(
% 1.40/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.40/0.99    inference(ennf_transformation,[],[f12])).
% 1.40/0.99  
% 1.40/0.99  fof(f47,plain,(
% 1.40/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.40/0.99    inference(cnf_transformation,[],[f22])).
% 1.40/0.99  
% 1.40/0.99  cnf(c_3,plain,
% 1.40/0.99      ( r1_tarski(X0,X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_757,plain,
% 1.40/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.40/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_4,plain,
% 1.40/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.40/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_756,plain,
% 1.40/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 1.40/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.40/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1173,plain,
% 1.40/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.40/0.99      inference(superposition,[status(thm)],[c_757,c_756]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_8,plain,
% 1.40/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 1.40/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_753,plain,
% 1.40/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.40/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_6,plain,
% 1.40/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 1.40/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_772,plain,
% 1.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.40/0.99      inference(light_normalisation,[status(thm)],[c_753,c_6]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_7,plain,
% 1.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.40/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_754,plain,
% 1.40/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 1.40/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.40/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1096,plain,
% 1.40/0.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 1.40/0.99      inference(superposition,[status(thm)],[c_772,c_754]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_15,plain,
% 1.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.40/0.99      | ~ l1_pre_topc(X1)
% 1.40/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_17,negated_conjecture,
% 1.40/0.99      ( l1_pre_topc(sK0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_307,plain,
% 1.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.40/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 1.40/0.99      | sK0 != X1 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_308,plain,
% 1.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.40/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_307]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_751,plain,
% 1.40/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 1.40/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.40/0.99      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1097,plain,
% 1.40/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 1.40/0.99      inference(superposition,[status(thm)],[c_772,c_751]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1101,plain,
% 1.40/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 1.40/0.99      inference(demodulation,[status(thm)],[c_1096,c_1097]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1218,plain,
% 1.40/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 1.40/0.99      inference(demodulation,[status(thm)],[c_1173,c_1101]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_0,plain,
% 1.40/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_10,plain,
% 1.40/0.99      ( v4_pre_topc(X0,X1)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.40/0.99      | ~ v2_pre_topc(X1)
% 1.40/0.99      | ~ l1_pre_topc(X1)
% 1.40/0.99      | ~ v1_xboole_0(X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_244,plain,
% 1.40/0.99      ( v4_pre_topc(X0,X1)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.40/0.99      | ~ v2_pre_topc(X1)
% 1.40/0.99      | ~ l1_pre_topc(X1)
% 1.40/0.99      | k1_xboole_0 != X0 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_245,plain,
% 1.40/0.99      ( v4_pre_topc(k1_xboole_0,X0)
% 1.40/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.40/0.99      | ~ v2_pre_topc(X0)
% 1.40/0.99      | ~ l1_pre_topc(X0) ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_244]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_9,plain,
% 1.40/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.40/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_257,plain,
% 1.40/0.99      ( v4_pre_topc(k1_xboole_0,X0)
% 1.40/0.99      | ~ v2_pre_topc(X0)
% 1.40/0.99      | ~ l1_pre_topc(X0) ),
% 1.40/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_245,c_9]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_18,negated_conjecture,
% 1.40/0.99      ( v2_pre_topc(sK0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_268,plain,
% 1.40/0.99      ( v4_pre_topc(k1_xboole_0,X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_257,c_18]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_269,plain,
% 1.40/0.99      ( v4_pre_topc(k1_xboole_0,sK0) | ~ l1_pre_topc(sK0) ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_268]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_271,plain,
% 1.40/0.99      ( v4_pre_topc(k1_xboole_0,sK0) ),
% 1.40/0.99      inference(global_propositional_subsumption,
% 1.40/0.99                [status(thm)],
% 1.40/0.99                [c_269,c_17]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_14,plain,
% 1.40/0.99      ( ~ v4_pre_topc(X0,X1)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.40/0.99      | ~ l1_pre_topc(X1)
% 1.40/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 1.40/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_319,plain,
% 1.40/0.99      ( ~ v4_pre_topc(X0,X1)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.40/0.99      | k2_pre_topc(X1,X0) = X0
% 1.40/0.99      | sK0 != X1 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_320,plain,
% 1.40/0.99      ( ~ v4_pre_topc(X0,sK0)
% 1.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.40/0.99      | k2_pre_topc(sK0,X0) = X0 ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_319]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_343,plain,
% 1.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.40/0.99      | k2_pre_topc(sK0,X0) = X0
% 1.40/0.99      | sK0 != sK0
% 1.40/0.99      | k1_xboole_0 != X0 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_271,c_320]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_344,plain,
% 1.40/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.40/0.99      | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_350,plain,
% 1.40/0.99      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 1.40/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_344,c_9]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1219,plain,
% 1.40/0.99      ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
% 1.40/0.99      inference(light_normalisation,[status(thm)],[c_1218,c_350]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_1220,plain,
% 1.40/0.99      ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 1.40/0.99      inference(demodulation,[status(thm)],[c_1219,c_6]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_16,negated_conjecture,
% 1.40/0.99      ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
% 1.40/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_12,plain,
% 1.40/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_11,plain,
% 1.40/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.40/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_230,plain,
% 1.40/0.99      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.40/0.99      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_302,plain,
% 1.40/0.99      ( k2_struct_0(X0) = u1_struct_0(X0) | sK0 != X0 ),
% 1.40/0.99      inference(resolution_lifted,[status(thm)],[c_230,c_17]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_303,plain,
% 1.40/0.99      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.40/0.99      inference(unflattening,[status(thm)],[c_302]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(c_769,plain,
% 1.40/0.99      ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
% 1.40/0.99      inference(light_normalisation,[status(thm)],[c_16,c_303]) ).
% 1.40/0.99  
% 1.40/0.99  cnf(contradiction,plain,
% 1.40/0.99      ( $false ),
% 1.40/0.99      inference(minisat,[status(thm)],[c_1220,c_769]) ).
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.40/0.99  
% 1.40/0.99  ------                               Statistics
% 1.40/0.99  
% 1.40/0.99  ------ General
% 1.40/0.99  
% 1.40/0.99  abstr_ref_over_cycles:                  0
% 1.40/0.99  abstr_ref_under_cycles:                 0
% 1.40/0.99  gc_basic_clause_elim:                   0
% 1.40/0.99  forced_gc_time:                         0
% 1.40/0.99  parsing_time:                           0.014
% 1.40/0.99  unif_index_cands_time:                  0.
% 1.40/0.99  unif_index_add_time:                    0.
% 1.40/0.99  orderings_time:                         0.
% 1.40/0.99  out_proof_time:                         0.008
% 1.40/0.99  total_time:                             0.053
% 1.40/0.99  num_of_symbols:                         47
% 1.40/0.99  num_of_terms:                           952
% 1.40/0.99  
% 1.40/0.99  ------ Preprocessing
% 1.40/0.99  
% 1.40/0.99  num_of_splits:                          0
% 1.40/0.99  num_of_split_atoms:                     0
% 1.40/0.99  num_of_reused_defs:                     0
% 1.40/0.99  num_eq_ax_congr_red:                    17
% 1.40/0.99  num_of_sem_filtered_clauses:            1
% 1.40/0.99  num_of_subtypes:                        0
% 1.40/0.99  monotx_restored_types:                  0
% 1.40/0.99  sat_num_of_epr_types:                   0
% 1.40/0.99  sat_num_of_non_cyclic_types:            0
% 1.40/0.99  sat_guarded_non_collapsed_types:        0
% 1.40/0.99  num_pure_diseq_elim:                    0
% 1.40/0.99  simp_replaced_by:                       0
% 1.40/0.99  res_preprocessed:                       73
% 1.40/0.99  prep_upred:                             0
% 1.40/0.99  prep_unflattend:                        15
% 1.40/0.99  smt_new_axioms:                         0
% 1.40/0.99  pred_elim_cands:                        2
% 1.40/0.99  pred_elim:                              5
% 1.40/0.99  pred_elim_cl:                           6
% 1.40/0.99  pred_elim_cycles:                       7
% 1.40/0.99  merged_defs:                            8
% 1.40/0.99  merged_defs_ncl:                        0
% 1.40/0.99  bin_hyper_res:                          8
% 1.40/0.99  prep_cycles:                            4
% 1.40/0.99  pred_elim_time:                         0.003
% 1.40/0.99  splitting_time:                         0.
% 1.40/0.99  sem_filter_time:                        0.
% 1.40/0.99  monotx_time:                            0.
% 1.40/0.99  subtype_inf_time:                       0.
% 1.40/0.99  
% 1.40/0.99  ------ Problem properties
% 1.40/0.99  
% 1.40/0.99  clauses:                                12
% 1.40/0.99  conjectures:                            1
% 1.40/0.99  epr:                                    2
% 1.40/0.99  horn:                                   12
% 1.40/0.99  ground:                                 3
% 1.40/0.99  unary:                                  7
% 1.40/0.99  binary:                                 4
% 1.40/0.99  lits:                                   18
% 1.40/0.99  lits_eq:                                9
% 1.40/0.99  fd_pure:                                0
% 1.40/0.99  fd_pseudo:                              0
% 1.40/0.99  fd_cond:                                0
% 1.40/0.99  fd_pseudo_cond:                         1
% 1.40/0.99  ac_symbols:                             0
% 1.40/0.99  
% 1.40/0.99  ------ Propositional Solver
% 1.40/0.99  
% 1.40/0.99  prop_solver_calls:                      26
% 1.40/0.99  prop_fast_solver_calls:                 338
% 1.40/0.99  smt_solver_calls:                       0
% 1.40/0.99  smt_fast_solver_calls:                  0
% 1.40/0.99  prop_num_of_clauses:                    346
% 1.40/0.99  prop_preprocess_simplified:             2106
% 1.40/0.99  prop_fo_subsumed:                       2
% 1.40/0.99  prop_solver_time:                       0.
% 1.40/0.99  smt_solver_time:                        0.
% 1.40/0.99  smt_fast_solver_time:                   0.
% 1.40/0.99  prop_fast_solver_time:                  0.
% 1.40/0.99  prop_unsat_core_time:                   0.
% 1.40/0.99  
% 1.40/0.99  ------ QBF
% 1.40/0.99  
% 1.40/0.99  qbf_q_res:                              0
% 1.40/0.99  qbf_num_tautologies:                    0
% 1.40/0.99  qbf_prep_cycles:                        0
% 1.40/0.99  
% 1.40/0.99  ------ BMC1
% 1.40/0.99  
% 1.40/0.99  bmc1_current_bound:                     -1
% 1.40/0.99  bmc1_last_solved_bound:                 -1
% 1.40/0.99  bmc1_unsat_core_size:                   -1
% 1.40/0.99  bmc1_unsat_core_parents_size:           -1
% 1.40/0.99  bmc1_merge_next_fun:                    0
% 1.40/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.40/0.99  
% 1.40/0.99  ------ Instantiation
% 1.40/0.99  
% 1.40/0.99  inst_num_of_clauses:                    122
% 1.40/0.99  inst_num_in_passive:                    16
% 1.40/0.99  inst_num_in_active:                     77
% 1.40/0.99  inst_num_in_unprocessed:                29
% 1.40/0.99  inst_num_of_loops:                      80
% 1.40/0.99  inst_num_of_learning_restarts:          0
% 1.40/0.99  inst_num_moves_active_passive:          1
% 1.40/0.99  inst_lit_activity:                      0
% 1.40/0.99  inst_lit_activity_moves:                0
% 1.40/0.99  inst_num_tautologies:                   0
% 1.40/0.99  inst_num_prop_implied:                  0
% 1.40/0.99  inst_num_existing_simplified:           0
% 1.40/0.99  inst_num_eq_res_simplified:             0
% 1.40/0.99  inst_num_child_elim:                    0
% 1.40/0.99  inst_num_of_dismatching_blockings:      11
% 1.40/0.99  inst_num_of_non_proper_insts:           106
% 1.40/0.99  inst_num_of_duplicates:                 0
% 1.40/0.99  inst_inst_num_from_inst_to_res:         0
% 1.40/0.99  inst_dismatching_checking_time:         0.
% 1.40/0.99  
% 1.40/0.99  ------ Resolution
% 1.40/0.99  
% 1.40/0.99  res_num_of_clauses:                     0
% 1.40/0.99  res_num_in_passive:                     0
% 1.40/0.99  res_num_in_active:                      0
% 1.40/0.99  res_num_of_loops:                       77
% 1.40/0.99  res_forward_subset_subsumed:            11
% 1.40/0.99  res_backward_subset_subsumed:           0
% 1.40/0.99  res_forward_subsumed:                   0
% 1.40/0.99  res_backward_subsumed:                  0
% 1.40/0.99  res_forward_subsumption_resolution:     2
% 1.40/0.99  res_backward_subsumption_resolution:    0
% 1.40/0.99  res_clause_to_clause_subsumption:       39
% 1.40/0.99  res_orphan_elimination:                 0
% 1.40/0.99  res_tautology_del:                      25
% 1.40/0.99  res_num_eq_res_simplified:              0
% 1.40/0.99  res_num_sel_changes:                    0
% 1.40/0.99  res_moves_from_active_to_pass:          0
% 1.40/0.99  
% 1.40/0.99  ------ Superposition
% 1.40/0.99  
% 1.40/0.99  sup_time_total:                         0.
% 1.40/0.99  sup_time_generating:                    0.
% 1.40/0.99  sup_time_sim_full:                      0.
% 1.40/0.99  sup_time_sim_immed:                     0.
% 1.40/0.99  
% 1.40/0.99  sup_num_of_clauses:                     18
% 1.40/0.99  sup_num_in_active:                      13
% 1.40/0.99  sup_num_in_passive:                     5
% 1.40/0.99  sup_num_of_loops:                       14
% 1.40/0.99  sup_fw_superposition:                   3
% 1.40/0.99  sup_bw_superposition:                   3
% 1.40/0.99  sup_immediate_simplified:               4
% 1.40/0.99  sup_given_eliminated:                   0
% 1.40/0.99  comparisons_done:                       0
% 1.40/0.99  comparisons_avoided:                    0
% 1.40/0.99  
% 1.40/0.99  ------ Simplifications
% 1.40/0.99  
% 1.40/0.99  
% 1.40/0.99  sim_fw_subset_subsumed:                 0
% 1.40/0.99  sim_bw_subset_subsumed:                 0
% 1.40/0.99  sim_fw_subsumed:                        0
% 1.40/0.99  sim_bw_subsumed:                        0
% 1.40/0.99  sim_fw_subsumption_res:                 0
% 1.40/0.99  sim_bw_subsumption_res:                 0
% 1.40/0.99  sim_tautology_del:                      0
% 1.40/0.99  sim_eq_tautology_del:                   0
% 1.40/0.99  sim_eq_res_simp:                        0
% 1.40/0.99  sim_fw_demodulated:                     2
% 1.40/0.99  sim_bw_demodulated:                     2
% 1.40/0.99  sim_light_normalised:                   4
% 1.40/0.99  sim_joinable_taut:                      0
% 1.40/0.99  sim_joinable_simp:                      0
% 1.40/0.99  sim_ac_normalised:                      0
% 1.40/0.99  sim_smt_subsumption:                    0
% 1.40/0.99  
%------------------------------------------------------------------------------
