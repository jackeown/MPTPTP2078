%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:08 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 209 expanded)
%              Number of clauses        :   52 (  68 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  221 ( 663 expanded)
%              Number of equality atoms :   71 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK2),sK2)
        & v4_pre_topc(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK1,X1),X1)
          & v4_pre_topc(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ r1_tarski(k2_tops_1(sK1,sK2),sK2)
    & v4_pre_topc(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f57,f56])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f74])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f24,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f72,f74])).

fof(f92,plain,(
    ~ r1_tarski(k2_tops_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1242,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_1237,plain,
    ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_1622,plain,
    ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1242,c_1237])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_1236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_1627,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1622,c_1236])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1317,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_1318,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_2062,plain,
    ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_33,c_1318])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4736,plain,
    ( r1_tarski(k2_tops_1(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_1245])).

cnf(c_4734,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1245])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_233,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_234])).

cnf(c_538,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_539,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_583,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_283,c_539])).

cnf(c_1235,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_5169,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4734,c_1235])).

cnf(c_11840,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4736,c_5169])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k4_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_1238,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1717,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1242,c_1238])).

cnf(c_24,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,negated_conjecture,
    ( v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_393,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_31,c_30])).

cnf(c_1719,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1717,c_393])).

cnf(c_11846,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_11840,c_1719])).

cnf(c_13,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1248,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3310,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1248])).

cnf(c_11857,plain,
    ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11846,c_3310])).

cnf(c_28,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_35,plain,
    ( r1_tarski(k2_tops_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11857,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:38:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.83/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.97  
% 3.83/0.97  ------  iProver source info
% 3.83/0.97  
% 3.83/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.97  git: non_committed_changes: false
% 3.83/0.97  git: last_make_outside_of_git: false
% 3.83/0.97  
% 3.83/0.97  ------ 
% 3.83/0.97  
% 3.83/0.97  ------ Input Options
% 3.83/0.97  
% 3.83/0.97  --out_options                           all
% 3.83/0.97  --tptp_safe_out                         true
% 3.83/0.97  --problem_path                          ""
% 3.83/0.97  --include_path                          ""
% 3.83/0.97  --clausifier                            res/vclausify_rel
% 3.83/0.97  --clausifier_options                    ""
% 3.83/0.97  --stdin                                 false
% 3.83/0.97  --stats_out                             all
% 3.83/0.97  
% 3.83/0.97  ------ General Options
% 3.83/0.97  
% 3.83/0.97  --fof                                   false
% 3.83/0.97  --time_out_real                         305.
% 3.83/0.97  --time_out_virtual                      -1.
% 3.83/0.97  --symbol_type_check                     false
% 3.83/0.97  --clausify_out                          false
% 3.83/0.97  --sig_cnt_out                           false
% 3.83/0.97  --trig_cnt_out                          false
% 3.83/0.97  --trig_cnt_out_tolerance                1.
% 3.83/0.97  --trig_cnt_out_sk_spl                   false
% 3.83/0.97  --abstr_cl_out                          false
% 3.83/0.97  
% 3.83/0.97  ------ Global Options
% 3.83/0.97  
% 3.83/0.97  --schedule                              default
% 3.83/0.97  --add_important_lit                     false
% 3.83/0.97  --prop_solver_per_cl                    1000
% 3.83/0.97  --min_unsat_core                        false
% 3.83/0.97  --soft_assumptions                      false
% 3.83/0.97  --soft_lemma_size                       3
% 3.83/0.97  --prop_impl_unit_size                   0
% 3.83/0.97  --prop_impl_unit                        []
% 3.83/0.97  --share_sel_clauses                     true
% 3.83/0.97  --reset_solvers                         false
% 3.83/0.97  --bc_imp_inh                            [conj_cone]
% 3.83/0.97  --conj_cone_tolerance                   3.
% 3.83/0.97  --extra_neg_conj                        none
% 3.83/0.97  --large_theory_mode                     true
% 3.83/0.97  --prolific_symb_bound                   200
% 3.83/0.97  --lt_threshold                          2000
% 3.83/0.97  --clause_weak_htbl                      true
% 3.83/0.97  --gc_record_bc_elim                     false
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing Options
% 3.83/0.97  
% 3.83/0.97  --preprocessing_flag                    true
% 3.83/0.97  --time_out_prep_mult                    0.1
% 3.83/0.97  --splitting_mode                        input
% 3.83/0.97  --splitting_grd                         true
% 3.83/0.97  --splitting_cvd                         false
% 3.83/0.97  --splitting_cvd_svl                     false
% 3.83/0.97  --splitting_nvd                         32
% 3.83/0.97  --sub_typing                            true
% 3.83/0.97  --prep_gs_sim                           true
% 3.83/0.97  --prep_unflatten                        true
% 3.83/0.97  --prep_res_sim                          true
% 3.83/0.97  --prep_upred                            true
% 3.83/0.97  --prep_sem_filter                       exhaustive
% 3.83/0.97  --prep_sem_filter_out                   false
% 3.83/0.97  --pred_elim                             true
% 3.83/0.97  --res_sim_input                         true
% 3.83/0.97  --eq_ax_congr_red                       true
% 3.83/0.97  --pure_diseq_elim                       true
% 3.83/0.97  --brand_transform                       false
% 3.83/0.97  --non_eq_to_eq                          false
% 3.83/0.97  --prep_def_merge                        true
% 3.83/0.97  --prep_def_merge_prop_impl              false
% 3.83/0.97  --prep_def_merge_mbd                    true
% 3.83/0.97  --prep_def_merge_tr_red                 false
% 3.83/0.97  --prep_def_merge_tr_cl                  false
% 3.83/0.97  --smt_preprocessing                     true
% 3.83/0.97  --smt_ac_axioms                         fast
% 3.83/0.97  --preprocessed_out                      false
% 3.83/0.97  --preprocessed_stats                    false
% 3.83/0.97  
% 3.83/0.97  ------ Abstraction refinement Options
% 3.83/0.97  
% 3.83/0.97  --abstr_ref                             []
% 3.83/0.97  --abstr_ref_prep                        false
% 3.83/0.97  --abstr_ref_until_sat                   false
% 3.83/0.97  --abstr_ref_sig_restrict                funpre
% 3.83/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.97  --abstr_ref_under                       []
% 3.83/0.97  
% 3.83/0.97  ------ SAT Options
% 3.83/0.97  
% 3.83/0.97  --sat_mode                              false
% 3.83/0.97  --sat_fm_restart_options                ""
% 3.83/0.97  --sat_gr_def                            false
% 3.83/0.97  --sat_epr_types                         true
% 3.83/0.97  --sat_non_cyclic_types                  false
% 3.83/0.97  --sat_finite_models                     false
% 3.83/0.97  --sat_fm_lemmas                         false
% 3.83/0.97  --sat_fm_prep                           false
% 3.83/0.97  --sat_fm_uc_incr                        true
% 3.83/0.97  --sat_out_model                         small
% 3.83/0.97  --sat_out_clauses                       false
% 3.83/0.97  
% 3.83/0.97  ------ QBF Options
% 3.83/0.97  
% 3.83/0.97  --qbf_mode                              false
% 3.83/0.97  --qbf_elim_univ                         false
% 3.83/0.97  --qbf_dom_inst                          none
% 3.83/0.97  --qbf_dom_pre_inst                      false
% 3.83/0.97  --qbf_sk_in                             false
% 3.83/0.97  --qbf_pred_elim                         true
% 3.83/0.97  --qbf_split                             512
% 3.83/0.97  
% 3.83/0.97  ------ BMC1 Options
% 3.83/0.97  
% 3.83/0.97  --bmc1_incremental                      false
% 3.83/0.97  --bmc1_axioms                           reachable_all
% 3.83/0.97  --bmc1_min_bound                        0
% 3.83/0.97  --bmc1_max_bound                        -1
% 3.83/0.97  --bmc1_max_bound_default                -1
% 3.83/0.97  --bmc1_symbol_reachability              true
% 3.83/0.97  --bmc1_property_lemmas                  false
% 3.83/0.97  --bmc1_k_induction                      false
% 3.83/0.97  --bmc1_non_equiv_states                 false
% 3.83/0.97  --bmc1_deadlock                         false
% 3.83/0.97  --bmc1_ucm                              false
% 3.83/0.97  --bmc1_add_unsat_core                   none
% 3.83/0.97  --bmc1_unsat_core_children              false
% 3.83/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.97  --bmc1_out_stat                         full
% 3.83/0.97  --bmc1_ground_init                      false
% 3.83/0.97  --bmc1_pre_inst_next_state              false
% 3.83/0.97  --bmc1_pre_inst_state                   false
% 3.83/0.97  --bmc1_pre_inst_reach_state             false
% 3.83/0.97  --bmc1_out_unsat_core                   false
% 3.83/0.97  --bmc1_aig_witness_out                  false
% 3.83/0.97  --bmc1_verbose                          false
% 3.83/0.97  --bmc1_dump_clauses_tptp                false
% 3.83/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.97  --bmc1_dump_file                        -
% 3.83/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.97  --bmc1_ucm_extend_mode                  1
% 3.83/0.97  --bmc1_ucm_init_mode                    2
% 3.83/0.97  --bmc1_ucm_cone_mode                    none
% 3.83/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.97  --bmc1_ucm_relax_model                  4
% 3.83/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.97  --bmc1_ucm_layered_model                none
% 3.83/0.97  --bmc1_ucm_max_lemma_size               10
% 3.83/0.97  
% 3.83/0.97  ------ AIG Options
% 3.83/0.97  
% 3.83/0.97  --aig_mode                              false
% 3.83/0.97  
% 3.83/0.97  ------ Instantiation Options
% 3.83/0.97  
% 3.83/0.97  --instantiation_flag                    true
% 3.83/0.97  --inst_sos_flag                         true
% 3.83/0.97  --inst_sos_phase                        true
% 3.83/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.97  --inst_lit_sel_side                     num_symb
% 3.83/0.97  --inst_solver_per_active                1400
% 3.83/0.97  --inst_solver_calls_frac                1.
% 3.83/0.97  --inst_passive_queue_type               priority_queues
% 3.83/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.97  --inst_passive_queues_freq              [25;2]
% 3.83/0.97  --inst_dismatching                      true
% 3.83/0.97  --inst_eager_unprocessed_to_passive     true
% 3.83/0.97  --inst_prop_sim_given                   true
% 3.83/0.97  --inst_prop_sim_new                     false
% 3.83/0.97  --inst_subs_new                         false
% 3.83/0.97  --inst_eq_res_simp                      false
% 3.83/0.97  --inst_subs_given                       false
% 3.83/0.97  --inst_orphan_elimination               true
% 3.83/0.97  --inst_learning_loop_flag               true
% 3.83/0.97  --inst_learning_start                   3000
% 3.83/0.97  --inst_learning_factor                  2
% 3.83/0.97  --inst_start_prop_sim_after_learn       3
% 3.83/0.97  --inst_sel_renew                        solver
% 3.83/0.97  --inst_lit_activity_flag                true
% 3.83/0.97  --inst_restr_to_given                   false
% 3.83/0.97  --inst_activity_threshold               500
% 3.83/0.97  --inst_out_proof                        true
% 3.83/0.97  
% 3.83/0.97  ------ Resolution Options
% 3.83/0.97  
% 3.83/0.97  --resolution_flag                       true
% 3.83/0.97  --res_lit_sel                           adaptive
% 3.83/0.97  --res_lit_sel_side                      none
% 3.83/0.97  --res_ordering                          kbo
% 3.83/0.97  --res_to_prop_solver                    active
% 3.83/0.97  --res_prop_simpl_new                    false
% 3.83/0.97  --res_prop_simpl_given                  true
% 3.83/0.97  --res_passive_queue_type                priority_queues
% 3.83/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.97  --res_passive_queues_freq               [15;5]
% 3.83/0.97  --res_forward_subs                      full
% 3.83/0.97  --res_backward_subs                     full
% 3.83/0.97  --res_forward_subs_resolution           true
% 3.83/0.97  --res_backward_subs_resolution          true
% 3.83/0.97  --res_orphan_elimination                true
% 3.83/0.97  --res_time_limit                        2.
% 3.83/0.97  --res_out_proof                         true
% 3.83/0.97  
% 3.83/0.97  ------ Superposition Options
% 3.83/0.97  
% 3.83/0.97  --superposition_flag                    true
% 3.83/0.97  --sup_passive_queue_type                priority_queues
% 3.83/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.83/0.97  --demod_completeness_check              fast
% 3.83/0.97  --demod_use_ground                      true
% 3.83/0.97  --sup_to_prop_solver                    passive
% 3.83/0.97  --sup_prop_simpl_new                    true
% 3.83/0.97  --sup_prop_simpl_given                  true
% 3.83/0.97  --sup_fun_splitting                     true
% 3.83/0.97  --sup_smt_interval                      50000
% 3.83/0.97  
% 3.83/0.97  ------ Superposition Simplification Setup
% 3.83/0.97  
% 3.83/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/0.97  --sup_immed_triv                        [TrivRules]
% 3.83/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.97  --sup_immed_bw_main                     []
% 3.83/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.97  --sup_input_bw                          []
% 3.83/0.97  
% 3.83/0.97  ------ Combination Options
% 3.83/0.97  
% 3.83/0.97  --comb_res_mult                         3
% 3.83/0.97  --comb_sup_mult                         2
% 3.83/0.97  --comb_inst_mult                        10
% 3.83/0.97  
% 3.83/0.97  ------ Debug Options
% 3.83/0.97  
% 3.83/0.97  --dbg_backtrace                         false
% 3.83/0.97  --dbg_dump_prop_clauses                 false
% 3.83/0.97  --dbg_dump_prop_clauses_file            -
% 3.83/0.97  --dbg_out_stat                          false
% 3.83/0.97  ------ Parsing...
% 3.83/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.97  ------ Proving...
% 3.83/0.97  ------ Problem Properties 
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  clauses                                 30
% 3.83/0.97  conjectures                             2
% 3.83/0.97  EPR                                     3
% 3.83/0.97  Horn                                    29
% 3.83/0.97  unary                                   12
% 3.83/0.97  binary                                  16
% 3.83/0.97  lits                                    50
% 3.83/0.97  lits eq                                 13
% 3.83/0.97  fd_pure                                 0
% 3.83/0.97  fd_pseudo                               0
% 3.83/0.97  fd_cond                                 1
% 3.83/0.97  fd_pseudo_cond                          0
% 3.83/0.97  AC symbols                              0
% 3.83/0.97  
% 3.83/0.97  ------ Schedule dynamic 5 is on 
% 3.83/0.97  
% 3.83/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  ------ 
% 3.83/0.97  Current options:
% 3.83/0.97  ------ 
% 3.83/0.97  
% 3.83/0.97  ------ Input Options
% 3.83/0.97  
% 3.83/0.97  --out_options                           all
% 3.83/0.97  --tptp_safe_out                         true
% 3.83/0.97  --problem_path                          ""
% 3.83/0.97  --include_path                          ""
% 3.83/0.97  --clausifier                            res/vclausify_rel
% 3.83/0.97  --clausifier_options                    ""
% 3.83/0.97  --stdin                                 false
% 3.83/0.97  --stats_out                             all
% 3.83/0.97  
% 3.83/0.97  ------ General Options
% 3.83/0.97  
% 3.83/0.97  --fof                                   false
% 3.83/0.97  --time_out_real                         305.
% 3.83/0.97  --time_out_virtual                      -1.
% 3.83/0.97  --symbol_type_check                     false
% 3.83/0.97  --clausify_out                          false
% 3.83/0.97  --sig_cnt_out                           false
% 3.83/0.97  --trig_cnt_out                          false
% 3.83/0.97  --trig_cnt_out_tolerance                1.
% 3.83/0.97  --trig_cnt_out_sk_spl                   false
% 3.83/0.97  --abstr_cl_out                          false
% 3.83/0.97  
% 3.83/0.97  ------ Global Options
% 3.83/0.97  
% 3.83/0.97  --schedule                              default
% 3.83/0.97  --add_important_lit                     false
% 3.83/0.97  --prop_solver_per_cl                    1000
% 3.83/0.97  --min_unsat_core                        false
% 3.83/0.97  --soft_assumptions                      false
% 3.83/0.97  --soft_lemma_size                       3
% 3.83/0.97  --prop_impl_unit_size                   0
% 3.83/0.97  --prop_impl_unit                        []
% 3.83/0.97  --share_sel_clauses                     true
% 3.83/0.97  --reset_solvers                         false
% 3.83/0.97  --bc_imp_inh                            [conj_cone]
% 3.83/0.97  --conj_cone_tolerance                   3.
% 3.83/0.97  --extra_neg_conj                        none
% 3.83/0.97  --large_theory_mode                     true
% 3.83/0.97  --prolific_symb_bound                   200
% 3.83/0.97  --lt_threshold                          2000
% 3.83/0.97  --clause_weak_htbl                      true
% 3.83/0.97  --gc_record_bc_elim                     false
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing Options
% 3.83/0.97  
% 3.83/0.97  --preprocessing_flag                    true
% 3.83/0.97  --time_out_prep_mult                    0.1
% 3.83/0.97  --splitting_mode                        input
% 3.83/0.97  --splitting_grd                         true
% 3.83/0.97  --splitting_cvd                         false
% 3.83/0.97  --splitting_cvd_svl                     false
% 3.83/0.97  --splitting_nvd                         32
% 3.83/0.97  --sub_typing                            true
% 3.83/0.97  --prep_gs_sim                           true
% 3.83/0.97  --prep_unflatten                        true
% 3.83/0.97  --prep_res_sim                          true
% 3.83/0.97  --prep_upred                            true
% 3.83/0.97  --prep_sem_filter                       exhaustive
% 3.83/0.97  --prep_sem_filter_out                   false
% 3.83/0.97  --pred_elim                             true
% 3.83/0.97  --res_sim_input                         true
% 3.83/0.97  --eq_ax_congr_red                       true
% 3.83/0.97  --pure_diseq_elim                       true
% 3.83/0.97  --brand_transform                       false
% 3.83/0.97  --non_eq_to_eq                          false
% 3.83/0.97  --prep_def_merge                        true
% 3.83/0.97  --prep_def_merge_prop_impl              false
% 3.83/0.97  --prep_def_merge_mbd                    true
% 3.83/0.97  --prep_def_merge_tr_red                 false
% 3.83/0.97  --prep_def_merge_tr_cl                  false
% 3.83/0.97  --smt_preprocessing                     true
% 3.83/0.97  --smt_ac_axioms                         fast
% 3.83/0.97  --preprocessed_out                      false
% 3.83/0.97  --preprocessed_stats                    false
% 3.83/0.97  
% 3.83/0.97  ------ Abstraction refinement Options
% 3.83/0.97  
% 3.83/0.97  --abstr_ref                             []
% 3.83/0.97  --abstr_ref_prep                        false
% 3.83/0.97  --abstr_ref_until_sat                   false
% 3.83/0.97  --abstr_ref_sig_restrict                funpre
% 3.83/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.97  --abstr_ref_under                       []
% 3.83/0.97  
% 3.83/0.97  ------ SAT Options
% 3.83/0.97  
% 3.83/0.97  --sat_mode                              false
% 3.83/0.97  --sat_fm_restart_options                ""
% 3.83/0.97  --sat_gr_def                            false
% 3.83/0.97  --sat_epr_types                         true
% 3.83/0.97  --sat_non_cyclic_types                  false
% 3.83/0.97  --sat_finite_models                     false
% 3.83/0.97  --sat_fm_lemmas                         false
% 3.83/0.97  --sat_fm_prep                           false
% 3.83/0.97  --sat_fm_uc_incr                        true
% 3.83/0.97  --sat_out_model                         small
% 3.83/0.97  --sat_out_clauses                       false
% 3.83/0.97  
% 3.83/0.97  ------ QBF Options
% 3.83/0.97  
% 3.83/0.97  --qbf_mode                              false
% 3.83/0.97  --qbf_elim_univ                         false
% 3.83/0.97  --qbf_dom_inst                          none
% 3.83/0.97  --qbf_dom_pre_inst                      false
% 3.83/0.97  --qbf_sk_in                             false
% 3.83/0.97  --qbf_pred_elim                         true
% 3.83/0.97  --qbf_split                             512
% 3.83/0.97  
% 3.83/0.97  ------ BMC1 Options
% 3.83/0.97  
% 3.83/0.97  --bmc1_incremental                      false
% 3.83/0.97  --bmc1_axioms                           reachable_all
% 3.83/0.97  --bmc1_min_bound                        0
% 3.83/0.97  --bmc1_max_bound                        -1
% 3.83/0.97  --bmc1_max_bound_default                -1
% 3.83/0.97  --bmc1_symbol_reachability              true
% 3.83/0.97  --bmc1_property_lemmas                  false
% 3.83/0.97  --bmc1_k_induction                      false
% 3.83/0.97  --bmc1_non_equiv_states                 false
% 3.83/0.97  --bmc1_deadlock                         false
% 3.83/0.97  --bmc1_ucm                              false
% 3.83/0.97  --bmc1_add_unsat_core                   none
% 3.83/0.97  --bmc1_unsat_core_children              false
% 3.83/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.97  --bmc1_out_stat                         full
% 3.83/0.97  --bmc1_ground_init                      false
% 3.83/0.97  --bmc1_pre_inst_next_state              false
% 3.83/0.97  --bmc1_pre_inst_state                   false
% 3.83/0.97  --bmc1_pre_inst_reach_state             false
% 3.83/0.97  --bmc1_out_unsat_core                   false
% 3.83/0.97  --bmc1_aig_witness_out                  false
% 3.83/0.97  --bmc1_verbose                          false
% 3.83/0.97  --bmc1_dump_clauses_tptp                false
% 3.83/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.97  --bmc1_dump_file                        -
% 3.83/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.97  --bmc1_ucm_extend_mode                  1
% 3.83/0.97  --bmc1_ucm_init_mode                    2
% 3.83/0.97  --bmc1_ucm_cone_mode                    none
% 3.83/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.97  --bmc1_ucm_relax_model                  4
% 3.83/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.97  --bmc1_ucm_layered_model                none
% 3.83/0.97  --bmc1_ucm_max_lemma_size               10
% 3.83/0.97  
% 3.83/0.97  ------ AIG Options
% 3.83/0.97  
% 3.83/0.97  --aig_mode                              false
% 3.83/0.97  
% 3.83/0.97  ------ Instantiation Options
% 3.83/0.97  
% 3.83/0.97  --instantiation_flag                    true
% 3.83/0.97  --inst_sos_flag                         true
% 3.83/0.97  --inst_sos_phase                        true
% 3.83/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.97  --inst_lit_sel_side                     none
% 3.83/0.97  --inst_solver_per_active                1400
% 3.83/0.97  --inst_solver_calls_frac                1.
% 3.83/0.97  --inst_passive_queue_type               priority_queues
% 3.83/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.97  --inst_passive_queues_freq              [25;2]
% 3.83/0.97  --inst_dismatching                      true
% 3.83/0.97  --inst_eager_unprocessed_to_passive     true
% 3.83/0.97  --inst_prop_sim_given                   true
% 3.83/0.97  --inst_prop_sim_new                     false
% 3.83/0.97  --inst_subs_new                         false
% 3.83/0.97  --inst_eq_res_simp                      false
% 3.83/0.97  --inst_subs_given                       false
% 3.83/0.97  --inst_orphan_elimination               true
% 3.83/0.97  --inst_learning_loop_flag               true
% 3.83/0.97  --inst_learning_start                   3000
% 3.83/0.97  --inst_learning_factor                  2
% 3.83/0.97  --inst_start_prop_sim_after_learn       3
% 3.83/0.97  --inst_sel_renew                        solver
% 3.83/0.97  --inst_lit_activity_flag                true
% 3.83/0.97  --inst_restr_to_given                   false
% 3.83/0.97  --inst_activity_threshold               500
% 3.83/0.97  --inst_out_proof                        true
% 3.83/0.97  
% 3.83/0.97  ------ Resolution Options
% 3.83/0.97  
% 3.83/0.97  --resolution_flag                       false
% 3.83/0.97  --res_lit_sel                           adaptive
% 3.83/0.97  --res_lit_sel_side                      none
% 3.83/0.97  --res_ordering                          kbo
% 3.83/0.97  --res_to_prop_solver                    active
% 3.83/0.97  --res_prop_simpl_new                    false
% 3.83/0.97  --res_prop_simpl_given                  true
% 3.83/0.97  --res_passive_queue_type                priority_queues
% 3.83/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.97  --res_passive_queues_freq               [15;5]
% 3.83/0.97  --res_forward_subs                      full
% 3.83/0.97  --res_backward_subs                     full
% 3.83/0.97  --res_forward_subs_resolution           true
% 3.83/0.97  --res_backward_subs_resolution          true
% 3.83/0.97  --res_orphan_elimination                true
% 3.83/0.97  --res_time_limit                        2.
% 3.83/0.97  --res_out_proof                         true
% 3.83/0.97  
% 3.83/0.97  ------ Superposition Options
% 3.83/0.97  
% 3.83/0.97  --superposition_flag                    true
% 3.83/0.97  --sup_passive_queue_type                priority_queues
% 3.83/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.83/0.97  --demod_completeness_check              fast
% 3.83/0.97  --demod_use_ground                      true
% 3.83/0.97  --sup_to_prop_solver                    passive
% 3.83/0.97  --sup_prop_simpl_new                    true
% 3.83/0.97  --sup_prop_simpl_given                  true
% 3.83/0.97  --sup_fun_splitting                     true
% 3.83/0.97  --sup_smt_interval                      50000
% 3.83/0.97  
% 3.83/0.97  ------ Superposition Simplification Setup
% 3.83/0.97  
% 3.83/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/0.97  --sup_immed_triv                        [TrivRules]
% 3.83/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.97  --sup_immed_bw_main                     []
% 3.83/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.97  --sup_input_bw                          []
% 3.83/0.97  
% 3.83/0.97  ------ Combination Options
% 3.83/0.97  
% 3.83/0.97  --comb_res_mult                         3
% 3.83/0.97  --comb_sup_mult                         2
% 3.83/0.97  --comb_inst_mult                        10
% 3.83/0.97  
% 3.83/0.97  ------ Debug Options
% 3.83/0.97  
% 3.83/0.97  --dbg_backtrace                         false
% 3.83/0.97  --dbg_dump_prop_clauses                 false
% 3.83/0.97  --dbg_dump_prop_clauses_file            -
% 3.83/0.97  --dbg_out_stat                          false
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  ------ Proving...
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  % SZS status Theorem for theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  fof(f28,conjecture,(
% 3.83/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f29,negated_conjecture,(
% 3.83/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.83/0.97    inference(negated_conjecture,[],[f28])).
% 3.83/0.97  
% 3.83/0.97  fof(f49,plain,(
% 3.83/0.97    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.83/0.97    inference(ennf_transformation,[],[f29])).
% 3.83/0.97  
% 3.83/0.97  fof(f50,plain,(
% 3.83/0.97    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.83/0.97    inference(flattening,[],[f49])).
% 3.83/0.97  
% 3.83/0.97  fof(f57,plain,(
% 3.83/0.97    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK2),sK2) & v4_pre_topc(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f56,plain,(
% 3.83/0.97    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK1,X1),X1) & v4_pre_topc(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 3.83/0.97    introduced(choice_axiom,[])).
% 3.83/0.97  
% 3.83/0.97  fof(f58,plain,(
% 3.83/0.97    (~r1_tarski(k2_tops_1(sK1,sK2),sK2) & v4_pre_topc(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 3.83/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f57,f56])).
% 3.83/0.97  
% 3.83/0.97  fof(f90,plain,(
% 3.83/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.83/0.97    inference(cnf_transformation,[],[f58])).
% 3.83/0.97  
% 3.83/0.97  fof(f26,axiom,(
% 3.83/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f47,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.97    inference(ennf_transformation,[],[f26])).
% 3.83/0.97  
% 3.83/0.97  fof(f87,plain,(
% 3.83/0.97    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f47])).
% 3.83/0.97  
% 3.83/0.97  fof(f89,plain,(
% 3.83/0.97    l1_pre_topc(sK1)),
% 3.83/0.97    inference(cnf_transformation,[],[f58])).
% 3.83/0.97  
% 3.83/0.97  fof(f25,axiom,(
% 3.83/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f45,plain,(
% 3.83/0.97    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.83/0.97    inference(ennf_transformation,[],[f25])).
% 3.83/0.97  
% 3.83/0.97  fof(f46,plain,(
% 3.83/0.97    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.83/0.97    inference(flattening,[],[f45])).
% 3.83/0.97  
% 3.83/0.97  fof(f86,plain,(
% 3.83/0.97    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f46])).
% 3.83/0.97  
% 3.83/0.97  fof(f22,axiom,(
% 3.83/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f55,plain,(
% 3.83/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.83/0.97    inference(nnf_transformation,[],[f22])).
% 3.83/0.97  
% 3.83/0.97  fof(f82,plain,(
% 3.83/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.83/0.97    inference(cnf_transformation,[],[f55])).
% 3.83/0.97  
% 3.83/0.97  fof(f19,axiom,(
% 3.83/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f40,plain,(
% 3.83/0.97    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.83/0.97    inference(ennf_transformation,[],[f19])).
% 3.83/0.97  
% 3.83/0.97  fof(f41,plain,(
% 3.83/0.97    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.83/0.97    inference(flattening,[],[f40])).
% 3.83/0.97  
% 3.83/0.97  fof(f79,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.83/0.97    inference(cnf_transformation,[],[f41])).
% 3.83/0.97  
% 3.83/0.97  fof(f14,axiom,(
% 3.83/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f74,plain,(
% 3.83/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.83/0.97    inference(cnf_transformation,[],[f14])).
% 3.83/0.97  
% 3.83/0.97  fof(f102,plain,(
% 3.83/0.97    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.83/0.97    inference(definition_unfolding,[],[f79,f74])).
% 3.83/0.97  
% 3.83/0.97  fof(f83,plain,(
% 3.83/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f55])).
% 3.83/0.97  
% 3.83/0.97  fof(f27,axiom,(
% 3.83/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f48,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.97    inference(ennf_transformation,[],[f27])).
% 3.83/0.97  
% 3.83/0.97  fof(f88,plain,(
% 3.83/0.97    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f48])).
% 3.83/0.97  
% 3.83/0.97  fof(f24,axiom,(
% 3.83/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f30,plain,(
% 3.83/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.83/0.97    inference(pure_predicate_removal,[],[f24])).
% 3.83/0.97  
% 3.83/0.97  fof(f43,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.97    inference(ennf_transformation,[],[f30])).
% 3.83/0.97  
% 3.83/0.97  fof(f44,plain,(
% 3.83/0.97    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.97    inference(flattening,[],[f43])).
% 3.83/0.97  
% 3.83/0.97  fof(f85,plain,(
% 3.83/0.97    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f44])).
% 3.83/0.97  
% 3.83/0.97  fof(f91,plain,(
% 3.83/0.97    v4_pre_topc(sK2,sK1)),
% 3.83/0.97    inference(cnf_transformation,[],[f58])).
% 3.83/0.97  
% 3.83/0.97  fof(f13,axiom,(
% 3.83/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f73,plain,(
% 3.83/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.83/0.97    inference(cnf_transformation,[],[f13])).
% 3.83/0.97  
% 3.83/0.97  fof(f12,axiom,(
% 3.83/0.97    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.83/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.97  
% 3.83/0.97  fof(f72,plain,(
% 3.83/0.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.83/0.97    inference(cnf_transformation,[],[f12])).
% 3.83/0.97  
% 3.83/0.97  fof(f100,plain,(
% 3.83/0.97    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 3.83/0.97    inference(definition_unfolding,[],[f72,f74])).
% 3.83/0.97  
% 3.83/0.97  fof(f92,plain,(
% 3.83/0.97    ~r1_tarski(k2_tops_1(sK1,sK2),sK2)),
% 3.83/0.97    inference(cnf_transformation,[],[f58])).
% 3.83/0.97  
% 3.83/0.97  cnf(c_30,negated_conjecture,
% 3.83/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.83/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1242,plain,
% 3.83/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_26,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ l1_pre_topc(X1)
% 3.83/0.97      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 3.83/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_31,negated_conjecture,
% 3.83/0.97      ( l1_pre_topc(sK1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_411,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
% 3.83/0.97      | sK1 != X1 ),
% 3.83/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_412,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.83/0.97      | k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_tops_1(sK1,X0) ),
% 3.83/0.97      inference(unflattening,[status(thm)],[c_411]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1237,plain,
% 3.83/0.97      ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),X0)) = k2_tops_1(sK1,X0)
% 3.83/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1622,plain,
% 3.83/0.97      ( k2_tops_1(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_tops_1(sK1,sK2) ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_1242,c_1237]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_25,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ l1_pre_topc(X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f86]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_423,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | sK1 != X1 ),
% 3.83/0.97      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_424,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.83/0.97      | m1_subset_1(k2_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.83/0.97      inference(unflattening,[status(thm)],[c_423]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1236,plain,
% 3.83/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.83/0.97      | m1_subset_1(k2_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1627,plain,
% 3.83/0.97      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.83/0.97      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_1622,c_1236]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_33,plain,
% 3.83/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1317,plain,
% 3.83/0.97      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.83/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.83/0.97      inference(instantiation,[status(thm)],[c_424]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1318,plain,
% 3.83/0.97      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.83/0.97      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_2062,plain,
% 3.83/0.97      ( m1_subset_1(k2_tops_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_1627,c_33,c_1318]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_22,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1245,plain,
% 3.83/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.83/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4736,plain,
% 3.83/0.97      ( r1_tarski(k2_tops_1(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_2062,c_1245]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_4734,plain,
% 3.83/0.97      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_1242,c_1245]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_18,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.83/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.83/0.97      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 3.83/0.97      inference(cnf_transformation,[],[f102]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_21,plain,
% 3.83/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_233,plain,
% 3.83/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.83/0.97      inference(prop_impl,[status(thm)],[c_21]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_234,plain,
% 3.83/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.83/0.97      inference(renaming,[status(thm)],[c_233]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_283,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.83/0.97      | ~ r1_tarski(X2,X1)
% 3.83/0.97      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.83/0.97      inference(bin_hyper_res,[status(thm)],[c_18,c_234]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_538,plain,
% 3.83/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.83/0.97      inference(prop_impl,[status(thm)],[c_21]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_539,plain,
% 3.83/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.83/0.97      inference(renaming,[status(thm)],[c_538]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_583,plain,
% 3.83/0.97      ( ~ r1_tarski(X0,X1)
% 3.83/0.97      | ~ r1_tarski(X2,X1)
% 3.83/0.97      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.83/0.97      inference(bin_hyper_res,[status(thm)],[c_283,c_539]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1235,plain,
% 3.83/0.97      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.83/0.97      | r1_tarski(X2,X0) != iProver_top
% 3.83/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_5169,plain,
% 3.83/0.97      ( k4_subset_1(u1_struct_0(sK1),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 3.83/0.97      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_4734,c_1235]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_11840,plain,
% 3.83/0.97      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_4736,c_5169]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_27,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ l1_pre_topc(X1)
% 3.83/0.97      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.83/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_399,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.83/0.97      | sK1 != X1 ),
% 3.83/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_400,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.83/0.97      | k4_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k2_pre_topc(sK1,X0) ),
% 3.83/0.97      inference(unflattening,[status(thm)],[c_399]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1238,plain,
% 3.83/0.97      ( k4_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k2_pre_topc(sK1,X0)
% 3.83/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1717,plain,
% 3.83/0.97      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k2_pre_topc(sK1,sK2) ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_1242,c_1238]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_24,plain,
% 3.83/0.97      ( ~ v4_pre_topc(X0,X1)
% 3.83/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ l1_pre_topc(X1)
% 3.83/0.97      | k2_pre_topc(X1,X0) = X0 ),
% 3.83/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_29,negated_conjecture,
% 3.83/0.97      ( v4_pre_topc(sK2,sK1) ),
% 3.83/0.97      inference(cnf_transformation,[],[f91]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_390,plain,
% 3.83/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.97      | ~ l1_pre_topc(X1)
% 3.83/0.97      | k2_pre_topc(X1,X0) = X0
% 3.83/0.97      | sK2 != X0
% 3.83/0.97      | sK1 != X1 ),
% 3.83/0.97      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_391,plain,
% 3.83/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.83/0.97      | ~ l1_pre_topc(sK1)
% 3.83/0.97      | k2_pre_topc(sK1,sK2) = sK2 ),
% 3.83/0.97      inference(unflattening,[status(thm)],[c_390]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_393,plain,
% 3.83/0.97      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 3.83/0.97      inference(global_propositional_subsumption,
% 3.83/0.97                [status(thm)],
% 3.83/0.97                [c_391,c_31,c_30]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1719,plain,
% 3.83/0.97      ( k4_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = sK2 ),
% 3.83/0.97      inference(light_normalisation,[status(thm)],[c_1717,c_393]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_11846,plain,
% 3.83/0.97      ( k3_tarski(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = sK2 ),
% 3.83/0.97      inference(light_normalisation,[status(thm)],[c_11840,c_1719]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_13,plain,
% 3.83/0.97      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.83/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_12,plain,
% 3.83/0.97      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 3.83/0.97      inference(cnf_transformation,[],[f100]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_1248,plain,
% 3.83/0.97      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_3310,plain,
% 3.83/0.97      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_13,c_1248]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_11857,plain,
% 3.83/0.97      ( r1_tarski(k2_tops_1(sK1,sK2),sK2) = iProver_top ),
% 3.83/0.97      inference(superposition,[status(thm)],[c_11846,c_3310]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_28,negated_conjecture,
% 3.83/0.97      ( ~ r1_tarski(k2_tops_1(sK1,sK2),sK2) ),
% 3.83/0.97      inference(cnf_transformation,[],[f92]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(c_35,plain,
% 3.83/0.97      ( r1_tarski(k2_tops_1(sK1,sK2),sK2) != iProver_top ),
% 3.83/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.83/0.97  
% 3.83/0.97  cnf(contradiction,plain,
% 3.83/0.97      ( $false ),
% 3.83/0.97      inference(minisat,[status(thm)],[c_11857,c_35]) ).
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.97  
% 3.83/0.97  ------                               Statistics
% 3.83/0.97  
% 3.83/0.97  ------ General
% 3.83/0.97  
% 3.83/0.97  abstr_ref_over_cycles:                  0
% 3.83/0.97  abstr_ref_under_cycles:                 0
% 3.83/0.97  gc_basic_clause_elim:                   0
% 3.83/0.97  forced_gc_time:                         0
% 3.83/0.97  parsing_time:                           0.012
% 3.83/0.97  unif_index_cands_time:                  0.
% 3.83/0.97  unif_index_add_time:                    0.
% 3.83/0.97  orderings_time:                         0.
% 3.83/0.97  out_proof_time:                         0.01
% 3.83/0.97  total_time:                             0.447
% 3.83/0.97  num_of_symbols:                         52
% 3.83/0.97  num_of_terms:                           14133
% 3.83/0.97  
% 3.83/0.97  ------ Preprocessing
% 3.83/0.97  
% 3.83/0.97  num_of_splits:                          0
% 3.83/0.97  num_of_split_atoms:                     0
% 3.83/0.97  num_of_reused_defs:                     0
% 3.83/0.97  num_eq_ax_congr_red:                    32
% 3.83/0.97  num_of_sem_filtered_clauses:            1
% 3.83/0.97  num_of_subtypes:                        0
% 3.83/0.97  monotx_restored_types:                  0
% 3.83/0.97  sat_num_of_epr_types:                   0
% 3.83/0.97  sat_num_of_non_cyclic_types:            0
% 3.83/0.97  sat_guarded_non_collapsed_types:        0
% 3.83/0.97  num_pure_diseq_elim:                    0
% 3.83/0.97  simp_replaced_by:                       0
% 3.83/0.97  res_preprocessed:                       153
% 3.83/0.97  prep_upred:                             0
% 3.83/0.97  prep_unflattend:                        5
% 3.83/0.97  smt_new_axioms:                         0
% 3.83/0.97  pred_elim_cands:                        3
% 3.83/0.97  pred_elim:                              2
% 3.83/0.97  pred_elim_cl:                           2
% 3.83/0.97  pred_elim_cycles:                       4
% 3.83/0.97  merged_defs:                            16
% 3.83/0.97  merged_defs_ncl:                        0
% 3.83/0.97  bin_hyper_res:                          21
% 3.83/0.97  prep_cycles:                            4
% 3.83/0.97  pred_elim_time:                         0.001
% 3.83/0.97  splitting_time:                         0.
% 3.83/0.97  sem_filter_time:                        0.
% 3.83/0.97  monotx_time:                            0.001
% 3.83/0.97  subtype_inf_time:                       0.
% 3.83/0.97  
% 3.83/0.97  ------ Problem properties
% 3.83/0.97  
% 3.83/0.97  clauses:                                30
% 3.83/0.97  conjectures:                            2
% 3.83/0.97  epr:                                    3
% 3.83/0.97  horn:                                   29
% 3.83/0.97  ground:                                 3
% 3.83/0.97  unary:                                  12
% 3.83/0.97  binary:                                 16
% 3.83/0.97  lits:                                   50
% 3.83/0.97  lits_eq:                                13
% 3.83/0.97  fd_pure:                                0
% 3.83/0.97  fd_pseudo:                              0
% 3.83/0.97  fd_cond:                                1
% 3.83/0.97  fd_pseudo_cond:                         0
% 3.83/0.97  ac_symbols:                             0
% 3.83/0.97  
% 3.83/0.97  ------ Propositional Solver
% 3.83/0.97  
% 3.83/0.97  prop_solver_calls:                      30
% 3.83/0.97  prop_fast_solver_calls:                 826
% 3.83/0.97  smt_solver_calls:                       0
% 3.83/0.97  smt_fast_solver_calls:                  0
% 3.83/0.97  prop_num_of_clauses:                    5704
% 3.83/0.97  prop_preprocess_simplified:             11779
% 3.83/0.97  prop_fo_subsumed:                       7
% 3.83/0.97  prop_solver_time:                       0.
% 3.83/0.97  smt_solver_time:                        0.
% 3.83/0.97  smt_fast_solver_time:                   0.
% 3.83/0.97  prop_fast_solver_time:                  0.
% 3.83/0.97  prop_unsat_core_time:                   0.
% 3.83/0.97  
% 3.83/0.97  ------ QBF
% 3.83/0.97  
% 3.83/0.97  qbf_q_res:                              0
% 3.83/0.97  qbf_num_tautologies:                    0
% 3.83/0.97  qbf_prep_cycles:                        0
% 3.83/0.97  
% 3.83/0.97  ------ BMC1
% 3.83/0.97  
% 3.83/0.97  bmc1_current_bound:                     -1
% 3.83/0.97  bmc1_last_solved_bound:                 -1
% 3.83/0.97  bmc1_unsat_core_size:                   -1
% 3.83/0.97  bmc1_unsat_core_parents_size:           -1
% 3.83/0.97  bmc1_merge_next_fun:                    0
% 3.83/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.83/0.97  
% 3.83/0.97  ------ Instantiation
% 3.83/0.97  
% 3.83/0.97  inst_num_of_clauses:                    1309
% 3.83/0.97  inst_num_in_passive:                    559
% 3.83/0.97  inst_num_in_active:                     605
% 3.83/0.97  inst_num_in_unprocessed:                147
% 3.83/0.97  inst_num_of_loops:                      710
% 3.83/0.97  inst_num_of_learning_restarts:          0
% 3.83/0.97  inst_num_moves_active_passive:          104
% 3.83/0.97  inst_lit_activity:                      0
% 3.83/0.97  inst_lit_activity_moves:                0
% 3.83/0.97  inst_num_tautologies:                   0
% 3.83/0.97  inst_num_prop_implied:                  0
% 3.83/0.97  inst_num_existing_simplified:           0
% 3.83/0.97  inst_num_eq_res_simplified:             0
% 3.83/0.97  inst_num_child_elim:                    0
% 3.83/0.97  inst_num_of_dismatching_blockings:      855
% 3.83/0.97  inst_num_of_non_proper_insts:           1398
% 3.83/0.97  inst_num_of_duplicates:                 0
% 3.83/0.97  inst_inst_num_from_inst_to_res:         0
% 3.83/0.97  inst_dismatching_checking_time:         0.
% 3.83/0.97  
% 3.83/0.97  ------ Resolution
% 3.83/0.97  
% 3.83/0.97  res_num_of_clauses:                     0
% 3.83/0.97  res_num_in_passive:                     0
% 3.83/0.97  res_num_in_active:                      0
% 3.83/0.97  res_num_of_loops:                       157
% 3.83/0.97  res_forward_subset_subsumed:            94
% 3.83/0.97  res_backward_subset_subsumed:           4
% 3.83/0.97  res_forward_subsumed:                   0
% 3.83/0.97  res_backward_subsumed:                  0
% 3.83/0.97  res_forward_subsumption_resolution:     0
% 3.83/0.97  res_backward_subsumption_resolution:    0
% 3.83/0.97  res_clause_to_clause_subsumption:       3131
% 3.83/0.97  res_orphan_elimination:                 0
% 3.83/0.97  res_tautology_del:                      124
% 3.83/0.97  res_num_eq_res_simplified:              0
% 3.83/0.97  res_num_sel_changes:                    0
% 3.83/0.97  res_moves_from_active_to_pass:          0
% 3.83/0.97  
% 3.83/0.97  ------ Superposition
% 3.83/0.97  
% 3.83/0.97  sup_time_total:                         0.
% 3.83/0.97  sup_time_generating:                    0.
% 3.83/0.97  sup_time_sim_full:                      0.
% 3.83/0.97  sup_time_sim_immed:                     0.
% 3.83/0.97  
% 3.83/0.97  sup_num_of_clauses:                     556
% 3.83/0.97  sup_num_in_active:                      139
% 3.83/0.97  sup_num_in_passive:                     417
% 3.83/0.97  sup_num_of_loops:                       141
% 3.83/0.97  sup_fw_superposition:                   596
% 3.83/0.97  sup_bw_superposition:                   419
% 3.83/0.97  sup_immediate_simplified:               126
% 3.83/0.97  sup_given_eliminated:                   0
% 3.83/0.97  comparisons_done:                       0
% 3.83/0.97  comparisons_avoided:                    0
% 3.83/0.97  
% 3.83/0.97  ------ Simplifications
% 3.83/0.97  
% 3.83/0.97  
% 3.83/0.97  sim_fw_subset_subsumed:                 5
% 3.83/0.97  sim_bw_subset_subsumed:                 0
% 3.83/0.97  sim_fw_subsumed:                        8
% 3.83/0.97  sim_bw_subsumed:                        0
% 3.83/0.97  sim_fw_subsumption_res:                 0
% 3.83/0.97  sim_bw_subsumption_res:                 0
% 3.83/0.97  sim_tautology_del:                      11
% 3.83/0.97  sim_eq_tautology_del:                   13
% 3.83/0.97  sim_eq_res_simp:                        0
% 3.83/0.97  sim_fw_demodulated:                     17
% 3.83/0.97  sim_bw_demodulated:                     18
% 3.83/0.97  sim_light_normalised:                   91
% 3.83/0.97  sim_joinable_taut:                      0
% 3.83/0.97  sim_joinable_simp:                      0
% 3.83/0.97  sim_ac_normalised:                      0
% 3.83/0.97  sim_smt_subsumption:                    0
% 3.83/0.97  
%------------------------------------------------------------------------------
