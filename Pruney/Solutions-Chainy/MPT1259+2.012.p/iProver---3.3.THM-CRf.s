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
% DateTime   : Thu Dec  3 12:14:16 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 256 expanded)
%              Number of clauses        :   51 (  83 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  231 ( 812 expanded)
%              Number of equality atoms :  105 ( 253 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_tops_1(X0,k2_tops_1(X0,sK1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,sK1)))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30,f29])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_710,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_706,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_707,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_1137,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,X0)),k1_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_tops_1(sK0,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_707])).

cnf(c_2534,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_1137])).

cnf(c_6294,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_710,c_2534])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_14])).

cnf(c_709,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_1021,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_710,c_709])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_14])).

cnf(c_708,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_925,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_tops_1(sK0,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_708])).

cnf(c_1702,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_710,c_925])).

cnf(c_6306,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_6294,c_1021,c_1702])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_715,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_712,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1407,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_715,c_712])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_714,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1302,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_715,c_714])).

cnf(c_2027,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1407,c_1302])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_711,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1826,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) = k4_xboole_0(k2_tops_1(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_711])).

cnf(c_2660,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,X0)),X1) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_1826])).

cnf(c_3585,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_710,c_2660])).

cnf(c_6307,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_6306,c_2027,c_3585])).

cnf(c_403,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_961,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_404,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_811,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) != X0
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_960,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) != k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_12,negated_conjecture,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6307,c_961,c_960,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:24:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.55/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.03  
% 2.55/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/1.03  
% 2.55/1.03  ------  iProver source info
% 2.55/1.03  
% 2.55/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.55/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/1.03  git: non_committed_changes: false
% 2.55/1.03  git: last_make_outside_of_git: false
% 2.55/1.03  
% 2.55/1.03  ------ 
% 2.55/1.03  
% 2.55/1.03  ------ Input Options
% 2.55/1.03  
% 2.55/1.03  --out_options                           all
% 2.55/1.03  --tptp_safe_out                         true
% 2.55/1.03  --problem_path                          ""
% 2.55/1.03  --include_path                          ""
% 2.55/1.03  --clausifier                            res/vclausify_rel
% 2.55/1.03  --clausifier_options                    --mode clausify
% 2.55/1.03  --stdin                                 false
% 2.55/1.03  --stats_out                             all
% 2.55/1.03  
% 2.55/1.03  ------ General Options
% 2.55/1.03  
% 2.55/1.03  --fof                                   false
% 2.55/1.03  --time_out_real                         305.
% 2.55/1.03  --time_out_virtual                      -1.
% 2.55/1.03  --symbol_type_check                     false
% 2.55/1.03  --clausify_out                          false
% 2.55/1.03  --sig_cnt_out                           false
% 2.55/1.03  --trig_cnt_out                          false
% 2.55/1.03  --trig_cnt_out_tolerance                1.
% 2.55/1.03  --trig_cnt_out_sk_spl                   false
% 2.55/1.03  --abstr_cl_out                          false
% 2.55/1.03  
% 2.55/1.03  ------ Global Options
% 2.55/1.03  
% 2.55/1.03  --schedule                              default
% 2.55/1.03  --add_important_lit                     false
% 2.55/1.03  --prop_solver_per_cl                    1000
% 2.55/1.03  --min_unsat_core                        false
% 2.55/1.03  --soft_assumptions                      false
% 2.55/1.03  --soft_lemma_size                       3
% 2.55/1.03  --prop_impl_unit_size                   0
% 2.55/1.03  --prop_impl_unit                        []
% 2.55/1.03  --share_sel_clauses                     true
% 2.55/1.03  --reset_solvers                         false
% 2.55/1.03  --bc_imp_inh                            [conj_cone]
% 2.55/1.03  --conj_cone_tolerance                   3.
% 2.55/1.03  --extra_neg_conj                        none
% 2.55/1.03  --large_theory_mode                     true
% 2.55/1.03  --prolific_symb_bound                   200
% 2.55/1.03  --lt_threshold                          2000
% 2.55/1.03  --clause_weak_htbl                      true
% 2.55/1.03  --gc_record_bc_elim                     false
% 2.55/1.03  
% 2.55/1.03  ------ Preprocessing Options
% 2.55/1.03  
% 2.55/1.03  --preprocessing_flag                    true
% 2.55/1.03  --time_out_prep_mult                    0.1
% 2.55/1.03  --splitting_mode                        input
% 2.55/1.03  --splitting_grd                         true
% 2.55/1.03  --splitting_cvd                         false
% 2.55/1.03  --splitting_cvd_svl                     false
% 2.55/1.03  --splitting_nvd                         32
% 2.55/1.03  --sub_typing                            true
% 2.55/1.03  --prep_gs_sim                           true
% 2.55/1.03  --prep_unflatten                        true
% 2.55/1.03  --prep_res_sim                          true
% 2.55/1.03  --prep_upred                            true
% 2.55/1.03  --prep_sem_filter                       exhaustive
% 2.55/1.03  --prep_sem_filter_out                   false
% 2.55/1.03  --pred_elim                             true
% 2.55/1.03  --res_sim_input                         true
% 2.55/1.03  --eq_ax_congr_red                       true
% 2.55/1.03  --pure_diseq_elim                       true
% 2.55/1.03  --brand_transform                       false
% 2.55/1.03  --non_eq_to_eq                          false
% 2.55/1.03  --prep_def_merge                        true
% 2.55/1.03  --prep_def_merge_prop_impl              false
% 2.55/1.03  --prep_def_merge_mbd                    true
% 2.55/1.03  --prep_def_merge_tr_red                 false
% 2.55/1.03  --prep_def_merge_tr_cl                  false
% 2.55/1.03  --smt_preprocessing                     true
% 2.55/1.03  --smt_ac_axioms                         fast
% 2.55/1.03  --preprocessed_out                      false
% 2.55/1.03  --preprocessed_stats                    false
% 2.55/1.03  
% 2.55/1.03  ------ Abstraction refinement Options
% 2.55/1.03  
% 2.55/1.03  --abstr_ref                             []
% 2.55/1.03  --abstr_ref_prep                        false
% 2.55/1.03  --abstr_ref_until_sat                   false
% 2.55/1.03  --abstr_ref_sig_restrict                funpre
% 2.55/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.03  --abstr_ref_under                       []
% 2.55/1.03  
% 2.55/1.03  ------ SAT Options
% 2.55/1.03  
% 2.55/1.03  --sat_mode                              false
% 2.55/1.03  --sat_fm_restart_options                ""
% 2.55/1.03  --sat_gr_def                            false
% 2.55/1.03  --sat_epr_types                         true
% 2.55/1.03  --sat_non_cyclic_types                  false
% 2.55/1.03  --sat_finite_models                     false
% 2.55/1.03  --sat_fm_lemmas                         false
% 2.55/1.03  --sat_fm_prep                           false
% 2.55/1.03  --sat_fm_uc_incr                        true
% 2.55/1.03  --sat_out_model                         small
% 2.55/1.03  --sat_out_clauses                       false
% 2.55/1.03  
% 2.55/1.03  ------ QBF Options
% 2.55/1.03  
% 2.55/1.03  --qbf_mode                              false
% 2.55/1.03  --qbf_elim_univ                         false
% 2.55/1.03  --qbf_dom_inst                          none
% 2.55/1.03  --qbf_dom_pre_inst                      false
% 2.55/1.03  --qbf_sk_in                             false
% 2.55/1.03  --qbf_pred_elim                         true
% 2.55/1.03  --qbf_split                             512
% 2.55/1.03  
% 2.55/1.03  ------ BMC1 Options
% 2.55/1.03  
% 2.55/1.03  --bmc1_incremental                      false
% 2.55/1.03  --bmc1_axioms                           reachable_all
% 2.55/1.03  --bmc1_min_bound                        0
% 2.55/1.03  --bmc1_max_bound                        -1
% 2.55/1.03  --bmc1_max_bound_default                -1
% 2.55/1.03  --bmc1_symbol_reachability              true
% 2.55/1.03  --bmc1_property_lemmas                  false
% 2.55/1.03  --bmc1_k_induction                      false
% 2.55/1.03  --bmc1_non_equiv_states                 false
% 2.55/1.03  --bmc1_deadlock                         false
% 2.55/1.03  --bmc1_ucm                              false
% 2.55/1.03  --bmc1_add_unsat_core                   none
% 2.55/1.03  --bmc1_unsat_core_children              false
% 2.55/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.03  --bmc1_out_stat                         full
% 2.55/1.03  --bmc1_ground_init                      false
% 2.55/1.03  --bmc1_pre_inst_next_state              false
% 2.55/1.03  --bmc1_pre_inst_state                   false
% 2.55/1.03  --bmc1_pre_inst_reach_state             false
% 2.55/1.03  --bmc1_out_unsat_core                   false
% 2.55/1.03  --bmc1_aig_witness_out                  false
% 2.55/1.03  --bmc1_verbose                          false
% 2.55/1.03  --bmc1_dump_clauses_tptp                false
% 2.55/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.03  --bmc1_dump_file                        -
% 2.55/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.03  --bmc1_ucm_extend_mode                  1
% 2.55/1.03  --bmc1_ucm_init_mode                    2
% 2.55/1.03  --bmc1_ucm_cone_mode                    none
% 2.55/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.03  --bmc1_ucm_relax_model                  4
% 2.55/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.03  --bmc1_ucm_layered_model                none
% 2.55/1.03  --bmc1_ucm_max_lemma_size               10
% 2.55/1.03  
% 2.55/1.03  ------ AIG Options
% 2.55/1.03  
% 2.55/1.03  --aig_mode                              false
% 2.55/1.03  
% 2.55/1.03  ------ Instantiation Options
% 2.55/1.03  
% 2.55/1.03  --instantiation_flag                    true
% 2.55/1.03  --inst_sos_flag                         false
% 2.55/1.03  --inst_sos_phase                        true
% 2.55/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.03  --inst_lit_sel_side                     num_symb
% 2.55/1.03  --inst_solver_per_active                1400
% 2.55/1.03  --inst_solver_calls_frac                1.
% 2.55/1.03  --inst_passive_queue_type               priority_queues
% 2.55/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.03  --inst_passive_queues_freq              [25;2]
% 2.55/1.03  --inst_dismatching                      true
% 2.55/1.03  --inst_eager_unprocessed_to_passive     true
% 2.55/1.03  --inst_prop_sim_given                   true
% 2.55/1.03  --inst_prop_sim_new                     false
% 2.55/1.03  --inst_subs_new                         false
% 2.55/1.03  --inst_eq_res_simp                      false
% 2.55/1.03  --inst_subs_given                       false
% 2.55/1.03  --inst_orphan_elimination               true
% 2.55/1.03  --inst_learning_loop_flag               true
% 2.55/1.03  --inst_learning_start                   3000
% 2.55/1.03  --inst_learning_factor                  2
% 2.55/1.03  --inst_start_prop_sim_after_learn       3
% 2.55/1.03  --inst_sel_renew                        solver
% 2.55/1.03  --inst_lit_activity_flag                true
% 2.55/1.03  --inst_restr_to_given                   false
% 2.55/1.03  --inst_activity_threshold               500
% 2.55/1.03  --inst_out_proof                        true
% 2.55/1.03  
% 2.55/1.03  ------ Resolution Options
% 2.55/1.03  
% 2.55/1.03  --resolution_flag                       true
% 2.55/1.03  --res_lit_sel                           adaptive
% 2.55/1.03  --res_lit_sel_side                      none
% 2.55/1.03  --res_ordering                          kbo
% 2.55/1.03  --res_to_prop_solver                    active
% 2.55/1.03  --res_prop_simpl_new                    false
% 2.55/1.03  --res_prop_simpl_given                  true
% 2.55/1.03  --res_passive_queue_type                priority_queues
% 2.55/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.03  --res_passive_queues_freq               [15;5]
% 2.55/1.03  --res_forward_subs                      full
% 2.55/1.03  --res_backward_subs                     full
% 2.55/1.03  --res_forward_subs_resolution           true
% 2.55/1.03  --res_backward_subs_resolution          true
% 2.55/1.03  --res_orphan_elimination                true
% 2.55/1.03  --res_time_limit                        2.
% 2.55/1.03  --res_out_proof                         true
% 2.55/1.03  
% 2.55/1.03  ------ Superposition Options
% 2.55/1.03  
% 2.55/1.03  --superposition_flag                    true
% 2.55/1.03  --sup_passive_queue_type                priority_queues
% 2.55/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.03  --demod_completeness_check              fast
% 2.55/1.03  --demod_use_ground                      true
% 2.55/1.03  --sup_to_prop_solver                    passive
% 2.55/1.03  --sup_prop_simpl_new                    true
% 2.55/1.03  --sup_prop_simpl_given                  true
% 2.55/1.03  --sup_fun_splitting                     false
% 2.55/1.03  --sup_smt_interval                      50000
% 2.55/1.03  
% 2.55/1.03  ------ Superposition Simplification Setup
% 2.55/1.03  
% 2.55/1.03  --sup_indices_passive                   []
% 2.55/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.03  --sup_full_bw                           [BwDemod]
% 2.55/1.03  --sup_immed_triv                        [TrivRules]
% 2.55/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.03  --sup_immed_bw_main                     []
% 2.55/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.03  
% 2.55/1.03  ------ Combination Options
% 2.55/1.03  
% 2.55/1.03  --comb_res_mult                         3
% 2.55/1.03  --comb_sup_mult                         2
% 2.55/1.03  --comb_inst_mult                        10
% 2.55/1.03  
% 2.55/1.03  ------ Debug Options
% 2.55/1.03  
% 2.55/1.03  --dbg_backtrace                         false
% 2.55/1.03  --dbg_dump_prop_clauses                 false
% 2.55/1.03  --dbg_dump_prop_clauses_file            -
% 2.55/1.03  --dbg_out_stat                          false
% 2.55/1.03  ------ Parsing...
% 2.55/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/1.03  
% 2.55/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.55/1.03  
% 2.55/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/1.03  
% 2.55/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/1.03  ------ Proving...
% 2.55/1.03  ------ Problem Properties 
% 2.55/1.03  
% 2.55/1.03  
% 2.55/1.03  clauses                                 13
% 2.55/1.03  conjectures                             2
% 2.55/1.03  EPR                                     2
% 2.55/1.03  Horn                                    13
% 2.55/1.03  unary                                   3
% 2.55/1.03  binary                                  9
% 2.55/1.03  lits                                    24
% 2.55/1.03  lits eq                                 9
% 2.55/1.03  fd_pure                                 0
% 2.55/1.03  fd_pseudo                               0
% 2.55/1.03  fd_cond                                 0
% 2.55/1.03  fd_pseudo_cond                          1
% 2.55/1.03  AC symbols                              0
% 2.55/1.03  
% 2.55/1.03  ------ Schedule dynamic 5 is on 
% 2.55/1.03  
% 2.55/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/1.03  
% 2.55/1.03  
% 2.55/1.03  ------ 
% 2.55/1.03  Current options:
% 2.55/1.03  ------ 
% 2.55/1.03  
% 2.55/1.03  ------ Input Options
% 2.55/1.03  
% 2.55/1.03  --out_options                           all
% 2.55/1.03  --tptp_safe_out                         true
% 2.55/1.03  --problem_path                          ""
% 2.55/1.03  --include_path                          ""
% 2.55/1.03  --clausifier                            res/vclausify_rel
% 2.55/1.03  --clausifier_options                    --mode clausify
% 2.55/1.03  --stdin                                 false
% 2.55/1.03  --stats_out                             all
% 2.55/1.03  
% 2.55/1.03  ------ General Options
% 2.55/1.03  
% 2.55/1.03  --fof                                   false
% 2.55/1.03  --time_out_real                         305.
% 2.55/1.03  --time_out_virtual                      -1.
% 2.55/1.03  --symbol_type_check                     false
% 2.55/1.03  --clausify_out                          false
% 2.55/1.03  --sig_cnt_out                           false
% 2.55/1.03  --trig_cnt_out                          false
% 2.55/1.03  --trig_cnt_out_tolerance                1.
% 2.55/1.03  --trig_cnt_out_sk_spl                   false
% 2.55/1.03  --abstr_cl_out                          false
% 2.55/1.03  
% 2.55/1.03  ------ Global Options
% 2.55/1.03  
% 2.55/1.03  --schedule                              default
% 2.55/1.03  --add_important_lit                     false
% 2.55/1.03  --prop_solver_per_cl                    1000
% 2.55/1.03  --min_unsat_core                        false
% 2.55/1.03  --soft_assumptions                      false
% 2.55/1.03  --soft_lemma_size                       3
% 2.55/1.03  --prop_impl_unit_size                   0
% 2.55/1.03  --prop_impl_unit                        []
% 2.55/1.03  --share_sel_clauses                     true
% 2.55/1.03  --reset_solvers                         false
% 2.55/1.03  --bc_imp_inh                            [conj_cone]
% 2.55/1.03  --conj_cone_tolerance                   3.
% 2.55/1.03  --extra_neg_conj                        none
% 2.55/1.03  --large_theory_mode                     true
% 2.55/1.03  --prolific_symb_bound                   200
% 2.55/1.03  --lt_threshold                          2000
% 2.55/1.03  --clause_weak_htbl                      true
% 2.55/1.03  --gc_record_bc_elim                     false
% 2.55/1.03  
% 2.55/1.03  ------ Preprocessing Options
% 2.55/1.03  
% 2.55/1.03  --preprocessing_flag                    true
% 2.55/1.03  --time_out_prep_mult                    0.1
% 2.55/1.03  --splitting_mode                        input
% 2.55/1.03  --splitting_grd                         true
% 2.55/1.03  --splitting_cvd                         false
% 2.55/1.03  --splitting_cvd_svl                     false
% 2.55/1.03  --splitting_nvd                         32
% 2.55/1.03  --sub_typing                            true
% 2.55/1.03  --prep_gs_sim                           true
% 2.55/1.03  --prep_unflatten                        true
% 2.55/1.03  --prep_res_sim                          true
% 2.55/1.03  --prep_upred                            true
% 2.55/1.03  --prep_sem_filter                       exhaustive
% 2.55/1.03  --prep_sem_filter_out                   false
% 2.55/1.03  --pred_elim                             true
% 2.55/1.03  --res_sim_input                         true
% 2.55/1.03  --eq_ax_congr_red                       true
% 2.55/1.03  --pure_diseq_elim                       true
% 2.55/1.03  --brand_transform                       false
% 2.55/1.03  --non_eq_to_eq                          false
% 2.55/1.03  --prep_def_merge                        true
% 2.55/1.03  --prep_def_merge_prop_impl              false
% 2.55/1.03  --prep_def_merge_mbd                    true
% 2.55/1.03  --prep_def_merge_tr_red                 false
% 2.55/1.03  --prep_def_merge_tr_cl                  false
% 2.55/1.03  --smt_preprocessing                     true
% 2.55/1.03  --smt_ac_axioms                         fast
% 2.55/1.03  --preprocessed_out                      false
% 2.55/1.03  --preprocessed_stats                    false
% 2.55/1.03  
% 2.55/1.03  ------ Abstraction refinement Options
% 2.55/1.03  
% 2.55/1.03  --abstr_ref                             []
% 2.55/1.03  --abstr_ref_prep                        false
% 2.55/1.03  --abstr_ref_until_sat                   false
% 2.55/1.03  --abstr_ref_sig_restrict                funpre
% 2.55/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.03  --abstr_ref_under                       []
% 2.55/1.03  
% 2.55/1.03  ------ SAT Options
% 2.55/1.03  
% 2.55/1.03  --sat_mode                              false
% 2.55/1.03  --sat_fm_restart_options                ""
% 2.55/1.03  --sat_gr_def                            false
% 2.55/1.03  --sat_epr_types                         true
% 2.55/1.03  --sat_non_cyclic_types                  false
% 2.55/1.03  --sat_finite_models                     false
% 2.55/1.03  --sat_fm_lemmas                         false
% 2.55/1.03  --sat_fm_prep                           false
% 2.55/1.03  --sat_fm_uc_incr                        true
% 2.55/1.03  --sat_out_model                         small
% 2.55/1.03  --sat_out_clauses                       false
% 2.55/1.03  
% 2.55/1.03  ------ QBF Options
% 2.55/1.03  
% 2.55/1.03  --qbf_mode                              false
% 2.55/1.03  --qbf_elim_univ                         false
% 2.55/1.03  --qbf_dom_inst                          none
% 2.55/1.03  --qbf_dom_pre_inst                      false
% 2.55/1.03  --qbf_sk_in                             false
% 2.55/1.03  --qbf_pred_elim                         true
% 2.55/1.03  --qbf_split                             512
% 2.55/1.03  
% 2.55/1.03  ------ BMC1 Options
% 2.55/1.03  
% 2.55/1.03  --bmc1_incremental                      false
% 2.55/1.03  --bmc1_axioms                           reachable_all
% 2.55/1.03  --bmc1_min_bound                        0
% 2.55/1.03  --bmc1_max_bound                        -1
% 2.55/1.03  --bmc1_max_bound_default                -1
% 2.55/1.03  --bmc1_symbol_reachability              true
% 2.55/1.03  --bmc1_property_lemmas                  false
% 2.55/1.03  --bmc1_k_induction                      false
% 2.55/1.03  --bmc1_non_equiv_states                 false
% 2.55/1.03  --bmc1_deadlock                         false
% 2.55/1.03  --bmc1_ucm                              false
% 2.55/1.03  --bmc1_add_unsat_core                   none
% 2.55/1.03  --bmc1_unsat_core_children              false
% 2.55/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.03  --bmc1_out_stat                         full
% 2.55/1.03  --bmc1_ground_init                      false
% 2.55/1.03  --bmc1_pre_inst_next_state              false
% 2.55/1.03  --bmc1_pre_inst_state                   false
% 2.55/1.03  --bmc1_pre_inst_reach_state             false
% 2.55/1.03  --bmc1_out_unsat_core                   false
% 2.55/1.03  --bmc1_aig_witness_out                  false
% 2.55/1.03  --bmc1_verbose                          false
% 2.55/1.03  --bmc1_dump_clauses_tptp                false
% 2.55/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.03  --bmc1_dump_file                        -
% 2.55/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.03  --bmc1_ucm_extend_mode                  1
% 2.55/1.03  --bmc1_ucm_init_mode                    2
% 2.55/1.03  --bmc1_ucm_cone_mode                    none
% 2.55/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.03  --bmc1_ucm_relax_model                  4
% 2.55/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.03  --bmc1_ucm_layered_model                none
% 2.55/1.03  --bmc1_ucm_max_lemma_size               10
% 2.55/1.03  
% 2.55/1.03  ------ AIG Options
% 2.55/1.03  
% 2.55/1.03  --aig_mode                              false
% 2.55/1.03  
% 2.55/1.03  ------ Instantiation Options
% 2.55/1.03  
% 2.55/1.03  --instantiation_flag                    true
% 2.55/1.03  --inst_sos_flag                         false
% 2.55/1.03  --inst_sos_phase                        true
% 2.55/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.03  --inst_lit_sel_side                     none
% 2.55/1.03  --inst_solver_per_active                1400
% 2.55/1.03  --inst_solver_calls_frac                1.
% 2.55/1.03  --inst_passive_queue_type               priority_queues
% 2.55/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.03  --inst_passive_queues_freq              [25;2]
% 2.55/1.03  --inst_dismatching                      true
% 2.55/1.03  --inst_eager_unprocessed_to_passive     true
% 2.55/1.03  --inst_prop_sim_given                   true
% 2.55/1.03  --inst_prop_sim_new                     false
% 2.55/1.03  --inst_subs_new                         false
% 2.55/1.03  --inst_eq_res_simp                      false
% 2.55/1.03  --inst_subs_given                       false
% 2.55/1.03  --inst_orphan_elimination               true
% 2.55/1.03  --inst_learning_loop_flag               true
% 2.55/1.03  --inst_learning_start                   3000
% 2.55/1.03  --inst_learning_factor                  2
% 2.55/1.03  --inst_start_prop_sim_after_learn       3
% 2.55/1.03  --inst_sel_renew                        solver
% 2.55/1.03  --inst_lit_activity_flag                true
% 2.55/1.03  --inst_restr_to_given                   false
% 2.55/1.03  --inst_activity_threshold               500
% 2.55/1.03  --inst_out_proof                        true
% 2.55/1.03  
% 2.55/1.03  ------ Resolution Options
% 2.55/1.03  
% 2.55/1.03  --resolution_flag                       false
% 2.55/1.03  --res_lit_sel                           adaptive
% 2.55/1.03  --res_lit_sel_side                      none
% 2.55/1.03  --res_ordering                          kbo
% 2.55/1.03  --res_to_prop_solver                    active
% 2.55/1.03  --res_prop_simpl_new                    false
% 2.55/1.03  --res_prop_simpl_given                  true
% 2.55/1.03  --res_passive_queue_type                priority_queues
% 2.55/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.03  --res_passive_queues_freq               [15;5]
% 2.55/1.03  --res_forward_subs                      full
% 2.55/1.03  --res_backward_subs                     full
% 2.55/1.03  --res_forward_subs_resolution           true
% 2.55/1.03  --res_backward_subs_resolution          true
% 2.55/1.03  --res_orphan_elimination                true
% 2.55/1.03  --res_time_limit                        2.
% 2.55/1.03  --res_out_proof                         true
% 2.55/1.03  
% 2.55/1.03  ------ Superposition Options
% 2.55/1.03  
% 2.55/1.03  --superposition_flag                    true
% 2.55/1.03  --sup_passive_queue_type                priority_queues
% 2.55/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.03  --demod_completeness_check              fast
% 2.55/1.03  --demod_use_ground                      true
% 2.55/1.03  --sup_to_prop_solver                    passive
% 2.55/1.03  --sup_prop_simpl_new                    true
% 2.55/1.03  --sup_prop_simpl_given                  true
% 2.55/1.03  --sup_fun_splitting                     false
% 2.55/1.03  --sup_smt_interval                      50000
% 2.55/1.03  
% 2.55/1.03  ------ Superposition Simplification Setup
% 2.55/1.03  
% 2.55/1.03  --sup_indices_passive                   []
% 2.55/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.03  --sup_full_bw                           [BwDemod]
% 2.55/1.03  --sup_immed_triv                        [TrivRules]
% 2.55/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.03  --sup_immed_bw_main                     []
% 2.55/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.03  
% 2.55/1.03  ------ Combination Options
% 2.55/1.03  
% 2.55/1.03  --comb_res_mult                         3
% 2.55/1.03  --comb_sup_mult                         2
% 2.55/1.03  --comb_inst_mult                        10
% 2.55/1.03  
% 2.55/1.03  ------ Debug Options
% 2.55/1.03  
% 2.55/1.03  --dbg_backtrace                         false
% 2.55/1.03  --dbg_dump_prop_clauses                 false
% 2.55/1.03  --dbg_dump_prop_clauses_file            -
% 2.55/1.03  --dbg_out_stat                          false
% 2.55/1.03  
% 2.55/1.03  
% 2.55/1.03  
% 2.55/1.03  
% 2.55/1.03  ------ Proving...
% 2.55/1.03  
% 2.55/1.03  
% 2.55/1.03  % SZS status Theorem for theBenchmark.p
% 2.55/1.03  
% 2.55/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/1.03  
% 2.55/1.03  fof(f11,conjecture,(
% 2.55/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f12,negated_conjecture,(
% 2.55/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.55/1.03    inference(negated_conjecture,[],[f11])).
% 2.55/1.03  
% 2.55/1.03  fof(f24,plain,(
% 2.55/1.03    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.55/1.03    inference(ennf_transformation,[],[f12])).
% 2.55/1.03  
% 2.55/1.03  fof(f25,plain,(
% 2.55/1.03    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.55/1.03    inference(flattening,[],[f24])).
% 2.55/1.03  
% 2.55/1.03  fof(f30,plain,(
% 2.55/1.03    ( ! [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_tops_1(X0,k2_tops_1(X0,sK1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.55/1.03    introduced(choice_axiom,[])).
% 2.55/1.03  
% 2.55/1.03  fof(f29,plain,(
% 2.55/1.03    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.55/1.03    introduced(choice_axiom,[])).
% 2.55/1.03  
% 2.55/1.03  fof(f31,plain,(
% 2.55/1.03    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.55/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30,f29])).
% 2.55/1.03  
% 2.55/1.03  fof(f47,plain,(
% 2.55/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.55/1.03    inference(cnf_transformation,[],[f31])).
% 2.55/1.03  
% 2.55/1.03  fof(f7,axiom,(
% 2.55/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f17,plain,(
% 2.55/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.55/1.03    inference(ennf_transformation,[],[f7])).
% 2.55/1.03  
% 2.55/1.03  fof(f18,plain,(
% 2.55/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.55/1.03    inference(flattening,[],[f17])).
% 2.55/1.03  
% 2.55/1.03  fof(f41,plain,(
% 2.55/1.03    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f18])).
% 2.55/1.03  
% 2.55/1.03  fof(f46,plain,(
% 2.55/1.03    l1_pre_topc(sK0)),
% 2.55/1.03    inference(cnf_transformation,[],[f31])).
% 2.55/1.03  
% 2.55/1.03  fof(f8,axiom,(
% 2.55/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f19,plain,(
% 2.55/1.03    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.55/1.03    inference(ennf_transformation,[],[f8])).
% 2.55/1.03  
% 2.55/1.03  fof(f42,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f19])).
% 2.55/1.03  
% 2.55/1.03  fof(f10,axiom,(
% 2.55/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f22,plain,(
% 2.55/1.03    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.55/1.03    inference(ennf_transformation,[],[f10])).
% 2.55/1.03  
% 2.55/1.03  fof(f23,plain,(
% 2.55/1.03    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.55/1.03    inference(flattening,[],[f22])).
% 2.55/1.03  
% 2.55/1.03  fof(f44,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f23])).
% 2.55/1.03  
% 2.55/1.03  fof(f45,plain,(
% 2.55/1.03    v2_pre_topc(sK0)),
% 2.55/1.03    inference(cnf_transformation,[],[f31])).
% 2.55/1.03  
% 2.55/1.03  fof(f9,axiom,(
% 2.55/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f20,plain,(
% 2.55/1.03    ! [X0] : (! [X1] : (k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.55/1.03    inference(ennf_transformation,[],[f9])).
% 2.55/1.03  
% 2.55/1.03  fof(f21,plain,(
% 2.55/1.03    ! [X0] : (! [X1] : (k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.55/1.03    inference(flattening,[],[f20])).
% 2.55/1.03  
% 2.55/1.03  fof(f43,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f21])).
% 2.55/1.03  
% 2.55/1.03  fof(f1,axiom,(
% 2.55/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f26,plain,(
% 2.55/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.55/1.03    inference(nnf_transformation,[],[f1])).
% 2.55/1.03  
% 2.55/1.03  fof(f27,plain,(
% 2.55/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.55/1.03    inference(flattening,[],[f26])).
% 2.55/1.03  
% 2.55/1.03  fof(f32,plain,(
% 2.55/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.55/1.03    inference(cnf_transformation,[],[f27])).
% 2.55/1.03  
% 2.55/1.03  fof(f51,plain,(
% 2.55/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.55/1.03    inference(equality_resolution,[],[f32])).
% 2.55/1.03  
% 2.55/1.03  fof(f3,axiom,(
% 2.55/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f13,plain,(
% 2.55/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.55/1.03    inference(ennf_transformation,[],[f3])).
% 2.55/1.03  
% 2.55/1.03  fof(f37,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f13])).
% 2.55/1.03  
% 2.55/1.03  fof(f4,axiom,(
% 2.55/1.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f38,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f4])).
% 2.55/1.03  
% 2.55/1.03  fof(f49,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.55/1.03    inference(definition_unfolding,[],[f37,f38])).
% 2.55/1.03  
% 2.55/1.03  fof(f2,axiom,(
% 2.55/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f28,plain,(
% 2.55/1.03    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.55/1.03    inference(nnf_transformation,[],[f2])).
% 2.55/1.03  
% 2.55/1.03  fof(f36,plain,(
% 2.55/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.55/1.03    inference(cnf_transformation,[],[f28])).
% 2.55/1.03  
% 2.55/1.03  fof(f5,axiom,(
% 2.55/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.55/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/1.03  
% 2.55/1.03  fof(f14,plain,(
% 2.55/1.03    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.55/1.03    inference(ennf_transformation,[],[f5])).
% 2.55/1.03  
% 2.55/1.03  fof(f39,plain,(
% 2.55/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/1.03    inference(cnf_transformation,[],[f14])).
% 2.55/1.03  
% 2.55/1.03  fof(f48,plain,(
% 2.55/1.03    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.55/1.03    inference(cnf_transformation,[],[f31])).
% 2.55/1.03  
% 2.55/1.03  cnf(c_13,negated_conjecture,
% 2.55/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.55/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_710,plain,
% 2.55/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_8,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | ~ l1_pre_topc(X1) ),
% 2.55/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_14,negated_conjecture,
% 2.55/1.03      ( l1_pre_topc(sK0) ),
% 2.55/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_253,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | sK0 != X1 ),
% 2.55/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_254,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.55/1.03      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.55/1.03      inference(unflattening,[status(thm)],[c_253]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_706,plain,
% 2.55/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.55/1.03      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_9,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | ~ l1_pre_topc(X1)
% 2.55/1.03      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.55/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_241,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.55/1.03      | sK0 != X1 ),
% 2.55/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_242,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.55/1.03      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.55/1.03      inference(unflattening,[status(thm)],[c_241]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_707,plain,
% 2.55/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.55/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_1137,plain,
% 2.55/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,X0)),k1_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_tops_1(sK0,k2_tops_1(sK0,X0))
% 2.55/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_706,c_707]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_2534,plain,
% 2.55/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))
% 2.55/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_706,c_1137]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_6294,plain,
% 2.55/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_710,c_2534]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_11,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | ~ v2_pre_topc(X1)
% 2.55/1.03      | ~ l1_pre_topc(X1)
% 2.55/1.03      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 2.55/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_15,negated_conjecture,
% 2.55/1.03      ( v2_pre_topc(sK0) ),
% 2.55/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_199,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | ~ l1_pre_topc(X1)
% 2.55/1.03      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
% 2.55/1.03      | sK0 != X1 ),
% 2.55/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_200,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.55/1.03      | ~ l1_pre_topc(sK0)
% 2.55/1.03      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 2.55/1.03      inference(unflattening,[status(thm)],[c_199]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_204,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.55/1.03      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 2.55/1.03      inference(global_propositional_subsumption,
% 2.55/1.03                [status(thm)],
% 2.55/1.03                [c_200,c_14]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_709,plain,
% 2.55/1.03      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
% 2.55/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_1021,plain,
% 2.55/1.03      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_710,c_709]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_10,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | ~ v2_pre_topc(X1)
% 2.55/1.03      | ~ l1_pre_topc(X1)
% 2.55/1.03      | k2_pre_topc(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.55/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_217,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.55/1.03      | ~ l1_pre_topc(X1)
% 2.55/1.03      | k2_pre_topc(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.55/1.03      | sK0 != X1 ),
% 2.55/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_218,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.55/1.03      | ~ l1_pre_topc(sK0)
% 2.55/1.03      | k2_pre_topc(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.55/1.03      inference(unflattening,[status(thm)],[c_217]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_222,plain,
% 2.55/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.55/1.03      | k2_pre_topc(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.55/1.03      inference(global_propositional_subsumption,
% 2.55/1.03                [status(thm)],
% 2.55/1.03                [c_218,c_14]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_708,plain,
% 2.55/1.03      ( k2_pre_topc(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.55/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_925,plain,
% 2.55/1.03      ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_tops_1(sK0,k2_tops_1(sK0,X0))
% 2.55/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_706,c_708]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_1702,plain,
% 2.55/1.03      ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_710,c_925]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_6306,plain,
% 2.55/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 2.55/1.03      inference(light_normalisation,[status(thm)],[c_6294,c_1021,c_1702]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_2,plain,
% 2.55/1.03      ( r1_tarski(X0,X0) ),
% 2.55/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_715,plain,
% 2.55/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_5,plain,
% 2.55/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.55/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_712,plain,
% 2.55/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 2.55/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.55/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_1407,plain,
% 2.55/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.55/1.03      inference(superposition,[status(thm)],[c_715,c_712]) ).
% 2.55/1.03  
% 2.55/1.03  cnf(c_3,plain,
% 2.55/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.55/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_714,plain,
% 2.55/1.04      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.55/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 2.55/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_1302,plain,
% 2.55/1.04      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.55/1.04      inference(superposition,[status(thm)],[c_715,c_714]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_2027,plain,
% 2.55/1.04      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.55/1.04      inference(light_normalisation,[status(thm)],[c_1407,c_1302]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_6,plain,
% 2.55/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.55/1.04      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.55/1.04      inference(cnf_transformation,[],[f39]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_711,plain,
% 2.55/1.04      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.55/1.04      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.55/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_1826,plain,
% 2.55/1.04      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1) = k4_xboole_0(k2_tops_1(sK0,X0),X1)
% 2.55/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.04      inference(superposition,[status(thm)],[c_706,c_711]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_2660,plain,
% 2.55/1.04      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,X0)),X1) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,X0)),X1)
% 2.55/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.55/1.04      inference(superposition,[status(thm)],[c_706,c_1826]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_3585,plain,
% 2.55/1.04      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
% 2.55/1.04      inference(superposition,[status(thm)],[c_710,c_2660]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_6307,plain,
% 2.55/1.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 2.55/1.04      inference(demodulation,[status(thm)],[c_6306,c_2027,c_3585]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_403,plain,( X0 = X0 ),theory(equality) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_961,plain,
% 2.55/1.04      ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 2.55/1.04      inference(instantiation,[status(thm)],[c_403]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_404,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_811,plain,
% 2.55/1.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) != X0
% 2.55/1.04      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0
% 2.55/1.04      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 2.55/1.04      inference(instantiation,[status(thm)],[c_404]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_960,plain,
% 2.55/1.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) != k2_tops_1(sK0,k2_tops_1(sK0,sK1))
% 2.55/1.04      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
% 2.55/1.04      | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 2.55/1.04      inference(instantiation,[status(thm)],[c_811]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(c_12,negated_conjecture,
% 2.55/1.04      ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 2.55/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.55/1.04  
% 2.55/1.04  cnf(contradiction,plain,
% 2.55/1.04      ( $false ),
% 2.55/1.04      inference(minisat,[status(thm)],[c_6307,c_961,c_960,c_12]) ).
% 2.55/1.04  
% 2.55/1.04  
% 2.55/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/1.04  
% 2.55/1.04  ------                               Statistics
% 2.55/1.04  
% 2.55/1.04  ------ General
% 2.55/1.04  
% 2.55/1.04  abstr_ref_over_cycles:                  0
% 2.55/1.04  abstr_ref_under_cycles:                 0
% 2.55/1.04  gc_basic_clause_elim:                   0
% 2.55/1.04  forced_gc_time:                         0
% 2.55/1.04  parsing_time:                           0.009
% 2.55/1.04  unif_index_cands_time:                  0.
% 2.55/1.04  unif_index_add_time:                    0.
% 2.55/1.04  orderings_time:                         0.
% 2.55/1.04  out_proof_time:                         0.007
% 2.55/1.04  total_time:                             0.198
% 2.55/1.04  num_of_symbols:                         45
% 2.55/1.04  num_of_terms:                           5307
% 2.55/1.04  
% 2.55/1.04  ------ Preprocessing
% 2.55/1.04  
% 2.55/1.04  num_of_splits:                          0
% 2.55/1.04  num_of_split_atoms:                     0
% 2.55/1.04  num_of_reused_defs:                     0
% 2.55/1.04  num_eq_ax_congr_red:                    11
% 2.55/1.04  num_of_sem_filtered_clauses:            1
% 2.55/1.04  num_of_subtypes:                        0
% 2.55/1.04  monotx_restored_types:                  0
% 2.55/1.04  sat_num_of_epr_types:                   0
% 2.55/1.04  sat_num_of_non_cyclic_types:            0
% 2.55/1.04  sat_guarded_non_collapsed_types:        0
% 2.55/1.04  num_pure_diseq_elim:                    0
% 2.55/1.04  simp_replaced_by:                       0
% 2.55/1.04  res_preprocessed:                       75
% 2.55/1.04  prep_upred:                             0
% 2.55/1.04  prep_unflattend:                        5
% 2.55/1.04  smt_new_axioms:                         0
% 2.55/1.04  pred_elim_cands:                        2
% 2.55/1.04  pred_elim:                              2
% 2.55/1.04  pred_elim_cl:                           2
% 2.55/1.04  pred_elim_cycles:                       4
% 2.55/1.04  merged_defs:                            8
% 2.55/1.04  merged_defs_ncl:                        0
% 2.55/1.04  bin_hyper_res:                          8
% 2.55/1.04  prep_cycles:                            4
% 2.55/1.04  pred_elim_time:                         0.014
% 2.55/1.04  splitting_time:                         0.
% 2.55/1.04  sem_filter_time:                        0.
% 2.55/1.04  monotx_time:                            0.
% 2.55/1.04  subtype_inf_time:                       0.
% 2.55/1.04  
% 2.55/1.04  ------ Problem properties
% 2.55/1.04  
% 2.55/1.04  clauses:                                13
% 2.55/1.04  conjectures:                            2
% 2.55/1.04  epr:                                    2
% 2.55/1.04  horn:                                   13
% 2.55/1.04  ground:                                 2
% 2.55/1.04  unary:                                  3
% 2.55/1.04  binary:                                 9
% 2.55/1.04  lits:                                   24
% 2.55/1.04  lits_eq:                                9
% 2.55/1.04  fd_pure:                                0
% 2.55/1.04  fd_pseudo:                              0
% 2.55/1.04  fd_cond:                                0
% 2.55/1.04  fd_pseudo_cond:                         1
% 2.55/1.04  ac_symbols:                             0
% 2.55/1.04  
% 2.55/1.04  ------ Propositional Solver
% 2.55/1.04  
% 2.55/1.04  prop_solver_calls:                      28
% 2.55/1.04  prop_fast_solver_calls:                 469
% 2.55/1.04  smt_solver_calls:                       0
% 2.55/1.04  smt_fast_solver_calls:                  0
% 2.55/1.04  prop_num_of_clauses:                    2954
% 2.55/1.04  prop_preprocess_simplified:             7104
% 2.55/1.04  prop_fo_subsumed:                       2
% 2.55/1.04  prop_solver_time:                       0.
% 2.55/1.04  smt_solver_time:                        0.
% 2.55/1.04  smt_fast_solver_time:                   0.
% 2.55/1.04  prop_fast_solver_time:                  0.
% 2.55/1.04  prop_unsat_core_time:                   0.
% 2.55/1.04  
% 2.55/1.04  ------ QBF
% 2.55/1.04  
% 2.55/1.04  qbf_q_res:                              0
% 2.55/1.04  qbf_num_tautologies:                    0
% 2.55/1.04  qbf_prep_cycles:                        0
% 2.55/1.04  
% 2.55/1.04  ------ BMC1
% 2.55/1.04  
% 2.55/1.04  bmc1_current_bound:                     -1
% 2.55/1.04  bmc1_last_solved_bound:                 -1
% 2.55/1.04  bmc1_unsat_core_size:                   -1
% 2.55/1.04  bmc1_unsat_core_parents_size:           -1
% 2.55/1.04  bmc1_merge_next_fun:                    0
% 2.55/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.55/1.04  
% 2.55/1.04  ------ Instantiation
% 2.55/1.04  
% 2.55/1.04  inst_num_of_clauses:                    959
% 2.55/1.04  inst_num_in_passive:                    498
% 2.55/1.04  inst_num_in_active:                     418
% 2.55/1.04  inst_num_in_unprocessed:                43
% 2.55/1.04  inst_num_of_loops:                      420
% 2.55/1.04  inst_num_of_learning_restarts:          0
% 2.55/1.04  inst_num_moves_active_passive:          0
% 2.55/1.04  inst_lit_activity:                      0
% 2.55/1.04  inst_lit_activity_moves:                0
% 2.55/1.04  inst_num_tautologies:                   0
% 2.55/1.04  inst_num_prop_implied:                  0
% 2.55/1.04  inst_num_existing_simplified:           0
% 2.55/1.04  inst_num_eq_res_simplified:             0
% 2.55/1.04  inst_num_child_elim:                    0
% 2.55/1.04  inst_num_of_dismatching_blockings:      49
% 2.55/1.04  inst_num_of_non_proper_insts:           682
% 2.55/1.04  inst_num_of_duplicates:                 0
% 2.55/1.04  inst_inst_num_from_inst_to_res:         0
% 2.55/1.04  inst_dismatching_checking_time:         0.
% 2.55/1.04  
% 2.55/1.04  ------ Resolution
% 2.55/1.04  
% 2.55/1.04  res_num_of_clauses:                     0
% 2.55/1.04  res_num_in_passive:                     0
% 2.55/1.04  res_num_in_active:                      0
% 2.55/1.04  res_num_of_loops:                       79
% 2.55/1.04  res_forward_subset_subsumed:            48
% 2.55/1.04  res_backward_subset_subsumed:           0
% 2.55/1.04  res_forward_subsumed:                   0
% 2.55/1.04  res_backward_subsumed:                  0
% 2.55/1.04  res_forward_subsumption_resolution:     0
% 2.55/1.04  res_backward_subsumption_resolution:    0
% 2.55/1.04  res_clause_to_clause_subsumption:       533
% 2.55/1.04  res_orphan_elimination:                 0
% 2.55/1.04  res_tautology_del:                      55
% 2.55/1.04  res_num_eq_res_simplified:              0
% 2.55/1.04  res_num_sel_changes:                    0
% 2.55/1.04  res_moves_from_active_to_pass:          0
% 2.55/1.04  
% 2.55/1.04  ------ Superposition
% 2.55/1.04  
% 2.55/1.04  sup_time_total:                         0.
% 2.55/1.04  sup_time_generating:                    0.
% 2.55/1.04  sup_time_sim_full:                      0.
% 2.55/1.04  sup_time_sim_immed:                     0.
% 2.55/1.04  
% 2.55/1.04  sup_num_of_clauses:                     134
% 2.55/1.04  sup_num_in_active:                      83
% 2.55/1.04  sup_num_in_passive:                     51
% 2.55/1.04  sup_num_of_loops:                       82
% 2.55/1.04  sup_fw_superposition:                   120
% 2.55/1.04  sup_bw_superposition:                   14
% 2.55/1.04  sup_immediate_simplified:               12
% 2.55/1.04  sup_given_eliminated:                   0
% 2.55/1.04  comparisons_done:                       0
% 2.55/1.04  comparisons_avoided:                    0
% 2.55/1.04  
% 2.55/1.04  ------ Simplifications
% 2.55/1.04  
% 2.55/1.04  
% 2.55/1.04  sim_fw_subset_subsumed:                 0
% 2.55/1.04  sim_bw_subset_subsumed:                 0
% 2.55/1.04  sim_fw_subsumed:                        1
% 2.55/1.04  sim_bw_subsumed:                        0
% 2.55/1.04  sim_fw_subsumption_res:                 0
% 2.55/1.04  sim_bw_subsumption_res:                 0
% 2.55/1.04  sim_tautology_del:                      3
% 2.55/1.04  sim_eq_tautology_del:                   10
% 2.55/1.04  sim_eq_res_simp:                        0
% 2.55/1.04  sim_fw_demodulated:                     1
% 2.55/1.04  sim_bw_demodulated:                     0
% 2.55/1.04  sim_light_normalised:                   12
% 2.55/1.04  sim_joinable_taut:                      0
% 2.55/1.04  sim_joinable_simp:                      0
% 2.55/1.04  sim_ac_normalised:                      0
% 2.55/1.04  sim_smt_subsumption:                    0
% 2.55/1.04  
%------------------------------------------------------------------------------
