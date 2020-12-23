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
% DateTime   : Thu Dec  3 12:13:46 EST 2020

% Result     : Theorem 43.65s
% Output     : CNFRefutation 43.65s
% Verified   : 
% Statistics : Number of formulae       :  154 (1983 expanded)
%              Number of clauses        :  106 ( 695 expanded)
%              Number of leaves         :   14 ( 539 expanded)
%              Depth                    :   21
%              Number of atoms          :  398 (6302 expanded)
%              Number of equality atoms :  191 ( 834 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_614,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_613,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_622,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X2),X3) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_622])).

cnf(c_17530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_2103])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19055,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17530,c_16])).

cnf(c_19056,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19055])).

cnf(c_19064,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_19056])).

cnf(c_19090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_19064])).

cnf(c_18,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_50641,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19090,c_16,c_18])).

cnf(c_50642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_50641])).

cnf(c_17529,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_2103])).

cnf(c_18639,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17529,c_16])).

cnf(c_18640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18639])).

cnf(c_18649,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_18640])).

cnf(c_50660,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_50642,c_18649])).

cnf(c_32818,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(sK2,X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_32823,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32818])).

cnf(c_51585,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50660,c_16,c_18,c_32823])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2335,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_617])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_761,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_762,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_2781,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2335,c_16,c_17,c_762])).

cnf(c_2787,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2781,c_622])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_620,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_618,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1225,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_618])).

cnf(c_2334,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_617])).

cnf(c_758,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_759,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_2753,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2334,c_16,c_18,c_759])).

cnf(c_2759,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_622])).

cnf(c_2914,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2759,c_622])).

cnf(c_6921,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_2914])).

cnf(c_808,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_9,c_13])).

cnf(c_809,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_827,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | r1_tarski(X0,u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1344,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_2496,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_2497,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(c_7208,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6921,c_16,c_18,c_759,c_809,c_2497])).

cnf(c_3088,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_622])).

cnf(c_9432,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_3088])).

cnf(c_810,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_9,c_14])).

cnf(c_811,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_1350,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_2524,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_2525,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_9596,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9432,c_16,c_17,c_762,c_811,c_2525])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_98,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_99,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_98])).

cnf(c_125,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_99])).

cnf(c_199,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_199])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_125,c_200])).

cnf(c_611,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_9602,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9596,c_611])).

cnf(c_81600,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_7208,c_9602])).

cnf(c_1226,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_618])).

cnf(c_1615,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_611])).

cnf(c_3304,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1225,c_1615])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_615,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3992,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3304,c_615])).

cnf(c_84843,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_81600,c_3992])).

cnf(c_84847,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_84843])).

cnf(c_177609,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_84847])).

cnf(c_831,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1674,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k3_tarski(k2_tarski(X0,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2537,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_2538,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2537])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1454,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14027,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_14028,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14027])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_623,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_619,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19063,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_19056])).

cnf(c_28531,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_19063])).

cnf(c_177610,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28531,c_84847])).

cnf(c_177652,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_177609,c_809,c_811,c_2538,c_14028,c_177610])).

cnf(c_177662,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51585,c_177652])).

cnf(c_18647,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_18640])).

cnf(c_27479,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_18647])).

cnf(c_177661,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27479,c_177652])).

cnf(c_177717,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_177662,c_809,c_811,c_2538,c_177661])).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_621,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_987,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_621])).

cnf(c_177722,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_177717,c_987])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.65/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.65/5.99  
% 43.65/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.65/5.99  
% 43.65/5.99  ------  iProver source info
% 43.65/5.99  
% 43.65/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.65/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.65/5.99  git: non_committed_changes: false
% 43.65/5.99  git: last_make_outside_of_git: false
% 43.65/5.99  
% 43.65/5.99  ------ 
% 43.65/5.99  ------ Parsing...
% 43.65/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.65/5.99  
% 43.65/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 43.65/5.99  
% 43.65/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.65/5.99  
% 43.65/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.65/5.99  ------ Proving...
% 43.65/5.99  ------ Problem Properties 
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  clauses                                 15
% 43.65/5.99  conjectures                             4
% 43.65/5.99  EPR                                     4
% 43.65/5.99  Horn                                    15
% 43.65/5.99  unary                                   7
% 43.65/5.99  binary                                  2
% 43.65/5.99  lits                                    31
% 43.65/5.99  lits eq                                 3
% 43.65/5.99  fd_pure                                 0
% 43.65/5.99  fd_pseudo                               0
% 43.65/5.99  fd_cond                                 0
% 43.65/5.99  fd_pseudo_cond                          1
% 43.65/5.99  AC symbols                              0
% 43.65/5.99  
% 43.65/5.99  ------ Input Options Time Limit: Unbounded
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  ------ 
% 43.65/5.99  Current options:
% 43.65/5.99  ------ 
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  ------ Proving...
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  % SZS status Theorem for theBenchmark.p
% 43.65/5.99  
% 43.65/5.99   Resolution empty clause
% 43.65/5.99  
% 43.65/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.65/5.99  
% 43.65/5.99  fof(f10,axiom,(
% 43.65/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f20,plain,(
% 43.65/5.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.65/5.99    inference(ennf_transformation,[],[f10])).
% 43.65/5.99  
% 43.65/5.99  fof(f21,plain,(
% 43.65/5.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.65/5.99    inference(flattening,[],[f20])).
% 43.65/5.99  
% 43.65/5.99  fof(f42,plain,(
% 43.65/5.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.65/5.99    inference(cnf_transformation,[],[f21])).
% 43.65/5.99  
% 43.65/5.99  fof(f11,conjecture,(
% 43.65/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f12,negated_conjecture,(
% 43.65/5.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 43.65/5.99    inference(negated_conjecture,[],[f11])).
% 43.65/5.99  
% 43.65/5.99  fof(f22,plain,(
% 43.65/5.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 43.65/5.99    inference(ennf_transformation,[],[f12])).
% 43.65/5.99  
% 43.65/5.99  fof(f28,plain,(
% 43.65/5.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.65/5.99    introduced(choice_axiom,[])).
% 43.65/5.99  
% 43.65/5.99  fof(f27,plain,(
% 43.65/5.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.65/5.99    introduced(choice_axiom,[])).
% 43.65/5.99  
% 43.65/5.99  fof(f26,plain,(
% 43.65/5.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 43.65/5.99    introduced(choice_axiom,[])).
% 43.65/5.99  
% 43.65/5.99  fof(f29,plain,(
% 43.65/5.99    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 43.65/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).
% 43.65/5.99  
% 43.65/5.99  fof(f45,plain,(
% 43.65/5.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 43.65/5.99    inference(cnf_transformation,[],[f29])).
% 43.65/5.99  
% 43.65/5.99  fof(f44,plain,(
% 43.65/5.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 43.65/5.99    inference(cnf_transformation,[],[f29])).
% 43.65/5.99  
% 43.65/5.99  fof(f2,axiom,(
% 43.65/5.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f13,plain,(
% 43.65/5.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.65/5.99    inference(ennf_transformation,[],[f2])).
% 43.65/5.99  
% 43.65/5.99  fof(f14,plain,(
% 43.65/5.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 43.65/5.99    inference(flattening,[],[f13])).
% 43.65/5.99  
% 43.65/5.99  fof(f33,plain,(
% 43.65/5.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.65/5.99    inference(cnf_transformation,[],[f14])).
% 43.65/5.99  
% 43.65/5.99  fof(f43,plain,(
% 43.65/5.99    l1_pre_topc(sK0)),
% 43.65/5.99    inference(cnf_transformation,[],[f29])).
% 43.65/5.99  
% 43.65/5.99  fof(f9,axiom,(
% 43.65/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f19,plain,(
% 43.65/5.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.65/5.99    inference(ennf_transformation,[],[f9])).
% 43.65/5.99  
% 43.65/5.99  fof(f41,plain,(
% 43.65/5.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.65/5.99    inference(cnf_transformation,[],[f19])).
% 43.65/5.99  
% 43.65/5.99  fof(f4,axiom,(
% 43.65/5.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f15,plain,(
% 43.65/5.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 43.65/5.99    inference(ennf_transformation,[],[f4])).
% 43.65/5.99  
% 43.65/5.99  fof(f16,plain,(
% 43.65/5.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 43.65/5.99    inference(flattening,[],[f15])).
% 43.65/5.99  
% 43.65/5.99  fof(f35,plain,(
% 43.65/5.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 43.65/5.99    inference(cnf_transformation,[],[f16])).
% 43.65/5.99  
% 43.65/5.99  fof(f6,axiom,(
% 43.65/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f37,plain,(
% 43.65/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.65/5.99    inference(cnf_transformation,[],[f6])).
% 43.65/5.99  
% 43.65/5.99  fof(f48,plain,(
% 43.65/5.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 43.65/5.99    inference(definition_unfolding,[],[f35,f37])).
% 43.65/5.99  
% 43.65/5.99  fof(f8,axiom,(
% 43.65/5.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f25,plain,(
% 43.65/5.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 43.65/5.99    inference(nnf_transformation,[],[f8])).
% 43.65/5.99  
% 43.65/5.99  fof(f39,plain,(
% 43.65/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 43.65/5.99    inference(cnf_transformation,[],[f25])).
% 43.65/5.99  
% 43.65/5.99  fof(f7,axiom,(
% 43.65/5.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f17,plain,(
% 43.65/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 43.65/5.99    inference(ennf_transformation,[],[f7])).
% 43.65/5.99  
% 43.65/5.99  fof(f18,plain,(
% 43.65/5.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.65/5.99    inference(flattening,[],[f17])).
% 43.65/5.99  
% 43.65/5.99  fof(f38,plain,(
% 43.65/5.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.65/5.99    inference(cnf_transformation,[],[f18])).
% 43.65/5.99  
% 43.65/5.99  fof(f49,plain,(
% 43.65/5.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.65/5.99    inference(definition_unfolding,[],[f38,f37])).
% 43.65/5.99  
% 43.65/5.99  fof(f40,plain,(
% 43.65/5.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 43.65/5.99    inference(cnf_transformation,[],[f25])).
% 43.65/5.99  
% 43.65/5.99  fof(f46,plain,(
% 43.65/5.99    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 43.65/5.99    inference(cnf_transformation,[],[f29])).
% 43.65/5.99  
% 43.65/5.99  fof(f3,axiom,(
% 43.65/5.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f34,plain,(
% 43.65/5.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 43.65/5.99    inference(cnf_transformation,[],[f3])).
% 43.65/5.99  
% 43.65/5.99  fof(f47,plain,(
% 43.65/5.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 43.65/5.99    inference(definition_unfolding,[],[f34,f37])).
% 43.65/5.99  
% 43.65/5.99  fof(f1,axiom,(
% 43.65/5.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f23,plain,(
% 43.65/5.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.65/5.99    inference(nnf_transformation,[],[f1])).
% 43.65/5.99  
% 43.65/5.99  fof(f24,plain,(
% 43.65/5.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.65/5.99    inference(flattening,[],[f23])).
% 43.65/5.99  
% 43.65/5.99  fof(f30,plain,(
% 43.65/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 43.65/5.99    inference(cnf_transformation,[],[f24])).
% 43.65/5.99  
% 43.65/5.99  fof(f51,plain,(
% 43.65/5.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.65/5.99    inference(equality_resolution,[],[f30])).
% 43.65/5.99  
% 43.65/5.99  fof(f5,axiom,(
% 43.65/5.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 43.65/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.65/5.99  
% 43.65/5.99  fof(f36,plain,(
% 43.65/5.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 43.65/5.99    inference(cnf_transformation,[],[f5])).
% 43.65/5.99  
% 43.65/5.99  cnf(c_11,plain,
% 43.65/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.65/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 43.65/5.99      | ~ r1_tarski(X0,X2)
% 43.65/5.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 43.65/5.99      | ~ l1_pre_topc(X1) ),
% 43.65/5.99      inference(cnf_transformation,[],[f42]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_616,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.65/5.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.65/5.99      | r1_tarski(X0,X2) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 43.65/5.99      | l1_pre_topc(X1) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_13,negated_conjecture,
% 43.65/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 43.65/5.99      inference(cnf_transformation,[],[f45]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_614,plain,
% 43.65/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_14,negated_conjecture,
% 43.65/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 43.65/5.99      inference(cnf_transformation,[],[f44]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_613,plain,
% 43.65/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_3,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 43.65/5.99      inference(cnf_transformation,[],[f33]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_622,plain,
% 43.65/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.65/5.99      | r1_tarski(X1,X2) != iProver_top
% 43.65/5.99      | r1_tarski(X0,X2) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2103,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.65/5.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.65/5.99      | r1_tarski(X0,X2) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(X1,X2),X3) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(X1,X0),X3) = iProver_top
% 43.65/5.99      | l1_pre_topc(X1) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_616,c_622]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_17530,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,X0) != iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_613,c_2103]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_15,negated_conjecture,
% 43.65/5.99      ( l1_pre_topc(sK0) ),
% 43.65/5.99      inference(cnf_transformation,[],[f43]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_16,plain,
% 43.65/5.99      ( l1_pre_topc(sK0) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_19055,plain,
% 43.65/5.99      ( r1_tarski(sK1,X0) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,[status(thm)],[c_17530,c_16]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_19056,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,X0) != iProver_top ),
% 43.65/5.99      inference(renaming,[status(thm)],[c_19055]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_19064,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_614,c_19056]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_19090,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,sK2) != iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_616,c_19064]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_18,plain,
% 43.65/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_50641,plain,
% 43.65/5.99      ( r1_tarski(sK1,sK2) != iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_19090,c_16,c_18]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_50642,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 43.65/5.99      inference(renaming,[status(thm)],[c_50641]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_17529,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_614,c_2103]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_18639,plain,
% 43.65/5.99      ( r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,[status(thm)],[c_17529,c_16]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_18640,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.65/5.99      inference(renaming,[status(thm)],[c_18639]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_18649,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 43.65/5.99      | r1_tarski(sK2,sK1) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_613,c_18640]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_50660,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | r1_tarski(sK2,sK1) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_50642,c_18649]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_32818,plain,
% 43.65/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.65/5.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 43.65/5.99      | ~ r1_tarski(sK2,X0)
% 43.65/5.99      | ~ l1_pre_topc(sK0) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_11]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_32823,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_32818]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_51585,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_50660,c_16,c_18,c_32823]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_10,plain,
% 43.65/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.65/5.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 43.65/5.99      | ~ l1_pre_topc(X1) ),
% 43.65/5.99      inference(cnf_transformation,[],[f41]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_617,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 43.65/5.99      | l1_pre_topc(X1) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2335,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_613,c_617]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_17,plain,
% 43.65/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_761,plain,
% 43.65/5.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 43.65/5.99      | ~ l1_pre_topc(sK0) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_10]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_762,plain,
% 43.65/5.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2781,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_2335,c_16,c_17,c_762]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2787,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_2781,c_622]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_5,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,X1)
% 43.65/5.99      | ~ r1_tarski(X2,X1)
% 43.65/5.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 43.65/5.99      inference(cnf_transformation,[],[f48]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_620,plain,
% 43.65/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.65/5.99      | r1_tarski(X2,X1) != iProver_top
% 43.65/5.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_9,plain,
% 43.65/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.65/5.99      inference(cnf_transformation,[],[f39]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_618,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.65/5.99      | r1_tarski(X0,X1) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1225,plain,
% 43.65/5.99      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_614,c_618]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2334,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_614,c_617]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_758,plain,
% 43.65/5.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 43.65/5.99      | ~ l1_pre_topc(sK0) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_10]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_759,plain,
% 43.65/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 43.65/5.99      | l1_pre_topc(sK0) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2753,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_2334,c_16,c_18,c_759]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2759,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_2753,c_622]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2914,plain,
% 43.65/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_2759,c_622]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_6921,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_1225,c_2914]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_808,plain,
% 43.65/5.99      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(resolution,[status(thm)],[c_9,c_13]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_809,plain,
% 43.65/5.99      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_827,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,X1)
% 43.65/5.99      | ~ r1_tarski(X1,u1_struct_0(X2))
% 43.65/5.99      | r1_tarski(X0,u1_struct_0(X2)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_3]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1344,plain,
% 43.65/5.99      ( r1_tarski(X0,u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(X0,sK2)
% 43.65/5.99      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_827]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2496,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 43.65/5.99      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_1344]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2497,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 43.65/5.99      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_2496]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_7208,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_6921,c_16,c_18,c_759,c_809,c_2497]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_3088,plain,
% 43.65/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_2787,c_622]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_9432,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_1225,c_3088]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_810,plain,
% 43.65/5.99      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(resolution,[status(thm)],[c_9,c_14]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_811,plain,
% 43.65/5.99      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1350,plain,
% 43.65/5.99      ( r1_tarski(X0,u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(X0,sK1)
% 43.65/5.99      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_827]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2524,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 43.65/5.99      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_1350]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2525,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_2524]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_9596,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_9432,c_16,c_17,c_762,c_811,c_2525]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_7,plain,
% 43.65/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.65/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.65/5.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 43.65/5.99      inference(cnf_transformation,[],[f49]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_8,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.65/5.99      inference(cnf_transformation,[],[f40]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_98,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.65/5.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_99,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.65/5.99      inference(renaming,[status(thm)],[c_98]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_125,plain,
% 43.65/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.65/5.99      | ~ r1_tarski(X2,X1)
% 43.65/5.99      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 43.65/5.99      inference(bin_hyper_res,[status(thm)],[c_7,c_99]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_199,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.65/5.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_200,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.65/5.99      inference(renaming,[status(thm)],[c_199]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_227,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,X1)
% 43.65/5.99      | ~ r1_tarski(X2,X1)
% 43.65/5.99      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 43.65/5.99      inference(bin_hyper_res,[status(thm)],[c_125,c_200]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_611,plain,
% 43.65/5.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 43.65/5.99      | r1_tarski(X1,X0) != iProver_top
% 43.65/5.99      | r1_tarski(X2,X0) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_9602,plain,
% 43.65/5.99      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),X0))
% 43.65/5.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_9596,c_611]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_81600,plain,
% 43.65/5.99      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_7208,c_9602]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1226,plain,
% 43.65/5.99      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_613,c_618]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1615,plain,
% 43.65/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 43.65/5.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_1226,c_611]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_3304,plain,
% 43.65/5.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_1225,c_1615]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_12,negated_conjecture,
% 43.65/5.99      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 43.65/5.99      inference(cnf_transformation,[],[f46]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_615,plain,
% 43.65/5.99      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_3992,plain,
% 43.65/5.99      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
% 43.65/5.99      inference(demodulation,[status(thm)],[c_3304,c_615]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_84843,plain,
% 43.65/5.99      ( r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
% 43.65/5.99      inference(demodulation,[status(thm)],[c_81600,c_3992]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_84847,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_620,c_84843]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177609,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_2787,c_84847]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_831,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 43.65/5.99      | ~ r1_tarski(X2,u1_struct_0(X1))
% 43.65/5.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),u1_struct_0(X1)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_5]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1674,plain,
% 43.65/5.99      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 43.65/5.99      | r1_tarski(k3_tarski(k2_tarski(X0,sK2)),u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_831]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2537,plain,
% 43.65/5.99      ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 43.65/5.99      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_1674]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2538,plain,
% 43.65/5.99      ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_2537]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_4,plain,
% 43.65/5.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 43.65/5.99      inference(cnf_transformation,[],[f47]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_1454,plain,
% 43.65/5.99      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,X0))) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_4]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_14027,plain,
% 43.65/5.99      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) ),
% 43.65/5.99      inference(instantiation,[status(thm)],[c_1454]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_14028,plain,
% 43.65/5.99      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_14027]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f51]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_623,plain,
% 43.65/5.99      ( r1_tarski(X0,X0) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_619,plain,
% 43.65/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 43.65/5.99      | r1_tarski(X0,X1) != iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_19063,plain,
% 43.65/5.99      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_619,c_19056]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_28531,plain,
% 43.65/5.99      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK1,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_623,c_19063]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177610,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top
% 43.65/5.99      | r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_28531,c_84847]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177652,plain,
% 43.65/5.99      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) != iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_177609,c_809,c_811,c_2538,c_14028,c_177610]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177662,plain,
% 43.65/5.99      ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.65/5.99      | r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_51585,c_177652]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_18647,plain,
% 43.65/5.99      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),X1) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_619,c_18640]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_27479,plain,
% 43.65/5.99      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) = iProver_top
% 43.65/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_623,c_18647]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177661,plain,
% 43.65/5.99      ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top
% 43.65/5.99      | r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_27479,c_177652]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177717,plain,
% 43.65/5.99      ( r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) != iProver_top ),
% 43.65/5.99      inference(global_propositional_subsumption,
% 43.65/5.99                [status(thm)],
% 43.65/5.99                [c_177662,c_809,c_811,c_2538,c_177661]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_6,plain,
% 43.65/5.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 43.65/5.99      inference(cnf_transformation,[],[f36]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_621,plain,
% 43.65/5.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 43.65/5.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_987,plain,
% 43.65/5.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 43.65/5.99      inference(superposition,[status(thm)],[c_6,c_621]) ).
% 43.65/5.99  
% 43.65/5.99  cnf(c_177722,plain,
% 43.65/5.99      ( $false ),
% 43.65/5.99      inference(forward_subsumption_resolution,[status(thm)],[c_177717,c_987]) ).
% 43.65/5.99  
% 43.65/5.99  
% 43.65/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.65/5.99  
% 43.65/5.99  ------                               Statistics
% 43.65/5.99  
% 43.65/5.99  ------ Selected
% 43.65/5.99  
% 43.65/5.99  total_time:                             5.48
% 43.65/5.99  
%------------------------------------------------------------------------------
