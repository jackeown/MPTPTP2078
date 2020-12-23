%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:49 EST 2020

% Result     : Theorem 31.66s
% Output     : CNFRefutation 31.66s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 919 expanded)
%              Number of clauses        :  132 ( 419 expanded)
%              Number of leaves         :   16 ( 222 expanded)
%              Depth                    :   25
%              Number of atoms          :  452 (2917 expanded)
%              Number of equality atoms :  156 ( 349 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f25,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).

fof(f38,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_314,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_92,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_93,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_92])).

cnf(c_116,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_93])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_116,c_242])).

cnf(c_309,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,X1_39)
    | k4_subset_1(X1_39,X0_39,X2_39) = k2_xboole_0(X0_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_264])).

cnf(c_325,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X3_39)
    | X2_39 != X0_39
    | X3_39 != X1_39 ),
    theory(equality)).

cnf(c_322,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_2472,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X1_39)
    | X2_39 != X0_39 ),
    inference(resolution,[status(thm)],[c_325,c_322])).

cnf(c_21905,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,X1_39)
    | r1_tarski(k4_subset_1(X1_39,X0_39,X2_39),X3_39)
    | ~ r1_tarski(k2_xboole_0(X0_39,X2_39),X3_39) ),
    inference(resolution,[status(thm)],[c_309,c_2472])).

cnf(c_121557,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_314,c_21905])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_742,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_743,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1186,plain,
    ( k1_tops_1(sK0,X0_39) = k1_tops_1(sK0,X0_39) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_18833,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1186])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_312,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_644,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) ),
    inference(subtyping,[status(esa)],[c_184])).

cnf(c_646,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_834,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_646])).

cnf(c_313,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_643,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_641,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
    | r1_tarski(X0_39,X1_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1731,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_641])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,X0_39)
    | r1_tarski(X2_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_637,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X2_39,X0_39) != iProver_top
    | r1_tarski(X2_39,X1_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_1742,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_637])).

cnf(c_1980,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X1_39,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_637])).

cnf(c_2755,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_1980])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_358,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_360,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_745,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_746,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_758,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),X0_39)
    | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1084,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1085,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_3057,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2755,c_14,c_360,c_746,c_1085])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_166,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39)
    | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_645,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | ~ r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_640,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) = iProver_top
    | r1_tarski(X0_39,X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1578,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_646])).

cnf(c_2263,plain,
    ( r1_tarski(X0_39,X1_39) = iProver_top
    | r1_tarski(X0_39,k1_tops_1(sK0,X1_39)) != iProver_top
    | r1_tarski(X1_39,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_637])).

cnf(c_8433,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_2263])).

cnf(c_1689,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_39,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1690,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1689])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39)
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),X2_39)
    | r1_tarski(k1_tops_1(sK0,X1_39),X2_39) ),
    inference(resolution,[status(thm)],[c_319,c_311])).

cnf(c_1005,plain,
    ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
    | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) ),
    inference(resolution,[status(thm)],[c_316,c_310])).

cnf(c_1772,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39)
    | ~ r1_tarski(X0_39,u1_struct_0(sK0))
    | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) ),
    inference(resolution,[status(thm)],[c_1137,c_1005])).

cnf(c_1773,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_9817,plain,
    ( m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8433,c_1690,c_1773])).

cnf(c_9818,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X1_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
    inference(renaming,[status(thm)],[c_9817])).

cnf(c_759,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_9821,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9818,c_358,c_759])).

cnf(c_9822,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
    inference(renaming,[status(thm)],[c_9821])).

cnf(c_9828,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0_39) = iProver_top
    | r1_tarski(sK2,X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_9822])).

cnf(c_647,plain,
    ( k4_subset_1(X0_39,X1_39,X2_39) = k2_xboole_0(X1_39,X2_39)
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(X2_39,X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_9854,plain,
    ( k4_subset_1(X0_39,X1_39,k1_tops_1(sK0,sK2)) = k2_xboole_0(X1_39,k1_tops_1(sK0,sK2))
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(sK2,X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_9828,c_647])).

cnf(c_24114,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_9854])).

cnf(c_15857,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_39 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_18832,plain,
    ( ~ r1_tarski(X0_39,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15857])).

cnf(c_45085,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_18832])).

cnf(c_122045,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_121557,c_15,c_9,c_743,c_18833,c_24114,c_45085])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_317,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,X1_39)
    | r1_tarski(k2_xboole_0(X0_39,X2_39),X1_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_122057,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_122045,c_317])).

cnf(c_336,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_872,plain,
    ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
    | r1_tarski(k2_xboole_0(X0_39,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_874,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_871,plain,
    ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) = k2_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_878,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_1070,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_803,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,k2_xboole_0(X2_39,X3_39))
    | X0_39 != X2_39
    | X1_39 != k2_xboole_0(X2_39,X3_39) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_1456,plain,
    ( r1_tarski(X0_39,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))
    | ~ r1_tarski(X1_39,k2_xboole_0(X1_39,sK2))
    | X0_39 != X1_39
    | k4_subset_1(u1_struct_0(sK0),X1_39,sK2) != k2_xboole_0(X1_39,sK2) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1458,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_2,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_318,plain,
    ( r1_tarski(X0_39,k2_xboole_0(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1809,plain,
    ( r1_tarski(X0_39,k2_xboole_0(X0_39,sK2)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1811,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_3311,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_39,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))
    | r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_3313,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3311])).

cnf(c_7490,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),X0_39,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_7492,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7490])).

cnf(c_954,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k2_xboole_0(X2_39,sK2),u1_struct_0(sK0))
    | X0_39 != k2_xboole_0(X2_39,sK2)
    | X1_39 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_2906,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(X1_39,sK2),u1_struct_0(sK0))
    | X0_39 != k2_xboole_0(X1_39,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_8402,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),X0_39,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(X0_39,sK2),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) != k2_xboole_0(X0_39,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2906])).

cnf(c_8404,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_8402])).

cnf(c_3181,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k1_tops_1(sK0,X2_39),X1_39)
    | r1_tarski(k2_xboole_0(X0_39,k1_tops_1(sK0,X2_39)),X1_39) ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_88894,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_39),X1_39)
    | ~ r1_tarski(k1_tops_1(sK0,X2_39),X1_39)
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),X1_39) ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_106376,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_88894])).

cnf(c_123881,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_122057,c_11,c_10,c_15,c_9,c_336,c_742,c_743,c_745,c_874,c_878,c_1070,c_1458,c_1811,c_3313,c_7492,c_8404,c_18833,c_24114,c_45085,c_106376])).

cnf(c_329,plain,
    ( X0_39 != X1_39
    | k1_tops_1(X0_41,X0_39) = k1_tops_1(X0_41,X1_39) ),
    theory(equality)).

cnf(c_4582,plain,
    ( ~ r1_tarski(k1_tops_1(X0_41,X0_39),X1_39)
    | r1_tarski(k1_tops_1(X0_41,X2_39),X1_39)
    | X2_39 != X0_39 ),
    inference(resolution,[status(thm)],[c_2472,c_329])).

cnf(c_10817,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39)
    | r1_tarski(k1_tops_1(sK0,X2_39),k1_tops_1(sK0,X0_39))
    | X2_39 != X1_39 ),
    inference(resolution,[status(thm)],[c_4582,c_311])).

cnf(c_12971,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39))
    | ~ r1_tarski(sK2,X0_39)
    | X1_39 != sK2 ),
    inference(resolution,[status(thm)],[c_10817,c_313])).

cnf(c_123896,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | sK2 != sK2 ),
    inference(resolution,[status(thm)],[c_123881,c_12971])).

cnf(c_123903,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_123896])).

cnf(c_20915,plain,
    ( r1_tarski(X0_39,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,X1_39))
    | X0_39 != sK2
    | k4_subset_1(u1_struct_0(sK0),X1_39,sK2) != k2_xboole_0(sK2,X1_39) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_80929,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),X0_39,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0_39))
    | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) != k2_xboole_0(sK2,X0_39)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_20915])).

cnf(c_80931,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_80929])).

cnf(c_31410,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,X0_39)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_31412,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_31410])).

cnf(c_324,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_1454,plain,
    ( X0_39 != X1_39
    | X0_39 = k2_xboole_0(X2_39,X3_39)
    | k2_xboole_0(X2_39,X3_39) != X1_39 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_2364,plain,
    ( X0_39 != k2_xboole_0(X1_39,X2_39)
    | X0_39 = k2_xboole_0(X2_39,X1_39)
    | k2_xboole_0(X2_39,X1_39) != k2_xboole_0(X1_39,X2_39) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_10371,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_39,sK2) != k2_xboole_0(X0_39,sK2)
    | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) = k2_xboole_0(sK2,X0_39)
    | k2_xboole_0(sK2,X0_39) != k2_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_10372,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_10371])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_320,plain,
    ( k2_xboole_0(X0_39,X1_39) = k2_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_8394,plain,
    ( k2_xboole_0(sK2,X0_39) = k2_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_8399,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_8394])).

cnf(c_1062,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_123903,c_80931,c_31412,c_10372,c_8404,c_8399,c_7492,c_1070,c_1062,c_878,c_874,c_745,c_742,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.66/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.66/4.49  
% 31.66/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.66/4.49  
% 31.66/4.49  ------  iProver source info
% 31.66/4.49  
% 31.66/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.66/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.66/4.49  git: non_committed_changes: false
% 31.66/4.49  git: last_make_outside_of_git: false
% 31.66/4.49  
% 31.66/4.49  ------ 
% 31.66/4.49  ------ Parsing...
% 31.66/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.66/4.49  
% 31.66/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.66/4.49  
% 31.66/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.66/4.49  
% 31.66/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.66/4.49  ------ Proving...
% 31.66/4.49  ------ Problem Properties 
% 31.66/4.49  
% 31.66/4.49  
% 31.66/4.49  clauses                                 12
% 31.66/4.49  conjectures                             3
% 31.66/4.49  EPR                                     1
% 31.66/4.49  Horn                                    12
% 31.66/4.49  unary                                   5
% 31.66/4.49  binary                                  3
% 31.66/4.49  lits                                    24
% 31.66/4.49  lits eq                                 2
% 31.66/4.50  fd_pure                                 0
% 31.66/4.50  fd_pseudo                               0
% 31.66/4.50  fd_cond                                 0
% 31.66/4.50  fd_pseudo_cond                          0
% 31.66/4.50  AC symbols                              0
% 31.66/4.50  
% 31.66/4.50  ------ Input Options Time Limit: Unbounded
% 31.66/4.50  
% 31.66/4.50  
% 31.66/4.50  ------ 
% 31.66/4.50  Current options:
% 31.66/4.50  ------ 
% 31.66/4.50  
% 31.66/4.50  
% 31.66/4.50  
% 31.66/4.50  
% 31.66/4.50  ------ Proving...
% 31.66/4.50  
% 31.66/4.50  
% 31.66/4.50  % SZS status Theorem for theBenchmark.p
% 31.66/4.50  
% 31.66/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.66/4.50  
% 31.66/4.50  fof(f9,conjecture,(
% 31.66/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f10,negated_conjecture,(
% 31.66/4.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.66/4.50    inference(negated_conjecture,[],[f9])).
% 31.66/4.50  
% 31.66/4.50  fof(f20,plain,(
% 31.66/4.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.66/4.50    inference(ennf_transformation,[],[f10])).
% 31.66/4.50  
% 31.66/4.50  fof(f24,plain,(
% 31.66/4.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.66/4.50    introduced(choice_axiom,[])).
% 31.66/4.50  
% 31.66/4.50  fof(f23,plain,(
% 31.66/4.50    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.66/4.50    introduced(choice_axiom,[])).
% 31.66/4.50  
% 31.66/4.50  fof(f22,plain,(
% 31.66/4.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.66/4.50    introduced(choice_axiom,[])).
% 31.66/4.50  
% 31.66/4.50  fof(f25,plain,(
% 31.66/4.50    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.66/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).
% 31.66/4.50  
% 31.66/4.50  fof(f38,plain,(
% 31.66/4.50    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 31.66/4.50    inference(cnf_transformation,[],[f25])).
% 31.66/4.50  
% 31.66/4.50  fof(f5,axiom,(
% 31.66/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f15,plain,(
% 31.66/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.66/4.50    inference(ennf_transformation,[],[f5])).
% 31.66/4.50  
% 31.66/4.50  fof(f16,plain,(
% 31.66/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.66/4.50    inference(flattening,[],[f15])).
% 31.66/4.50  
% 31.66/4.50  fof(f30,plain,(
% 31.66/4.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.66/4.50    inference(cnf_transformation,[],[f16])).
% 31.66/4.50  
% 31.66/4.50  fof(f6,axiom,(
% 31.66/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f21,plain,(
% 31.66/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.66/4.50    inference(nnf_transformation,[],[f6])).
% 31.66/4.50  
% 31.66/4.50  fof(f32,plain,(
% 31.66/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.66/4.50    inference(cnf_transformation,[],[f21])).
% 31.66/4.50  
% 31.66/4.50  fof(f37,plain,(
% 31.66/4.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.66/4.50    inference(cnf_transformation,[],[f25])).
% 31.66/4.50  
% 31.66/4.50  fof(f31,plain,(
% 31.66/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.66/4.50    inference(cnf_transformation,[],[f21])).
% 31.66/4.50  
% 31.66/4.50  fof(f36,plain,(
% 31.66/4.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.66/4.50    inference(cnf_transformation,[],[f25])).
% 31.66/4.50  
% 31.66/4.50  fof(f7,axiom,(
% 31.66/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f17,plain,(
% 31.66/4.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.50    inference(ennf_transformation,[],[f7])).
% 31.66/4.50  
% 31.66/4.50  fof(f33,plain,(
% 31.66/4.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.66/4.50    inference(cnf_transformation,[],[f17])).
% 31.66/4.50  
% 31.66/4.50  fof(f35,plain,(
% 31.66/4.50    l1_pre_topc(sK0)),
% 31.66/4.50    inference(cnf_transformation,[],[f25])).
% 31.66/4.50  
% 31.66/4.50  fof(f2,axiom,(
% 31.66/4.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f11,plain,(
% 31.66/4.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 31.66/4.50    inference(ennf_transformation,[],[f2])).
% 31.66/4.50  
% 31.66/4.50  fof(f12,plain,(
% 31.66/4.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 31.66/4.50    inference(flattening,[],[f11])).
% 31.66/4.50  
% 31.66/4.50  fof(f27,plain,(
% 31.66/4.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 31.66/4.50    inference(cnf_transformation,[],[f12])).
% 31.66/4.50  
% 31.66/4.50  fof(f8,axiom,(
% 31.66/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f18,plain,(
% 31.66/4.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.50    inference(ennf_transformation,[],[f8])).
% 31.66/4.50  
% 31.66/4.50  fof(f19,plain,(
% 31.66/4.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.66/4.50    inference(flattening,[],[f18])).
% 31.66/4.50  
% 31.66/4.50  fof(f34,plain,(
% 31.66/4.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.66/4.50    inference(cnf_transformation,[],[f19])).
% 31.66/4.50  
% 31.66/4.50  fof(f4,axiom,(
% 31.66/4.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f13,plain,(
% 31.66/4.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 31.66/4.50    inference(ennf_transformation,[],[f4])).
% 31.66/4.50  
% 31.66/4.50  fof(f14,plain,(
% 31.66/4.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 31.66/4.50    inference(flattening,[],[f13])).
% 31.66/4.50  
% 31.66/4.50  fof(f29,plain,(
% 31.66/4.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 31.66/4.50    inference(cnf_transformation,[],[f14])).
% 31.66/4.50  
% 31.66/4.50  fof(f3,axiom,(
% 31.66/4.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f28,plain,(
% 31.66/4.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.66/4.50    inference(cnf_transformation,[],[f3])).
% 31.66/4.50  
% 31.66/4.50  fof(f1,axiom,(
% 31.66/4.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 31.66/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.66/4.50  
% 31.66/4.50  fof(f26,plain,(
% 31.66/4.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 31.66/4.50    inference(cnf_transformation,[],[f1])).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9,negated_conjecture,
% 31.66/4.50      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(cnf_transformation,[],[f38]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_314,negated_conjecture,
% 31.66/4.50      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_9]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_4,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.66/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.66/4.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.66/4.50      inference(cnf_transformation,[],[f30]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_5,plain,
% 31.66/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.66/4.50      inference(cnf_transformation,[],[f32]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_92,plain,
% 31.66/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.66/4.50      inference(prop_impl,[status(thm)],[c_5]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_93,plain,
% 31.66/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.66/4.50      inference(renaming,[status(thm)],[c_92]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_116,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.66/4.50      | ~ r1_tarski(X2,X1)
% 31.66/4.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.66/4.50      inference(bin_hyper_res,[status(thm)],[c_4,c_93]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_241,plain,
% 31.66/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.66/4.50      inference(prop_impl,[status(thm)],[c_5]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_242,plain,
% 31.66/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.66/4.50      inference(renaming,[status(thm)],[c_241]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_264,plain,
% 31.66/4.50      ( ~ r1_tarski(X0,X1)
% 31.66/4.50      | ~ r1_tarski(X2,X1)
% 31.66/4.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.66/4.50      inference(bin_hyper_res,[status(thm)],[c_116,c_242]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_309,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(X2_39,X1_39)
% 31.66/4.50      | k4_subset_1(X1_39,X0_39,X2_39) = k2_xboole_0(X0_39,X2_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_264]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_325,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | r1_tarski(X2_39,X3_39)
% 31.66/4.50      | X2_39 != X0_39
% 31.66/4.50      | X3_39 != X1_39 ),
% 31.66/4.50      theory(equality) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_322,plain,( X0_39 = X0_39 ),theory(equality) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_2472,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | r1_tarski(X2_39,X1_39)
% 31.66/4.50      | X2_39 != X0_39 ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_325,c_322]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_21905,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(X2_39,X1_39)
% 31.66/4.50      | r1_tarski(k4_subset_1(X1_39,X0_39,X2_39),X3_39)
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(X0_39,X2_39),X3_39) ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_309,c_2472]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_121557,plain,
% 31.66/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_314,c_21905]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_10,negated_conjecture,
% 31.66/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.66/4.50      inference(cnf_transformation,[],[f37]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_15,plain,
% 31.66/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_6,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.66/4.50      inference(cnf_transformation,[],[f31]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_315,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
% 31.66/4.50      | r1_tarski(X0_39,X1_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_6]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_742,plain,
% 31.66/4.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_315]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_743,plain,
% 31.66/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1186,plain,
% 31.66/4.50      ( k1_tops_1(sK0,X0_39) = k1_tops_1(sK0,X0_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_322]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_18833,plain,
% 31.66/4.50      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_1186]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_11,negated_conjecture,
% 31.66/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.66/4.50      inference(cnf_transformation,[],[f36]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_312,negated_conjecture,
% 31.66/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_11]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_644,plain,
% 31.66/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_7,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 31.66/4.50      | ~ l1_pre_topc(X1) ),
% 31.66/4.50      inference(cnf_transformation,[],[f33]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_12,negated_conjecture,
% 31.66/4.50      ( l1_pre_topc(sK0) ),
% 31.66/4.50      inference(cnf_transformation,[],[f35]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_183,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 31.66/4.50      | sK0 != X1 ),
% 31.66/4.50      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_184,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 31.66/4.50      inference(unflattening,[status(thm)],[c_183]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_310,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_184]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_646,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_834,plain,
% 31.66/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_644,c_646]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_313,negated_conjecture,
% 31.66/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_10]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_643,plain,
% 31.66/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_641,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,X1_39) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1731,plain,
% 31.66/4.50      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_643,c_641]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1,plain,
% 31.66/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 31.66/4.50      inference(cnf_transformation,[],[f27]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_319,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(X2_39,X0_39)
% 31.66/4.50      | r1_tarski(X2_39,X1_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_1]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_637,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39) != iProver_top
% 31.66/4.50      | r1_tarski(X2_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(X2_39,X1_39) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1742,plain,
% 31.66/4.50      ( r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
% 31.66/4.50      | r1_tarski(X0_39,sK2) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_1731,c_637]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1980,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
% 31.66/4.50      | r1_tarski(X1_39,sK2) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_1742,c_637]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_2755,plain,
% 31.66/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 31.66/4.50      | r1_tarski(sK1,sK2) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_834,c_1980]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_14,plain,
% 31.66/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_358,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_360,plain,
% 31.66/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_358]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_745,plain,
% 31.66/4.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_315]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_746,plain,
% 31.66/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_758,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,X0_39),X0_39)
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_319]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1084,plain,
% 31.66/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 31.66/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_758]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1085,plain,
% 31.66/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 31.66/4.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_3057,plain,
% 31.66/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 31.66/4.50      inference(global_propositional_subsumption,
% 31.66/4.50                [status(thm)],
% 31.66/4.50                [c_2755,c_14,c_360,c_746,c_1085]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_8,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.50      | ~ r1_tarski(X0,X2)
% 31.66/4.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.66/4.50      | ~ l1_pre_topc(X1) ),
% 31.66/4.50      inference(cnf_transformation,[],[f34]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_165,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.66/4.50      | ~ r1_tarski(X0,X2)
% 31.66/4.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.66/4.50      | sK0 != X1 ),
% 31.66/4.50      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_166,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X1,X0)
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 31.66/4.50      inference(unflattening,[status(thm)],[c_165]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_311,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X1_39,X0_39)
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_166]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_645,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_316,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
% 31.66/4.50      | ~ r1_tarski(X0_39,X1_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_5]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_640,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) = iProver_top
% 31.66/4.50      | r1_tarski(X0_39,X1_39) != iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1578,plain,
% 31.66/4.50      ( r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) = iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_640,c_646]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_2263,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39) = iProver_top
% 31.66/4.50      | r1_tarski(X0_39,k1_tops_1(sK0,X1_39)) != iProver_top
% 31.66/4.50      | r1_tarski(X1_39,u1_struct_0(sK0)) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_1578,c_637]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_8433,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) = iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_645,c_2263]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1689,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X0_39,u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_316]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1690,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.66/4.50      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_1689]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1137,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X1_39,X0_39)
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,X0_39),X2_39)
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),X2_39) ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_319,c_311]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1005,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_316,c_310]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1772,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X1_39,X0_39)
% 31.66/4.50      | ~ r1_tarski(X0_39,u1_struct_0(sK0))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_1137,c_1005]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1773,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_1772]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9817,plain,
% 31.66/4.50      ( m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),X0_39) = iProver_top ),
% 31.66/4.50      inference(global_propositional_subsumption,
% 31.66/4.50                [status(thm)],
% 31.66/4.50                [c_8433,c_1690,c_1773]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9818,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,X1_39) != iProver_top
% 31.66/4.50      | r1_tarski(X1_39,u1_struct_0(sK0)) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
% 31.66/4.50      inference(renaming,[status(thm)],[c_9817]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_759,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9821,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39) != iProver_top
% 31.66/4.50      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
% 31.66/4.50      inference(global_propositional_subsumption,
% 31.66/4.50                [status(thm)],
% 31.66/4.50                [c_9818,c_358,c_759]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9822,plain,
% 31.66/4.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.66/4.50      | r1_tarski(X0_39,X1_39) != iProver_top
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),X1_39) = iProver_top ),
% 31.66/4.50      inference(renaming,[status(thm)],[c_9821]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9828,plain,
% 31.66/4.50      ( r1_tarski(k1_tops_1(sK0,sK2),X0_39) = iProver_top
% 31.66/4.50      | r1_tarski(sK2,X0_39) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_643,c_9822]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_647,plain,
% 31.66/4.50      ( k4_subset_1(X0_39,X1_39,X2_39) = k2_xboole_0(X1_39,X2_39)
% 31.66/4.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(X2_39,X0_39) != iProver_top ),
% 31.66/4.50      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_9854,plain,
% 31.66/4.50      ( k4_subset_1(X0_39,X1_39,k1_tops_1(sK0,sK2)) = k2_xboole_0(X1_39,k1_tops_1(sK0,sK2))
% 31.66/4.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 31.66/4.50      | r1_tarski(sK2,X0_39) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_9828,c_647]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_24114,plain,
% 31.66/4.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.66/4.50      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 31.66/4.50      inference(superposition,[status(thm)],[c_3057,c_9854]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_15857,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
% 31.66/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_39 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_325]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_18832,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
% 31.66/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_15857]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_45085,plain,
% 31.66/4.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.66/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_18832]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_122045,plain,
% 31.66/4.50      ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(global_propositional_subsumption,
% 31.66/4.50                [status(thm)],
% 31.66/4.50                [c_121557,c_15,c_9,c_743,c_18833,c_24114,c_45085]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_3,plain,
% 31.66/4.50      ( ~ r1_tarski(X0,X1)
% 31.66/4.50      | ~ r1_tarski(X2,X1)
% 31.66/4.50      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 31.66/4.50      inference(cnf_transformation,[],[f29]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_317,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(X2_39,X1_39)
% 31.66/4.50      | r1_tarski(k2_xboole_0(X0_39,X2_39),X1_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_3]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_122057,plain,
% 31.66/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_122045,c_317]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_336,plain,
% 31.66/4.50      ( sK1 = sK1 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_322]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_872,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
% 31.66/4.50      | r1_tarski(k2_xboole_0(X0_39,sK2),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_317]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_874,plain,
% 31.66/4.50      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_872]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_871,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) = k2_xboole_0(X0_39,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_309]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_878,plain,
% 31.66/4.50      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_871]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1070,plain,
% 31.66/4.50      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_322]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_803,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(X2_39,k2_xboole_0(X2_39,X3_39))
% 31.66/4.50      | X0_39 != X2_39
% 31.66/4.50      | X1_39 != k2_xboole_0(X2_39,X3_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_325]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1456,plain,
% 31.66/4.50      ( r1_tarski(X0_39,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))
% 31.66/4.50      | ~ r1_tarski(X1_39,k2_xboole_0(X1_39,sK2))
% 31.66/4.50      | X0_39 != X1_39
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),X1_39,sK2) != k2_xboole_0(X1_39,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_803]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1458,plain,
% 31.66/4.50      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 31.66/4.50      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.66/4.50      | sK1 != sK1 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_1456]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_2,plain,
% 31.66/4.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 31.66/4.50      inference(cnf_transformation,[],[f28]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_318,plain,
% 31.66/4.50      ( r1_tarski(X0_39,k2_xboole_0(X0_39,X1_39)) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_2]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1809,plain,
% 31.66/4.50      ( r1_tarski(X0_39,k2_xboole_0(X0_39,sK2)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_318]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1811,plain,
% 31.66/4.50      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_1809]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_3311,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X0_39,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_311]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_3313,plain,
% 31.66/4.50      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_3311]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_7490,plain,
% 31.66/4.50      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),X0_39,sK2),u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_1689]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_7492,plain,
% 31.66/4.50      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_7490]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_954,plain,
% 31.66/4.50      ( r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(X2_39,sK2),u1_struct_0(sK0))
% 31.66/4.50      | X0_39 != k2_xboole_0(X2_39,sK2)
% 31.66/4.50      | X1_39 != u1_struct_0(sK0) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_325]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_2906,plain,
% 31.66/4.50      ( r1_tarski(X0_39,u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(X1_39,sK2),u1_struct_0(sK0))
% 31.66/4.50      | X0_39 != k2_xboole_0(X1_39,sK2)
% 31.66/4.50      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_954]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_8402,plain,
% 31.66/4.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),X0_39,sK2),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(X0_39,sK2),u1_struct_0(sK0))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) != k2_xboole_0(X0_39,sK2)
% 31.66/4.50      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_2906]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_8404,plain,
% 31.66/4.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 31.66/4.50      | ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.66/4.50      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_8402]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_3181,plain,
% 31.66/4.50      ( ~ r1_tarski(X0_39,X1_39)
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,X2_39),X1_39)
% 31.66/4.50      | r1_tarski(k2_xboole_0(X0_39,k1_tops_1(sK0,X2_39)),X1_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_317]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_88894,plain,
% 31.66/4.50      ( ~ r1_tarski(k1_tops_1(sK0,X0_39),X1_39)
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,X2_39),X1_39)
% 31.66/4.50      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),X1_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_3181]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_106376,plain,
% 31.66/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.66/4.50      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_88894]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_123881,plain,
% 31.66/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.66/4.50      inference(global_propositional_subsumption,
% 31.66/4.50                [status(thm)],
% 31.66/4.50                [c_122057,c_11,c_10,c_15,c_9,c_336,c_742,c_743,c_745,
% 31.66/4.50                 c_874,c_878,c_1070,c_1458,c_1811,c_3313,c_7492,c_8404,
% 31.66/4.50                 c_18833,c_24114,c_45085,c_106376]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_329,plain,
% 31.66/4.50      ( X0_39 != X1_39
% 31.66/4.50      | k1_tops_1(X0_41,X0_39) = k1_tops_1(X0_41,X1_39) ),
% 31.66/4.50      theory(equality) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_4582,plain,
% 31.66/4.50      ( ~ r1_tarski(k1_tops_1(X0_41,X0_39),X1_39)
% 31.66/4.50      | r1_tarski(k1_tops_1(X0_41,X2_39),X1_39)
% 31.66/4.50      | X2_39 != X0_39 ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_2472,c_329]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_10817,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(X1_39,X0_39)
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X2_39),k1_tops_1(sK0,X0_39))
% 31.66/4.50      | X2_39 != X1_39 ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_4582,c_311]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_12971,plain,
% 31.66/4.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39))
% 31.66/4.50      | ~ r1_tarski(sK2,X0_39)
% 31.66/4.50      | X1_39 != sK2 ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_10817,c_313]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_123896,plain,
% 31.66/4.50      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 31.66/4.50      | sK2 != sK2 ),
% 31.66/4.50      inference(resolution,[status(thm)],[c_123881,c_12971]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_123903,plain,
% 31.66/4.50      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.66/4.50      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.66/4.50      inference(equality_resolution_simp,[status(thm)],[c_123896]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_20915,plain,
% 31.66/4.50      ( r1_tarski(X0_39,k4_subset_1(u1_struct_0(sK0),X1_39,sK2))
% 31.66/4.50      | ~ r1_tarski(sK2,k2_xboole_0(sK2,X1_39))
% 31.66/4.50      | X0_39 != sK2
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),X1_39,sK2) != k2_xboole_0(sK2,X1_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_803]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_80929,plain,
% 31.66/4.50      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),X0_39,sK2))
% 31.66/4.50      | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0_39))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) != k2_xboole_0(sK2,X0_39)
% 31.66/4.50      | sK2 != sK2 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_20915]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_80931,plain,
% 31.66/4.50      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 31.66/4.50      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,sK1)
% 31.66/4.50      | sK2 != sK2 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_80929]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_31410,plain,
% 31.66/4.50      ( r1_tarski(sK2,k2_xboole_0(sK2,X0_39)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_318]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_31412,plain,
% 31.66/4.50      ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_31410]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_324,plain,
% 31.66/4.50      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 31.66/4.50      theory(equality) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1454,plain,
% 31.66/4.50      ( X0_39 != X1_39
% 31.66/4.50      | X0_39 = k2_xboole_0(X2_39,X3_39)
% 31.66/4.50      | k2_xboole_0(X2_39,X3_39) != X1_39 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_324]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_2364,plain,
% 31.66/4.50      ( X0_39 != k2_xboole_0(X1_39,X2_39)
% 31.66/4.50      | X0_39 = k2_xboole_0(X2_39,X1_39)
% 31.66/4.50      | k2_xboole_0(X2_39,X1_39) != k2_xboole_0(X1_39,X2_39) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_1454]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_10371,plain,
% 31.66/4.50      ( k4_subset_1(u1_struct_0(sK0),X0_39,sK2) != k2_xboole_0(X0_39,sK2)
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),X0_39,sK2) = k2_xboole_0(sK2,X0_39)
% 31.66/4.50      | k2_xboole_0(sK2,X0_39) != k2_xboole_0(X0_39,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_2364]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_10372,plain,
% 31.66/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
% 31.66/4.50      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.66/4.50      | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_10371]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_0,plain,
% 31.66/4.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 31.66/4.50      inference(cnf_transformation,[],[f26]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_320,plain,
% 31.66/4.50      ( k2_xboole_0(X0_39,X1_39) = k2_xboole_0(X1_39,X0_39) ),
% 31.66/4.50      inference(subtyping,[status(esa)],[c_0]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_8394,plain,
% 31.66/4.50      ( k2_xboole_0(sK2,X0_39) = k2_xboole_0(X0_39,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_320]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_8399,plain,
% 31.66/4.50      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_8394]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(c_1062,plain,
% 31.66/4.50      ( sK2 = sK2 ),
% 31.66/4.50      inference(instantiation,[status(thm)],[c_322]) ).
% 31.66/4.50  
% 31.66/4.50  cnf(contradiction,plain,
% 31.66/4.50      ( $false ),
% 31.66/4.50      inference(minisat,
% 31.66/4.50                [status(thm)],
% 31.66/4.50                [c_123903,c_80931,c_31412,c_10372,c_8404,c_8399,c_7492,
% 31.66/4.50                 c_1070,c_1062,c_878,c_874,c_745,c_742,c_10,c_11]) ).
% 31.66/4.50  
% 31.66/4.50  
% 31.66/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.66/4.50  
% 31.66/4.50  ------                               Statistics
% 31.66/4.50  
% 31.66/4.50  ------ Selected
% 31.66/4.50  
% 31.66/4.50  total_time:                             3.572
% 31.66/4.50  
%------------------------------------------------------------------------------
