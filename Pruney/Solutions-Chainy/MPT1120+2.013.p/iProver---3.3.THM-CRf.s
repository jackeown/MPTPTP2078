%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:36 EST 2020

% Result     : Theorem 31.36s
% Output     : CNFRefutation 31.36s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 442 expanded)
%              Number of clauses        :   65 ( 173 expanded)
%              Number of leaves         :   13 ( 101 expanded)
%              Depth                    :   17
%              Number of atoms          :  263 (1192 expanded)
%              Number of equality atoms :   95 ( 235 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26,f25,f24])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_687,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_683,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_685])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_139,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_116])).

cnf(c_680,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_2015,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_680])).

cnf(c_9880,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_683,c_2015])).

cnf(c_1103,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_685])).

cnf(c_1554,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1103,c_680])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_684,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1646,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1554,c_684])).

cnf(c_10180,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9880,c_1646])).

cnf(c_10420,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_10180])).

cnf(c_21603,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_10420])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_688,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_138,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_116])).

cnf(c_681,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_2220,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_681])).

cnf(c_12794,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2220,c_1103])).

cnf(c_12803,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12794,c_685])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_682,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_686,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_690,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1327,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_688,c_690])).

cnf(c_3504,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_1327])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_43,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3687,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3504,c_43])).

cnf(c_3688,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3687])).

cnf(c_3699,plain,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_3688])).

cnf(c_4827,plain,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_3699])).

cnf(c_51070,plain,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_4827])).

cnf(c_51718,plain,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0,sK2))),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0,sK2)))
    | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12803,c_51070])).

cnf(c_52539,plain,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_688,c_51718])).

cnf(c_689,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1227,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_689,c_680])).

cnf(c_2451,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_681])).

cnf(c_17621,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2451,c_689])).

cnf(c_17637,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_17621,c_685])).

cnf(c_53648,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_52539,c_17637])).

cnf(c_128366,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21603,c_17,c_53648])).

cnf(c_128372,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_128366,c_17637,c_12794])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:46:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.36/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.36/4.49  
% 31.36/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.36/4.49  
% 31.36/4.49  ------  iProver source info
% 31.36/4.49  
% 31.36/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.36/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.36/4.49  git: non_committed_changes: false
% 31.36/4.49  git: last_make_outside_of_git: false
% 31.36/4.49  
% 31.36/4.49  ------ 
% 31.36/4.49  
% 31.36/4.49  ------ Input Options
% 31.36/4.49  
% 31.36/4.49  --out_options                           all
% 31.36/4.49  --tptp_safe_out                         true
% 31.36/4.49  --problem_path                          ""
% 31.36/4.49  --include_path                          ""
% 31.36/4.49  --clausifier                            res/vclausify_rel
% 31.36/4.49  --clausifier_options                    --mode clausify
% 31.36/4.49  --stdin                                 false
% 31.36/4.49  --stats_out                             all
% 31.36/4.49  
% 31.36/4.49  ------ General Options
% 31.36/4.49  
% 31.36/4.49  --fof                                   false
% 31.36/4.49  --time_out_real                         305.
% 31.36/4.49  --time_out_virtual                      -1.
% 31.36/4.49  --symbol_type_check                     false
% 31.36/4.49  --clausify_out                          false
% 31.36/4.49  --sig_cnt_out                           false
% 31.36/4.49  --trig_cnt_out                          false
% 31.36/4.49  --trig_cnt_out_tolerance                1.
% 31.36/4.49  --trig_cnt_out_sk_spl                   false
% 31.36/4.49  --abstr_cl_out                          false
% 31.36/4.49  
% 31.36/4.49  ------ Global Options
% 31.36/4.49  
% 31.36/4.49  --schedule                              default
% 31.36/4.49  --add_important_lit                     false
% 31.36/4.49  --prop_solver_per_cl                    1000
% 31.36/4.49  --min_unsat_core                        false
% 31.36/4.49  --soft_assumptions                      false
% 31.36/4.49  --soft_lemma_size                       3
% 31.36/4.49  --prop_impl_unit_size                   0
% 31.36/4.49  --prop_impl_unit                        []
% 31.36/4.49  --share_sel_clauses                     true
% 31.36/4.49  --reset_solvers                         false
% 31.36/4.49  --bc_imp_inh                            [conj_cone]
% 31.36/4.49  --conj_cone_tolerance                   3.
% 31.36/4.49  --extra_neg_conj                        none
% 31.36/4.49  --large_theory_mode                     true
% 31.36/4.49  --prolific_symb_bound                   200
% 31.36/4.49  --lt_threshold                          2000
% 31.36/4.49  --clause_weak_htbl                      true
% 31.36/4.49  --gc_record_bc_elim                     false
% 31.36/4.49  
% 31.36/4.49  ------ Preprocessing Options
% 31.36/4.49  
% 31.36/4.49  --preprocessing_flag                    true
% 31.36/4.49  --time_out_prep_mult                    0.1
% 31.36/4.49  --splitting_mode                        input
% 31.36/4.49  --splitting_grd                         true
% 31.36/4.49  --splitting_cvd                         false
% 31.36/4.49  --splitting_cvd_svl                     false
% 31.36/4.49  --splitting_nvd                         32
% 31.36/4.49  --sub_typing                            true
% 31.36/4.49  --prep_gs_sim                           true
% 31.36/4.49  --prep_unflatten                        true
% 31.36/4.49  --prep_res_sim                          true
% 31.36/4.49  --prep_upred                            true
% 31.36/4.49  --prep_sem_filter                       exhaustive
% 31.36/4.49  --prep_sem_filter_out                   false
% 31.36/4.49  --pred_elim                             true
% 31.36/4.49  --res_sim_input                         true
% 31.36/4.49  --eq_ax_congr_red                       true
% 31.36/4.49  --pure_diseq_elim                       true
% 31.36/4.49  --brand_transform                       false
% 31.36/4.49  --non_eq_to_eq                          false
% 31.36/4.49  --prep_def_merge                        true
% 31.36/4.49  --prep_def_merge_prop_impl              false
% 31.36/4.49  --prep_def_merge_mbd                    true
% 31.36/4.49  --prep_def_merge_tr_red                 false
% 31.36/4.49  --prep_def_merge_tr_cl                  false
% 31.36/4.49  --smt_preprocessing                     true
% 31.36/4.49  --smt_ac_axioms                         fast
% 31.36/4.49  --preprocessed_out                      false
% 31.36/4.49  --preprocessed_stats                    false
% 31.36/4.49  
% 31.36/4.49  ------ Abstraction refinement Options
% 31.36/4.49  
% 31.36/4.49  --abstr_ref                             []
% 31.36/4.49  --abstr_ref_prep                        false
% 31.36/4.49  --abstr_ref_until_sat                   false
% 31.36/4.49  --abstr_ref_sig_restrict                funpre
% 31.36/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.36/4.49  --abstr_ref_under                       []
% 31.36/4.49  
% 31.36/4.49  ------ SAT Options
% 31.36/4.49  
% 31.36/4.49  --sat_mode                              false
% 31.36/4.49  --sat_fm_restart_options                ""
% 31.36/4.49  --sat_gr_def                            false
% 31.36/4.49  --sat_epr_types                         true
% 31.36/4.49  --sat_non_cyclic_types                  false
% 31.36/4.49  --sat_finite_models                     false
% 31.36/4.49  --sat_fm_lemmas                         false
% 31.36/4.49  --sat_fm_prep                           false
% 31.36/4.49  --sat_fm_uc_incr                        true
% 31.36/4.49  --sat_out_model                         small
% 31.36/4.49  --sat_out_clauses                       false
% 31.36/4.49  
% 31.36/4.49  ------ QBF Options
% 31.36/4.49  
% 31.36/4.49  --qbf_mode                              false
% 31.36/4.49  --qbf_elim_univ                         false
% 31.36/4.49  --qbf_dom_inst                          none
% 31.36/4.49  --qbf_dom_pre_inst                      false
% 31.36/4.49  --qbf_sk_in                             false
% 31.36/4.49  --qbf_pred_elim                         true
% 31.36/4.49  --qbf_split                             512
% 31.36/4.49  
% 31.36/4.49  ------ BMC1 Options
% 31.36/4.49  
% 31.36/4.49  --bmc1_incremental                      false
% 31.36/4.49  --bmc1_axioms                           reachable_all
% 31.36/4.49  --bmc1_min_bound                        0
% 31.36/4.49  --bmc1_max_bound                        -1
% 31.36/4.49  --bmc1_max_bound_default                -1
% 31.36/4.49  --bmc1_symbol_reachability              true
% 31.36/4.49  --bmc1_property_lemmas                  false
% 31.36/4.49  --bmc1_k_induction                      false
% 31.36/4.49  --bmc1_non_equiv_states                 false
% 31.36/4.49  --bmc1_deadlock                         false
% 31.36/4.49  --bmc1_ucm                              false
% 31.36/4.49  --bmc1_add_unsat_core                   none
% 31.36/4.49  --bmc1_unsat_core_children              false
% 31.36/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.36/4.49  --bmc1_out_stat                         full
% 31.36/4.49  --bmc1_ground_init                      false
% 31.36/4.49  --bmc1_pre_inst_next_state              false
% 31.36/4.49  --bmc1_pre_inst_state                   false
% 31.36/4.49  --bmc1_pre_inst_reach_state             false
% 31.36/4.49  --bmc1_out_unsat_core                   false
% 31.36/4.49  --bmc1_aig_witness_out                  false
% 31.36/4.49  --bmc1_verbose                          false
% 31.36/4.49  --bmc1_dump_clauses_tptp                false
% 31.36/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.36/4.49  --bmc1_dump_file                        -
% 31.36/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.36/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.36/4.49  --bmc1_ucm_extend_mode                  1
% 31.36/4.49  --bmc1_ucm_init_mode                    2
% 31.36/4.49  --bmc1_ucm_cone_mode                    none
% 31.36/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.36/4.49  --bmc1_ucm_relax_model                  4
% 31.36/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.36/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.36/4.49  --bmc1_ucm_layered_model                none
% 31.36/4.49  --bmc1_ucm_max_lemma_size               10
% 31.36/4.49  
% 31.36/4.49  ------ AIG Options
% 31.36/4.49  
% 31.36/4.49  --aig_mode                              false
% 31.36/4.49  
% 31.36/4.49  ------ Instantiation Options
% 31.36/4.49  
% 31.36/4.49  --instantiation_flag                    true
% 31.36/4.49  --inst_sos_flag                         false
% 31.36/4.49  --inst_sos_phase                        true
% 31.36/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.36/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.36/4.49  --inst_lit_sel_side                     num_symb
% 31.36/4.49  --inst_solver_per_active                1400
% 31.36/4.49  --inst_solver_calls_frac                1.
% 31.36/4.49  --inst_passive_queue_type               priority_queues
% 31.36/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.36/4.49  --inst_passive_queues_freq              [25;2]
% 31.36/4.49  --inst_dismatching                      true
% 31.36/4.49  --inst_eager_unprocessed_to_passive     true
% 31.36/4.49  --inst_prop_sim_given                   true
% 31.36/4.49  --inst_prop_sim_new                     false
% 31.36/4.49  --inst_subs_new                         false
% 31.36/4.49  --inst_eq_res_simp                      false
% 31.36/4.49  --inst_subs_given                       false
% 31.36/4.49  --inst_orphan_elimination               true
% 31.36/4.49  --inst_learning_loop_flag               true
% 31.36/4.49  --inst_learning_start                   3000
% 31.36/4.49  --inst_learning_factor                  2
% 31.36/4.49  --inst_start_prop_sim_after_learn       3
% 31.36/4.49  --inst_sel_renew                        solver
% 31.36/4.49  --inst_lit_activity_flag                true
% 31.36/4.49  --inst_restr_to_given                   false
% 31.36/4.49  --inst_activity_threshold               500
% 31.36/4.49  --inst_out_proof                        true
% 31.36/4.49  
% 31.36/4.49  ------ Resolution Options
% 31.36/4.49  
% 31.36/4.49  --resolution_flag                       true
% 31.36/4.49  --res_lit_sel                           adaptive
% 31.36/4.49  --res_lit_sel_side                      none
% 31.36/4.49  --res_ordering                          kbo
% 31.36/4.49  --res_to_prop_solver                    active
% 31.36/4.49  --res_prop_simpl_new                    false
% 31.36/4.49  --res_prop_simpl_given                  true
% 31.36/4.49  --res_passive_queue_type                priority_queues
% 31.36/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.36/4.49  --res_passive_queues_freq               [15;5]
% 31.36/4.49  --res_forward_subs                      full
% 31.36/4.49  --res_backward_subs                     full
% 31.36/4.49  --res_forward_subs_resolution           true
% 31.36/4.49  --res_backward_subs_resolution          true
% 31.36/4.49  --res_orphan_elimination                true
% 31.36/4.49  --res_time_limit                        2.
% 31.36/4.49  --res_out_proof                         true
% 31.36/4.49  
% 31.36/4.49  ------ Superposition Options
% 31.36/4.49  
% 31.36/4.49  --superposition_flag                    true
% 31.36/4.49  --sup_passive_queue_type                priority_queues
% 31.36/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.36/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.36/4.49  --demod_completeness_check              fast
% 31.36/4.49  --demod_use_ground                      true
% 31.36/4.49  --sup_to_prop_solver                    passive
% 31.36/4.49  --sup_prop_simpl_new                    true
% 31.36/4.49  --sup_prop_simpl_given                  true
% 31.36/4.49  --sup_fun_splitting                     false
% 31.36/4.49  --sup_smt_interval                      50000
% 31.36/4.49  
% 31.36/4.49  ------ Superposition Simplification Setup
% 31.36/4.49  
% 31.36/4.49  --sup_indices_passive                   []
% 31.36/4.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.36/4.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.36/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.36/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.36/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.36/4.49  --sup_full_bw                           [BwDemod]
% 31.36/4.49  --sup_immed_triv                        [TrivRules]
% 31.36/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.36/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.36/4.49  --sup_immed_bw_main                     []
% 31.36/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.36/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.36/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.36/4.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.36/4.49  
% 31.36/4.49  ------ Combination Options
% 31.36/4.49  
% 31.36/4.49  --comb_res_mult                         3
% 31.36/4.49  --comb_sup_mult                         2
% 31.36/4.49  --comb_inst_mult                        10
% 31.36/4.49  
% 31.36/4.49  ------ Debug Options
% 31.36/4.49  
% 31.36/4.49  --dbg_backtrace                         false
% 31.36/4.49  --dbg_dump_prop_clauses                 false
% 31.36/4.49  --dbg_dump_prop_clauses_file            -
% 31.36/4.49  --dbg_out_stat                          false
% 31.36/4.49  ------ Parsing...
% 31.36/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.36/4.49  
% 31.36/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.36/4.49  
% 31.36/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.36/4.49  
% 31.36/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.36/4.49  ------ Proving...
% 31.36/4.49  ------ Problem Properties 
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  clauses                                 13
% 31.36/4.49  conjectures                             3
% 31.36/4.49  EPR                                     2
% 31.36/4.49  Horn                                    13
% 31.36/4.49  unary                                   5
% 31.36/4.49  binary                                  5
% 31.36/4.49  lits                                    25
% 31.36/4.49  lits eq                                 2
% 31.36/4.49  fd_pure                                 0
% 31.36/4.49  fd_pseudo                               0
% 31.36/4.49  fd_cond                                 0
% 31.36/4.49  fd_pseudo_cond                          1
% 31.36/4.49  AC symbols                              0
% 31.36/4.49  
% 31.36/4.49  ------ Schedule dynamic 5 is on 
% 31.36/4.49  
% 31.36/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  ------ 
% 31.36/4.49  Current options:
% 31.36/4.49  ------ 
% 31.36/4.49  
% 31.36/4.49  ------ Input Options
% 31.36/4.49  
% 31.36/4.49  --out_options                           all
% 31.36/4.49  --tptp_safe_out                         true
% 31.36/4.49  --problem_path                          ""
% 31.36/4.49  --include_path                          ""
% 31.36/4.49  --clausifier                            res/vclausify_rel
% 31.36/4.49  --clausifier_options                    --mode clausify
% 31.36/4.49  --stdin                                 false
% 31.36/4.49  --stats_out                             all
% 31.36/4.49  
% 31.36/4.49  ------ General Options
% 31.36/4.49  
% 31.36/4.49  --fof                                   false
% 31.36/4.49  --time_out_real                         305.
% 31.36/4.49  --time_out_virtual                      -1.
% 31.36/4.49  --symbol_type_check                     false
% 31.36/4.49  --clausify_out                          false
% 31.36/4.49  --sig_cnt_out                           false
% 31.36/4.49  --trig_cnt_out                          false
% 31.36/4.49  --trig_cnt_out_tolerance                1.
% 31.36/4.49  --trig_cnt_out_sk_spl                   false
% 31.36/4.49  --abstr_cl_out                          false
% 31.36/4.49  
% 31.36/4.49  ------ Global Options
% 31.36/4.49  
% 31.36/4.49  --schedule                              default
% 31.36/4.49  --add_important_lit                     false
% 31.36/4.49  --prop_solver_per_cl                    1000
% 31.36/4.49  --min_unsat_core                        false
% 31.36/4.49  --soft_assumptions                      false
% 31.36/4.49  --soft_lemma_size                       3
% 31.36/4.49  --prop_impl_unit_size                   0
% 31.36/4.49  --prop_impl_unit                        []
% 31.36/4.49  --share_sel_clauses                     true
% 31.36/4.49  --reset_solvers                         false
% 31.36/4.49  --bc_imp_inh                            [conj_cone]
% 31.36/4.49  --conj_cone_tolerance                   3.
% 31.36/4.49  --extra_neg_conj                        none
% 31.36/4.49  --large_theory_mode                     true
% 31.36/4.49  --prolific_symb_bound                   200
% 31.36/4.49  --lt_threshold                          2000
% 31.36/4.49  --clause_weak_htbl                      true
% 31.36/4.49  --gc_record_bc_elim                     false
% 31.36/4.49  
% 31.36/4.49  ------ Preprocessing Options
% 31.36/4.49  
% 31.36/4.49  --preprocessing_flag                    true
% 31.36/4.49  --time_out_prep_mult                    0.1
% 31.36/4.49  --splitting_mode                        input
% 31.36/4.49  --splitting_grd                         true
% 31.36/4.49  --splitting_cvd                         false
% 31.36/4.49  --splitting_cvd_svl                     false
% 31.36/4.49  --splitting_nvd                         32
% 31.36/4.49  --sub_typing                            true
% 31.36/4.49  --prep_gs_sim                           true
% 31.36/4.49  --prep_unflatten                        true
% 31.36/4.49  --prep_res_sim                          true
% 31.36/4.49  --prep_upred                            true
% 31.36/4.49  --prep_sem_filter                       exhaustive
% 31.36/4.49  --prep_sem_filter_out                   false
% 31.36/4.49  --pred_elim                             true
% 31.36/4.49  --res_sim_input                         true
% 31.36/4.49  --eq_ax_congr_red                       true
% 31.36/4.49  --pure_diseq_elim                       true
% 31.36/4.49  --brand_transform                       false
% 31.36/4.49  --non_eq_to_eq                          false
% 31.36/4.49  --prep_def_merge                        true
% 31.36/4.49  --prep_def_merge_prop_impl              false
% 31.36/4.49  --prep_def_merge_mbd                    true
% 31.36/4.49  --prep_def_merge_tr_red                 false
% 31.36/4.49  --prep_def_merge_tr_cl                  false
% 31.36/4.49  --smt_preprocessing                     true
% 31.36/4.49  --smt_ac_axioms                         fast
% 31.36/4.49  --preprocessed_out                      false
% 31.36/4.49  --preprocessed_stats                    false
% 31.36/4.49  
% 31.36/4.49  ------ Abstraction refinement Options
% 31.36/4.49  
% 31.36/4.49  --abstr_ref                             []
% 31.36/4.49  --abstr_ref_prep                        false
% 31.36/4.49  --abstr_ref_until_sat                   false
% 31.36/4.49  --abstr_ref_sig_restrict                funpre
% 31.36/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.36/4.49  --abstr_ref_under                       []
% 31.36/4.49  
% 31.36/4.49  ------ SAT Options
% 31.36/4.49  
% 31.36/4.49  --sat_mode                              false
% 31.36/4.49  --sat_fm_restart_options                ""
% 31.36/4.49  --sat_gr_def                            false
% 31.36/4.49  --sat_epr_types                         true
% 31.36/4.49  --sat_non_cyclic_types                  false
% 31.36/4.49  --sat_finite_models                     false
% 31.36/4.49  --sat_fm_lemmas                         false
% 31.36/4.49  --sat_fm_prep                           false
% 31.36/4.49  --sat_fm_uc_incr                        true
% 31.36/4.49  --sat_out_model                         small
% 31.36/4.49  --sat_out_clauses                       false
% 31.36/4.49  
% 31.36/4.49  ------ QBF Options
% 31.36/4.49  
% 31.36/4.49  --qbf_mode                              false
% 31.36/4.49  --qbf_elim_univ                         false
% 31.36/4.49  --qbf_dom_inst                          none
% 31.36/4.49  --qbf_dom_pre_inst                      false
% 31.36/4.49  --qbf_sk_in                             false
% 31.36/4.49  --qbf_pred_elim                         true
% 31.36/4.49  --qbf_split                             512
% 31.36/4.49  
% 31.36/4.49  ------ BMC1 Options
% 31.36/4.49  
% 31.36/4.49  --bmc1_incremental                      false
% 31.36/4.49  --bmc1_axioms                           reachable_all
% 31.36/4.49  --bmc1_min_bound                        0
% 31.36/4.49  --bmc1_max_bound                        -1
% 31.36/4.49  --bmc1_max_bound_default                -1
% 31.36/4.49  --bmc1_symbol_reachability              true
% 31.36/4.49  --bmc1_property_lemmas                  false
% 31.36/4.49  --bmc1_k_induction                      false
% 31.36/4.49  --bmc1_non_equiv_states                 false
% 31.36/4.49  --bmc1_deadlock                         false
% 31.36/4.49  --bmc1_ucm                              false
% 31.36/4.49  --bmc1_add_unsat_core                   none
% 31.36/4.49  --bmc1_unsat_core_children              false
% 31.36/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.36/4.49  --bmc1_out_stat                         full
% 31.36/4.49  --bmc1_ground_init                      false
% 31.36/4.49  --bmc1_pre_inst_next_state              false
% 31.36/4.49  --bmc1_pre_inst_state                   false
% 31.36/4.49  --bmc1_pre_inst_reach_state             false
% 31.36/4.49  --bmc1_out_unsat_core                   false
% 31.36/4.49  --bmc1_aig_witness_out                  false
% 31.36/4.49  --bmc1_verbose                          false
% 31.36/4.49  --bmc1_dump_clauses_tptp                false
% 31.36/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.36/4.49  --bmc1_dump_file                        -
% 31.36/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.36/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.36/4.49  --bmc1_ucm_extend_mode                  1
% 31.36/4.49  --bmc1_ucm_init_mode                    2
% 31.36/4.49  --bmc1_ucm_cone_mode                    none
% 31.36/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.36/4.49  --bmc1_ucm_relax_model                  4
% 31.36/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.36/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.36/4.49  --bmc1_ucm_layered_model                none
% 31.36/4.49  --bmc1_ucm_max_lemma_size               10
% 31.36/4.49  
% 31.36/4.49  ------ AIG Options
% 31.36/4.49  
% 31.36/4.49  --aig_mode                              false
% 31.36/4.49  
% 31.36/4.49  ------ Instantiation Options
% 31.36/4.49  
% 31.36/4.49  --instantiation_flag                    true
% 31.36/4.49  --inst_sos_flag                         false
% 31.36/4.49  --inst_sos_phase                        true
% 31.36/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.36/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.36/4.49  --inst_lit_sel_side                     none
% 31.36/4.49  --inst_solver_per_active                1400
% 31.36/4.49  --inst_solver_calls_frac                1.
% 31.36/4.49  --inst_passive_queue_type               priority_queues
% 31.36/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.36/4.49  --inst_passive_queues_freq              [25;2]
% 31.36/4.49  --inst_dismatching                      true
% 31.36/4.49  --inst_eager_unprocessed_to_passive     true
% 31.36/4.49  --inst_prop_sim_given                   true
% 31.36/4.49  --inst_prop_sim_new                     false
% 31.36/4.49  --inst_subs_new                         false
% 31.36/4.49  --inst_eq_res_simp                      false
% 31.36/4.49  --inst_subs_given                       false
% 31.36/4.49  --inst_orphan_elimination               true
% 31.36/4.49  --inst_learning_loop_flag               true
% 31.36/4.49  --inst_learning_start                   3000
% 31.36/4.49  --inst_learning_factor                  2
% 31.36/4.49  --inst_start_prop_sim_after_learn       3
% 31.36/4.49  --inst_sel_renew                        solver
% 31.36/4.49  --inst_lit_activity_flag                true
% 31.36/4.49  --inst_restr_to_given                   false
% 31.36/4.49  --inst_activity_threshold               500
% 31.36/4.49  --inst_out_proof                        true
% 31.36/4.49  
% 31.36/4.49  ------ Resolution Options
% 31.36/4.49  
% 31.36/4.49  --resolution_flag                       false
% 31.36/4.49  --res_lit_sel                           adaptive
% 31.36/4.49  --res_lit_sel_side                      none
% 31.36/4.49  --res_ordering                          kbo
% 31.36/4.49  --res_to_prop_solver                    active
% 31.36/4.49  --res_prop_simpl_new                    false
% 31.36/4.49  --res_prop_simpl_given                  true
% 31.36/4.49  --res_passive_queue_type                priority_queues
% 31.36/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.36/4.49  --res_passive_queues_freq               [15;5]
% 31.36/4.49  --res_forward_subs                      full
% 31.36/4.49  --res_backward_subs                     full
% 31.36/4.49  --res_forward_subs_resolution           true
% 31.36/4.49  --res_backward_subs_resolution          true
% 31.36/4.49  --res_orphan_elimination                true
% 31.36/4.49  --res_time_limit                        2.
% 31.36/4.49  --res_out_proof                         true
% 31.36/4.49  
% 31.36/4.49  ------ Superposition Options
% 31.36/4.49  
% 31.36/4.49  --superposition_flag                    true
% 31.36/4.49  --sup_passive_queue_type                priority_queues
% 31.36/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.36/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.36/4.49  --demod_completeness_check              fast
% 31.36/4.49  --demod_use_ground                      true
% 31.36/4.49  --sup_to_prop_solver                    passive
% 31.36/4.49  --sup_prop_simpl_new                    true
% 31.36/4.49  --sup_prop_simpl_given                  true
% 31.36/4.49  --sup_fun_splitting                     false
% 31.36/4.49  --sup_smt_interval                      50000
% 31.36/4.49  
% 31.36/4.49  ------ Superposition Simplification Setup
% 31.36/4.49  
% 31.36/4.49  --sup_indices_passive                   []
% 31.36/4.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.36/4.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.36/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.36/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.36/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.36/4.49  --sup_full_bw                           [BwDemod]
% 31.36/4.49  --sup_immed_triv                        [TrivRules]
% 31.36/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.36/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.36/4.49  --sup_immed_bw_main                     []
% 31.36/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.36/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.36/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.36/4.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.36/4.49  
% 31.36/4.49  ------ Combination Options
% 31.36/4.49  
% 31.36/4.49  --comb_res_mult                         3
% 31.36/4.49  --comb_sup_mult                         2
% 31.36/4.49  --comb_inst_mult                        10
% 31.36/4.49  
% 31.36/4.49  ------ Debug Options
% 31.36/4.49  
% 31.36/4.49  --dbg_backtrace                         false
% 31.36/4.49  --dbg_dump_prop_clauses                 false
% 31.36/4.49  --dbg_dump_prop_clauses_file            -
% 31.36/4.49  --dbg_out_stat                          false
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  ------ Proving...
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  % SZS status Theorem for theBenchmark.p
% 31.36/4.49  
% 31.36/4.49   Resolution empty clause
% 31.36/4.49  
% 31.36/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.36/4.49  
% 31.36/4.49  fof(f9,axiom,(
% 31.36/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f18,plain,(
% 31.36/4.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.36/4.49    inference(ennf_transformation,[],[f9])).
% 31.36/4.49  
% 31.36/4.49  fof(f19,plain,(
% 31.36/4.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.36/4.49    inference(flattening,[],[f18])).
% 31.36/4.49  
% 31.36/4.49  fof(f39,plain,(
% 31.36/4.49    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.36/4.49    inference(cnf_transformation,[],[f19])).
% 31.36/4.49  
% 31.36/4.49  fof(f10,conjecture,(
% 31.36/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f11,negated_conjecture,(
% 31.36/4.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 31.36/4.49    inference(negated_conjecture,[],[f10])).
% 31.36/4.49  
% 31.36/4.49  fof(f20,plain,(
% 31.36/4.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.36/4.49    inference(ennf_transformation,[],[f11])).
% 31.36/4.49  
% 31.36/4.49  fof(f26,plain,(
% 31.36/4.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.36/4.49    introduced(choice_axiom,[])).
% 31.36/4.49  
% 31.36/4.49  fof(f25,plain,(
% 31.36/4.49    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.36/4.49    introduced(choice_axiom,[])).
% 31.36/4.49  
% 31.36/4.49  fof(f24,plain,(
% 31.36/4.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.36/4.49    introduced(choice_axiom,[])).
% 31.36/4.49  
% 31.36/4.49  fof(f27,plain,(
% 31.36/4.49    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.36/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26,f25,f24])).
% 31.36/4.49  
% 31.36/4.49  fof(f40,plain,(
% 31.36/4.49    l1_pre_topc(sK0)),
% 31.36/4.49    inference(cnf_transformation,[],[f27])).
% 31.36/4.49  
% 31.36/4.49  fof(f3,axiom,(
% 31.36/4.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f12,plain,(
% 31.36/4.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 31.36/4.49    inference(ennf_transformation,[],[f3])).
% 31.36/4.49  
% 31.36/4.49  fof(f13,plain,(
% 31.36/4.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 31.36/4.49    inference(flattening,[],[f12])).
% 31.36/4.49  
% 31.36/4.49  fof(f32,plain,(
% 31.36/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.36/4.49    inference(cnf_transformation,[],[f13])).
% 31.36/4.49  
% 31.36/4.49  fof(f6,axiom,(
% 31.36/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f35,plain,(
% 31.36/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.36/4.49    inference(cnf_transformation,[],[f6])).
% 31.36/4.49  
% 31.36/4.49  fof(f45,plain,(
% 31.36/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.36/4.49    inference(definition_unfolding,[],[f32,f35])).
% 31.36/4.49  
% 31.36/4.49  fof(f42,plain,(
% 31.36/4.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.36/4.49    inference(cnf_transformation,[],[f27])).
% 31.36/4.49  
% 31.36/4.49  fof(f8,axiom,(
% 31.36/4.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f16,plain,(
% 31.36/4.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.36/4.49    inference(ennf_transformation,[],[f8])).
% 31.36/4.49  
% 31.36/4.49  fof(f17,plain,(
% 31.36/4.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.36/4.49    inference(flattening,[],[f16])).
% 31.36/4.49  
% 31.36/4.49  fof(f38,plain,(
% 31.36/4.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.36/4.49    inference(cnf_transformation,[],[f17])).
% 31.36/4.49  
% 31.36/4.49  fof(f7,axiom,(
% 31.36/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f23,plain,(
% 31.36/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.36/4.49    inference(nnf_transformation,[],[f7])).
% 31.36/4.49  
% 31.36/4.49  fof(f36,plain,(
% 31.36/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.36/4.49    inference(cnf_transformation,[],[f23])).
% 31.36/4.49  
% 31.36/4.49  fof(f5,axiom,(
% 31.36/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f15,plain,(
% 31.36/4.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 31.36/4.49    inference(ennf_transformation,[],[f5])).
% 31.36/4.49  
% 31.36/4.49  fof(f34,plain,(
% 31.36/4.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 31.36/4.49    inference(cnf_transformation,[],[f15])).
% 31.36/4.49  
% 31.36/4.49  fof(f46,plain,(
% 31.36/4.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 31.36/4.49    inference(definition_unfolding,[],[f34,f35])).
% 31.36/4.49  
% 31.36/4.49  fof(f37,plain,(
% 31.36/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.36/4.49    inference(cnf_transformation,[],[f23])).
% 31.36/4.49  
% 31.36/4.49  fof(f43,plain,(
% 31.36/4.49    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 31.36/4.49    inference(cnf_transformation,[],[f27])).
% 31.36/4.49  
% 31.36/4.49  fof(f2,axiom,(
% 31.36/4.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f31,plain,(
% 31.36/4.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 31.36/4.49    inference(cnf_transformation,[],[f2])).
% 31.36/4.49  
% 31.36/4.49  fof(f44,plain,(
% 31.36/4.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 31.36/4.49    inference(definition_unfolding,[],[f31,f35])).
% 31.36/4.49  
% 31.36/4.49  fof(f4,axiom,(
% 31.36/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f14,plain,(
% 31.36/4.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 31.36/4.49    inference(ennf_transformation,[],[f4])).
% 31.36/4.49  
% 31.36/4.49  fof(f33,plain,(
% 31.36/4.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 31.36/4.49    inference(cnf_transformation,[],[f14])).
% 31.36/4.49  
% 31.36/4.49  fof(f41,plain,(
% 31.36/4.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.36/4.49    inference(cnf_transformation,[],[f27])).
% 31.36/4.49  
% 31.36/4.49  fof(f1,axiom,(
% 31.36/4.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.36/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.36/4.49  
% 31.36/4.49  fof(f21,plain,(
% 31.36/4.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.36/4.49    inference(nnf_transformation,[],[f1])).
% 31.36/4.49  
% 31.36/4.49  fof(f22,plain,(
% 31.36/4.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.36/4.49    inference(flattening,[],[f21])).
% 31.36/4.49  
% 31.36/4.49  fof(f30,plain,(
% 31.36/4.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.36/4.49    inference(cnf_transformation,[],[f22])).
% 31.36/4.49  
% 31.36/4.49  fof(f28,plain,(
% 31.36/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.36/4.49    inference(cnf_transformation,[],[f22])).
% 31.36/4.49  
% 31.36/4.49  fof(f48,plain,(
% 31.36/4.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.36/4.49    inference(equality_resolution,[],[f28])).
% 31.36/4.49  
% 31.36/4.49  cnf(c_10,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | ~ r1_tarski(X0,X2)
% 31.36/4.49      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 31.36/4.49      | ~ l1_pre_topc(X1) ),
% 31.36/4.49      inference(cnf_transformation,[],[f39]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_14,negated_conjecture,
% 31.36/4.49      ( l1_pre_topc(sK0) ),
% 31.36/4.49      inference(cnf_transformation,[],[f40]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_199,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | ~ r1_tarski(X0,X2)
% 31.36/4.49      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 31.36/4.49      | sK0 != X1 ),
% 31.36/4.49      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_200,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.36/4.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.36/4.49      | ~ r1_tarski(X1,X0)
% 31.36/4.49      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 31.36/4.49      inference(unflattening,[status(thm)],[c_199]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_679,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | r1_tarski(X1,X0) != iProver_top
% 31.36/4.49      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_4,plain,
% 31.36/4.49      ( ~ r1_tarski(X0,X1)
% 31.36/4.49      | ~ r1_tarski(X0,X2)
% 31.36/4.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 31.36/4.49      inference(cnf_transformation,[],[f45]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_687,plain,
% 31.36/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.36/4.49      | r1_tarski(X0,X2) != iProver_top
% 31.36/4.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_12,negated_conjecture,
% 31.36/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.36/4.49      inference(cnf_transformation,[],[f42]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_683,plain,
% 31.36/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_9,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | ~ l1_pre_topc(X1) ),
% 31.36/4.49      inference(cnf_transformation,[],[f38]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_217,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.36/4.49      | sK0 != X1 ),
% 31.36/4.49      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_218,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.36/4.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.36/4.49      inference(unflattening,[status(thm)],[c_217]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_678,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_8,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.36/4.49      inference(cnf_transformation,[],[f36]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_685,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.36/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_1105,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_678,c_685]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_6,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.36/4.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 31.36/4.49      inference(cnf_transformation,[],[f46]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_7,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.36/4.49      inference(cnf_transformation,[],[f37]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_115,plain,
% 31.36/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.36/4.49      inference(prop_impl,[status(thm)],[c_7]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_116,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.36/4.49      inference(renaming,[status(thm)],[c_115]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_139,plain,
% 31.36/4.49      ( ~ r1_tarski(X0,X1)
% 31.36/4.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 31.36/4.49      inference(bin_hyper_res,[status(thm)],[c_6,c_116]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_680,plain,
% 31.36/4.49      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 31.36/4.49      | r1_tarski(X2,X0) != iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_2015,plain,
% 31.36/4.49      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
% 31.36/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_1105,c_680]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_9880,plain,
% 31.36/4.49      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_683,c_2015]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_1103,plain,
% 31.36/4.49      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_683,c_685]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_1554,plain,
% 31.36/4.49      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_1103,c_680]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_11,negated_conjecture,
% 31.36/4.49      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 31.36/4.49      inference(cnf_transformation,[],[f43]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_684,plain,
% 31.36/4.49      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_1646,plain,
% 31.36/4.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 31.36/4.49      inference(demodulation,[status(thm)],[c_1554,c_684]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_10180,plain,
% 31.36/4.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
% 31.36/4.49      inference(demodulation,[status(thm)],[c_9880,c_1646]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_10420,plain,
% 31.36/4.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 31.36/4.49      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_687,c_10180]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_21603,plain,
% 31.36/4.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
% 31.36/4.49      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_679,c_10420]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_17,plain,
% 31.36/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_3,plain,
% 31.36/4.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 31.36/4.49      inference(cnf_transformation,[],[f44]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_688,plain,
% 31.36/4.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_5,plain,
% 31.36/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.36/4.49      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 31.36/4.49      inference(cnf_transformation,[],[f33]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_138,plain,
% 31.36/4.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 31.36/4.49      | ~ r1_tarski(X2,X0) ),
% 31.36/4.49      inference(bin_hyper_res,[status(thm)],[c_5,c_116]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_681,plain,
% 31.36/4.49      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 31.36/4.49      | r1_tarski(X2,X0) != iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_2220,plain,
% 31.36/4.49      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.36/4.49      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_1554,c_681]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_12794,plain,
% 31.36/4.49      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.36/4.49      inference(global_propositional_subsumption,[status(thm)],[c_2220,c_1103]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_12803,plain,
% 31.36/4.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),u1_struct_0(sK0)) = iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_12794,c_685]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_13,negated_conjecture,
% 31.36/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.36/4.49      inference(cnf_transformation,[],[f41]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_682,plain,
% 31.36/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_686,plain,
% 31.36/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.36/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_0,plain,
% 31.36/4.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.36/4.49      inference(cnf_transformation,[],[f30]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_690,plain,
% 31.36/4.49      ( X0 = X1
% 31.36/4.49      | r1_tarski(X0,X1) != iProver_top
% 31.36/4.49      | r1_tarski(X1,X0) != iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_1327,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 31.36/4.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_688,c_690]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_3504,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 31.36/4.49      | r1_tarski(X0,X1) != iProver_top
% 31.36/4.49      | r1_tarski(X0,X0) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_687,c_1327]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f48]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_43,plain,
% 31.36/4.49      ( r1_tarski(X0,X0) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_3687,plain,
% 31.36/4.49      ( r1_tarski(X0,X1) != iProver_top | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 31.36/4.49      inference(global_propositional_subsumption,[status(thm)],[c_3504,c_43]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_3688,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 31.36/4.49      inference(renaming,[status(thm)],[c_3687]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_3699,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,X0)
% 31.36/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_679,c_3688]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_4827,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,X0)
% 31.36/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | r1_tarski(X0,X1) != iProver_top
% 31.36/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_686,c_3699]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_51070,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,X0)
% 31.36/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 31.36/4.49      | r1_tarski(X0,sK1) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_682,c_4827]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_51718,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0,sK2))),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0,sK2)))
% 31.36/4.49      | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK1) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_12803,c_51070]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_52539,plain,
% 31.36/4.49      ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_688,c_51718]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_689,plain,
% 31.36/4.49      ( r1_tarski(X0,X0) = iProver_top ),
% 31.36/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_1227,plain,
% 31.36/4.49      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_689,c_680]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_2451,plain,
% 31.36/4.49      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
% 31.36/4.49      | r1_tarski(X1,X1) != iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_1227,c_681]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_17621,plain,
% 31.36/4.49      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 31.36/4.49      inference(forward_subsumption_resolution,[status(thm)],[c_2451,c_689]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_17637,plain,
% 31.36/4.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_17621,c_685]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_53648,plain,
% 31.36/4.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 31.36/4.49      inference(superposition,[status(thm)],[c_52539,c_17637]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_128366,plain,
% 31.36/4.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.36/4.49      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 31.36/4.49      inference(global_propositional_subsumption,
% 31.36/4.49                [status(thm)],
% 31.36/4.49                [c_21603,c_17,c_53648]) ).
% 31.36/4.49  
% 31.36/4.49  cnf(c_128372,plain,
% 31.36/4.49      ( $false ),
% 31.36/4.49      inference(forward_subsumption_resolution,
% 31.36/4.49                [status(thm)],
% 31.36/4.49                [c_128366,c_17637,c_12794]) ).
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.36/4.49  
% 31.36/4.49  ------                               Statistics
% 31.36/4.49  
% 31.36/4.49  ------ General
% 31.36/4.49  
% 31.36/4.49  abstr_ref_over_cycles:                  0
% 31.36/4.49  abstr_ref_under_cycles:                 0
% 31.36/4.49  gc_basic_clause_elim:                   0
% 31.36/4.49  forced_gc_time:                         0
% 31.36/4.49  parsing_time:                           0.008
% 31.36/4.49  unif_index_cands_time:                  0.
% 31.36/4.49  unif_index_add_time:                    0.
% 31.36/4.49  orderings_time:                         0.
% 31.36/4.49  out_proof_time:                         0.017
% 31.36/4.49  total_time:                             3.679
% 31.36/4.49  num_of_symbols:                         43
% 31.36/4.49  num_of_terms:                           135642
% 31.36/4.49  
% 31.36/4.49  ------ Preprocessing
% 31.36/4.49  
% 31.36/4.49  num_of_splits:                          0
% 31.36/4.49  num_of_split_atoms:                     0
% 31.36/4.49  num_of_reused_defs:                     0
% 31.36/4.49  num_eq_ax_congr_red:                    6
% 31.36/4.49  num_of_sem_filtered_clauses:            1
% 31.36/4.49  num_of_subtypes:                        0
% 31.36/4.49  monotx_restored_types:                  0
% 31.36/4.49  sat_num_of_epr_types:                   0
% 31.36/4.49  sat_num_of_non_cyclic_types:            0
% 31.36/4.49  sat_guarded_non_collapsed_types:        0
% 31.36/4.49  num_pure_diseq_elim:                    0
% 31.36/4.49  simp_replaced_by:                       0
% 31.36/4.49  res_preprocessed:                       72
% 31.36/4.49  prep_upred:                             0
% 31.36/4.49  prep_unflattend:                        2
% 31.36/4.49  smt_new_axioms:                         0
% 31.36/4.49  pred_elim_cands:                        2
% 31.36/4.49  pred_elim:                              1
% 31.36/4.49  pred_elim_cl:                           1
% 31.36/4.49  pred_elim_cycles:                       3
% 31.36/4.49  merged_defs:                            8
% 31.36/4.49  merged_defs_ncl:                        0
% 31.36/4.49  bin_hyper_res:                          10
% 31.36/4.49  prep_cycles:                            4
% 31.36/4.49  pred_elim_time:                         0.001
% 31.36/4.49  splitting_time:                         0.
% 31.36/4.49  sem_filter_time:                        0.
% 31.36/4.49  monotx_time:                            0.001
% 31.36/4.49  subtype_inf_time:                       0.
% 31.36/4.49  
% 31.36/4.49  ------ Problem properties
% 31.36/4.49  
% 31.36/4.49  clauses:                                13
% 31.36/4.49  conjectures:                            3
% 31.36/4.49  epr:                                    2
% 31.36/4.49  horn:                                   13
% 31.36/4.49  ground:                                 3
% 31.36/4.49  unary:                                  5
% 31.36/4.49  binary:                                 5
% 31.36/4.49  lits:                                   25
% 31.36/4.49  lits_eq:                                2
% 31.36/4.49  fd_pure:                                0
% 31.36/4.49  fd_pseudo:                              0
% 31.36/4.49  fd_cond:                                0
% 31.36/4.49  fd_pseudo_cond:                         1
% 31.36/4.49  ac_symbols:                             0
% 31.36/4.49  
% 31.36/4.49  ------ Propositional Solver
% 31.36/4.49  
% 31.36/4.49  prop_solver_calls:                      46
% 31.36/4.49  prop_fast_solver_calls:                 2704
% 31.36/4.49  smt_solver_calls:                       0
% 31.36/4.49  smt_fast_solver_calls:                  0
% 31.36/4.49  prop_num_of_clauses:                    45412
% 31.36/4.49  prop_preprocess_simplified:             66002
% 31.36/4.49  prop_fo_subsumed:                       99
% 31.36/4.49  prop_solver_time:                       0.
% 31.36/4.49  smt_solver_time:                        0.
% 31.36/4.49  smt_fast_solver_time:                   0.
% 31.36/4.49  prop_fast_solver_time:                  0.
% 31.36/4.49  prop_unsat_core_time:                   0.
% 31.36/4.49  
% 31.36/4.49  ------ QBF
% 31.36/4.49  
% 31.36/4.49  qbf_q_res:                              0
% 31.36/4.49  qbf_num_tautologies:                    0
% 31.36/4.49  qbf_prep_cycles:                        0
% 31.36/4.49  
% 31.36/4.49  ------ BMC1
% 31.36/4.49  
% 31.36/4.49  bmc1_current_bound:                     -1
% 31.36/4.49  bmc1_last_solved_bound:                 -1
% 31.36/4.49  bmc1_unsat_core_size:                   -1
% 31.36/4.49  bmc1_unsat_core_parents_size:           -1
% 31.36/4.49  bmc1_merge_next_fun:                    0
% 31.36/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.36/4.49  
% 31.36/4.49  ------ Instantiation
% 31.36/4.49  
% 31.36/4.49  inst_num_of_clauses:                    3951
% 31.36/4.49  inst_num_in_passive:                    1754
% 31.36/4.49  inst_num_in_active:                     4639
% 31.36/4.49  inst_num_in_unprocessed:                440
% 31.36/4.49  inst_num_of_loops:                      4829
% 31.36/4.49  inst_num_of_learning_restarts:          1
% 31.36/4.49  inst_num_moves_active_passive:          187
% 31.36/4.49  inst_lit_activity:                      0
% 31.36/4.49  inst_lit_activity_moves:                2
% 31.36/4.49  inst_num_tautologies:                   0
% 31.36/4.49  inst_num_prop_implied:                  0
% 31.36/4.49  inst_num_existing_simplified:           0
% 31.36/4.49  inst_num_eq_res_simplified:             0
% 31.36/4.49  inst_num_child_elim:                    0
% 31.36/4.49  inst_num_of_dismatching_blockings:      9140
% 31.36/4.49  inst_num_of_non_proper_insts:           15808
% 31.36/4.49  inst_num_of_duplicates:                 0
% 31.36/4.49  inst_inst_num_from_inst_to_res:         0
% 31.36/4.49  inst_dismatching_checking_time:         0.
% 31.36/4.49  
% 31.36/4.49  ------ Resolution
% 31.36/4.49  
% 31.36/4.49  res_num_of_clauses:                     22
% 31.36/4.49  res_num_in_passive:                     22
% 31.36/4.49  res_num_in_active:                      0
% 31.36/4.49  res_num_of_loops:                       76
% 31.36/4.49  res_forward_subset_subsumed:            565
% 31.36/4.49  res_backward_subset_subsumed:           8
% 31.36/4.49  res_forward_subsumed:                   0
% 31.36/4.49  res_backward_subsumed:                  0
% 31.36/4.49  res_forward_subsumption_resolution:     0
% 31.36/4.49  res_backward_subsumption_resolution:    0
% 31.36/4.49  res_clause_to_clause_subsumption:       52229
% 31.36/4.49  res_orphan_elimination:                 0
% 31.36/4.49  res_tautology_del:                      727
% 31.36/4.49  res_num_eq_res_simplified:              0
% 31.36/4.49  res_num_sel_changes:                    0
% 31.36/4.49  res_moves_from_active_to_pass:          0
% 31.36/4.49  
% 31.36/4.49  ------ Superposition
% 31.36/4.49  
% 31.36/4.49  sup_time_total:                         0.
% 31.36/4.49  sup_time_generating:                    0.
% 31.36/4.49  sup_time_sim_full:                      0.
% 31.36/4.49  sup_time_sim_immed:                     0.
% 31.36/4.49  
% 31.36/4.49  sup_num_of_clauses:                     5320
% 31.36/4.49  sup_num_in_active:                      946
% 31.36/4.49  sup_num_in_passive:                     4374
% 31.36/4.49  sup_num_of_loops:                       964
% 31.36/4.49  sup_fw_superposition:                   5692
% 31.36/4.49  sup_bw_superposition:                   4042
% 31.36/4.49  sup_immediate_simplified:               5346
% 31.36/4.49  sup_given_eliminated:                   8
% 31.36/4.49  comparisons_done:                       0
% 31.36/4.49  comparisons_avoided:                    0
% 31.36/4.49  
% 31.36/4.49  ------ Simplifications
% 31.36/4.49  
% 31.36/4.49  
% 31.36/4.49  sim_fw_subset_subsumed:                 157
% 31.36/4.49  sim_bw_subset_subsumed:                 44
% 31.36/4.49  sim_fw_subsumed:                        1181
% 31.36/4.49  sim_bw_subsumed:                        41
% 31.36/4.49  sim_fw_subsumption_res:                 8
% 31.36/4.49  sim_bw_subsumption_res:                 0
% 31.36/4.49  sim_tautology_del:                      77
% 31.36/4.49  sim_eq_tautology_del:                   552
% 31.36/4.49  sim_eq_res_simp:                        0
% 31.36/4.49  sim_fw_demodulated:                     1598
% 31.36/4.49  sim_bw_demodulated:                     52
% 31.36/4.49  sim_light_normalised:                   3004
% 31.36/4.49  sim_joinable_taut:                      0
% 31.36/4.49  sim_joinable_simp:                      0
% 31.36/4.49  sim_ac_normalised:                      0
% 31.36/4.49  sim_smt_subsumption:                    0
% 31.36/4.49  
%------------------------------------------------------------------------------
