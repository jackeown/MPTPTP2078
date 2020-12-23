%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:36 EST 2020

% Result     : Theorem 27.37s
% Output     : CNFRefutation 27.37s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 270 expanded)
%              Number of clauses        :   69 ( 104 expanded)
%              Number of leaves         :   13 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  277 ( 775 expanded)
%              Number of equality atoms :   70 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f28,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27,f26,f25])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_691,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_687,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_682,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_689,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_689])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_116])).

cnf(c_140,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_117])).

cnf(c_684,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_2024,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_684])).

cnf(c_8505,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_687,c_2024])).

cnf(c_1107,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_689])).

cnf(c_1234,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1107,c_684])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_688,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1679,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1234,c_688])).

cnf(c_8536,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8505,c_1679])).

cnf(c_9345,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_8536])).

cnf(c_20111,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_9345])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_935,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_938,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_686,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1108,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_689])).

cnf(c_791,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_992,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_11076,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_45667,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_11076])).

cnf(c_45701,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45667])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_940,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0,X1))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_2845,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,X0))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_45806,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_45811,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45806])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_993,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3008,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_54218,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3008])).

cnf(c_54219,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54218])).

cnf(c_941,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1415,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_54341,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_54342,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54341])).

cnf(c_105547,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20111,c_16,c_17,c_938,c_1108,c_45701,c_45811,c_54219,c_54342])).

cnf(c_693,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1233,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_693,c_684])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_139,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_117])).

cnf(c_685,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_2398,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_685])).

cnf(c_16382,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2398,c_693])).

cnf(c_16400,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_16382,c_689])).

cnf(c_105552,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_105547,c_16400])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:13:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.37/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/3.98  
% 27.37/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.37/3.98  
% 27.37/3.98  ------  iProver source info
% 27.37/3.98  
% 27.37/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.37/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.37/3.98  git: non_committed_changes: false
% 27.37/3.98  git: last_make_outside_of_git: false
% 27.37/3.98  
% 27.37/3.98  ------ 
% 27.37/3.98  
% 27.37/3.98  ------ Input Options
% 27.37/3.98  
% 27.37/3.98  --out_options                           all
% 27.37/3.98  --tptp_safe_out                         true
% 27.37/3.98  --problem_path                          ""
% 27.37/3.98  --include_path                          ""
% 27.37/3.98  --clausifier                            res/vclausify_rel
% 27.37/3.98  --clausifier_options                    --mode clausify
% 27.37/3.98  --stdin                                 false
% 27.37/3.98  --stats_out                             all
% 27.37/3.98  
% 27.37/3.98  ------ General Options
% 27.37/3.98  
% 27.37/3.98  --fof                                   false
% 27.37/3.98  --time_out_real                         305.
% 27.37/3.98  --time_out_virtual                      -1.
% 27.37/3.98  --symbol_type_check                     false
% 27.37/3.98  --clausify_out                          false
% 27.37/3.98  --sig_cnt_out                           false
% 27.37/3.98  --trig_cnt_out                          false
% 27.37/3.98  --trig_cnt_out_tolerance                1.
% 27.37/3.98  --trig_cnt_out_sk_spl                   false
% 27.37/3.98  --abstr_cl_out                          false
% 27.37/3.98  
% 27.37/3.98  ------ Global Options
% 27.37/3.98  
% 27.37/3.98  --schedule                              default
% 27.37/3.98  --add_important_lit                     false
% 27.37/3.98  --prop_solver_per_cl                    1000
% 27.37/3.98  --min_unsat_core                        false
% 27.37/3.98  --soft_assumptions                      false
% 27.37/3.98  --soft_lemma_size                       3
% 27.37/3.98  --prop_impl_unit_size                   0
% 27.37/3.98  --prop_impl_unit                        []
% 27.37/3.98  --share_sel_clauses                     true
% 27.37/3.98  --reset_solvers                         false
% 27.37/3.98  --bc_imp_inh                            [conj_cone]
% 27.37/3.98  --conj_cone_tolerance                   3.
% 27.37/3.98  --extra_neg_conj                        none
% 27.37/3.98  --large_theory_mode                     true
% 27.37/3.98  --prolific_symb_bound                   200
% 27.37/3.98  --lt_threshold                          2000
% 27.37/3.98  --clause_weak_htbl                      true
% 27.37/3.98  --gc_record_bc_elim                     false
% 27.37/3.98  
% 27.37/3.98  ------ Preprocessing Options
% 27.37/3.98  
% 27.37/3.98  --preprocessing_flag                    true
% 27.37/3.98  --time_out_prep_mult                    0.1
% 27.37/3.98  --splitting_mode                        input
% 27.37/3.98  --splitting_grd                         true
% 27.37/3.98  --splitting_cvd                         false
% 27.37/3.98  --splitting_cvd_svl                     false
% 27.37/3.98  --splitting_nvd                         32
% 27.37/3.98  --sub_typing                            true
% 27.37/3.98  --prep_gs_sim                           true
% 27.37/3.98  --prep_unflatten                        true
% 27.37/3.98  --prep_res_sim                          true
% 27.37/3.98  --prep_upred                            true
% 27.37/3.98  --prep_sem_filter                       exhaustive
% 27.37/3.98  --prep_sem_filter_out                   false
% 27.37/3.98  --pred_elim                             true
% 27.37/3.98  --res_sim_input                         true
% 27.37/3.98  --eq_ax_congr_red                       true
% 27.37/3.98  --pure_diseq_elim                       true
% 27.37/3.98  --brand_transform                       false
% 27.37/3.98  --non_eq_to_eq                          false
% 27.37/3.98  --prep_def_merge                        true
% 27.37/3.98  --prep_def_merge_prop_impl              false
% 27.37/3.98  --prep_def_merge_mbd                    true
% 27.37/3.98  --prep_def_merge_tr_red                 false
% 27.37/3.98  --prep_def_merge_tr_cl                  false
% 27.37/3.98  --smt_preprocessing                     true
% 27.37/3.98  --smt_ac_axioms                         fast
% 27.37/3.98  --preprocessed_out                      false
% 27.37/3.98  --preprocessed_stats                    false
% 27.37/3.98  
% 27.37/3.98  ------ Abstraction refinement Options
% 27.37/3.98  
% 27.37/3.98  --abstr_ref                             []
% 27.37/3.98  --abstr_ref_prep                        false
% 27.37/3.98  --abstr_ref_until_sat                   false
% 27.37/3.98  --abstr_ref_sig_restrict                funpre
% 27.37/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.37/3.98  --abstr_ref_under                       []
% 27.37/3.98  
% 27.37/3.98  ------ SAT Options
% 27.37/3.98  
% 27.37/3.98  --sat_mode                              false
% 27.37/3.98  --sat_fm_restart_options                ""
% 27.37/3.98  --sat_gr_def                            false
% 27.37/3.98  --sat_epr_types                         true
% 27.37/3.98  --sat_non_cyclic_types                  false
% 27.37/3.98  --sat_finite_models                     false
% 27.37/3.98  --sat_fm_lemmas                         false
% 27.37/3.98  --sat_fm_prep                           false
% 27.37/3.98  --sat_fm_uc_incr                        true
% 27.37/3.98  --sat_out_model                         small
% 27.37/3.98  --sat_out_clauses                       false
% 27.37/3.98  
% 27.37/3.98  ------ QBF Options
% 27.37/3.98  
% 27.37/3.98  --qbf_mode                              false
% 27.37/3.98  --qbf_elim_univ                         false
% 27.37/3.98  --qbf_dom_inst                          none
% 27.37/3.98  --qbf_dom_pre_inst                      false
% 27.37/3.98  --qbf_sk_in                             false
% 27.37/3.98  --qbf_pred_elim                         true
% 27.37/3.98  --qbf_split                             512
% 27.37/3.98  
% 27.37/3.98  ------ BMC1 Options
% 27.37/3.98  
% 27.37/3.98  --bmc1_incremental                      false
% 27.37/3.98  --bmc1_axioms                           reachable_all
% 27.37/3.98  --bmc1_min_bound                        0
% 27.37/3.98  --bmc1_max_bound                        -1
% 27.37/3.98  --bmc1_max_bound_default                -1
% 27.37/3.98  --bmc1_symbol_reachability              true
% 27.37/3.98  --bmc1_property_lemmas                  false
% 27.37/3.98  --bmc1_k_induction                      false
% 27.37/3.98  --bmc1_non_equiv_states                 false
% 27.37/3.98  --bmc1_deadlock                         false
% 27.37/3.98  --bmc1_ucm                              false
% 27.37/3.98  --bmc1_add_unsat_core                   none
% 27.37/3.98  --bmc1_unsat_core_children              false
% 27.37/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.37/3.98  --bmc1_out_stat                         full
% 27.37/3.98  --bmc1_ground_init                      false
% 27.37/3.98  --bmc1_pre_inst_next_state              false
% 27.37/3.98  --bmc1_pre_inst_state                   false
% 27.37/3.98  --bmc1_pre_inst_reach_state             false
% 27.37/3.98  --bmc1_out_unsat_core                   false
% 27.37/3.98  --bmc1_aig_witness_out                  false
% 27.37/3.98  --bmc1_verbose                          false
% 27.37/3.98  --bmc1_dump_clauses_tptp                false
% 27.37/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.37/3.98  --bmc1_dump_file                        -
% 27.37/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.37/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.37/3.98  --bmc1_ucm_extend_mode                  1
% 27.37/3.98  --bmc1_ucm_init_mode                    2
% 27.37/3.98  --bmc1_ucm_cone_mode                    none
% 27.37/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.37/3.98  --bmc1_ucm_relax_model                  4
% 27.37/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.37/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.37/3.98  --bmc1_ucm_layered_model                none
% 27.37/3.98  --bmc1_ucm_max_lemma_size               10
% 27.37/3.98  
% 27.37/3.98  ------ AIG Options
% 27.37/3.98  
% 27.37/3.98  --aig_mode                              false
% 27.37/3.98  
% 27.37/3.98  ------ Instantiation Options
% 27.37/3.98  
% 27.37/3.98  --instantiation_flag                    true
% 27.37/3.98  --inst_sos_flag                         false
% 27.37/3.98  --inst_sos_phase                        true
% 27.37/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.37/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.37/3.98  --inst_lit_sel_side                     num_symb
% 27.37/3.98  --inst_solver_per_active                1400
% 27.37/3.98  --inst_solver_calls_frac                1.
% 27.37/3.98  --inst_passive_queue_type               priority_queues
% 27.37/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.37/3.98  --inst_passive_queues_freq              [25;2]
% 27.37/3.98  --inst_dismatching                      true
% 27.37/3.98  --inst_eager_unprocessed_to_passive     true
% 27.37/3.98  --inst_prop_sim_given                   true
% 27.37/3.98  --inst_prop_sim_new                     false
% 27.37/3.98  --inst_subs_new                         false
% 27.37/3.98  --inst_eq_res_simp                      false
% 27.37/3.98  --inst_subs_given                       false
% 27.37/3.98  --inst_orphan_elimination               true
% 27.37/3.98  --inst_learning_loop_flag               true
% 27.37/3.98  --inst_learning_start                   3000
% 27.37/3.98  --inst_learning_factor                  2
% 27.37/3.98  --inst_start_prop_sim_after_learn       3
% 27.37/3.98  --inst_sel_renew                        solver
% 27.37/3.98  --inst_lit_activity_flag                true
% 27.37/3.98  --inst_restr_to_given                   false
% 27.37/3.98  --inst_activity_threshold               500
% 27.37/3.98  --inst_out_proof                        true
% 27.37/3.98  
% 27.37/3.98  ------ Resolution Options
% 27.37/3.98  
% 27.37/3.98  --resolution_flag                       true
% 27.37/3.98  --res_lit_sel                           adaptive
% 27.37/3.98  --res_lit_sel_side                      none
% 27.37/3.98  --res_ordering                          kbo
% 27.37/3.98  --res_to_prop_solver                    active
% 27.37/3.98  --res_prop_simpl_new                    false
% 27.37/3.98  --res_prop_simpl_given                  true
% 27.37/3.98  --res_passive_queue_type                priority_queues
% 27.37/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.37/3.98  --res_passive_queues_freq               [15;5]
% 27.37/3.98  --res_forward_subs                      full
% 27.37/3.98  --res_backward_subs                     full
% 27.37/3.98  --res_forward_subs_resolution           true
% 27.37/3.98  --res_backward_subs_resolution          true
% 27.37/3.98  --res_orphan_elimination                true
% 27.37/3.98  --res_time_limit                        2.
% 27.37/3.98  --res_out_proof                         true
% 27.37/3.98  
% 27.37/3.98  ------ Superposition Options
% 27.37/3.98  
% 27.37/3.98  --superposition_flag                    true
% 27.37/3.98  --sup_passive_queue_type                priority_queues
% 27.37/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.37/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.37/3.98  --demod_completeness_check              fast
% 27.37/3.98  --demod_use_ground                      true
% 27.37/3.98  --sup_to_prop_solver                    passive
% 27.37/3.98  --sup_prop_simpl_new                    true
% 27.37/3.98  --sup_prop_simpl_given                  true
% 27.37/3.98  --sup_fun_splitting                     false
% 27.37/3.98  --sup_smt_interval                      50000
% 27.37/3.98  
% 27.37/3.98  ------ Superposition Simplification Setup
% 27.37/3.98  
% 27.37/3.98  --sup_indices_passive                   []
% 27.37/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.37/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/3.98  --sup_full_bw                           [BwDemod]
% 27.37/3.98  --sup_immed_triv                        [TrivRules]
% 27.37/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.37/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/3.98  --sup_immed_bw_main                     []
% 27.37/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.37/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/3.98  
% 27.37/3.98  ------ Combination Options
% 27.37/3.98  
% 27.37/3.98  --comb_res_mult                         3
% 27.37/3.98  --comb_sup_mult                         2
% 27.37/3.98  --comb_inst_mult                        10
% 27.37/3.98  
% 27.37/3.98  ------ Debug Options
% 27.37/3.98  
% 27.37/3.98  --dbg_backtrace                         false
% 27.37/3.98  --dbg_dump_prop_clauses                 false
% 27.37/3.98  --dbg_dump_prop_clauses_file            -
% 27.37/3.98  --dbg_out_stat                          false
% 27.37/3.98  ------ Parsing...
% 27.37/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.37/3.98  
% 27.37/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.37/3.98  
% 27.37/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.37/3.98  
% 27.37/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.37/3.98  ------ Proving...
% 27.37/3.98  ------ Problem Properties 
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  clauses                                 13
% 27.37/3.98  conjectures                             3
% 27.37/3.98  EPR                                     2
% 27.37/3.98  Horn                                    13
% 27.37/3.98  unary                                   4
% 27.37/3.98  binary                                  6
% 27.37/3.98  lits                                    26
% 27.37/3.98  lits eq                                 2
% 27.37/3.98  fd_pure                                 0
% 27.37/3.98  fd_pseudo                               0
% 27.37/3.98  fd_cond                                 0
% 27.37/3.98  fd_pseudo_cond                          1
% 27.37/3.98  AC symbols                              0
% 27.37/3.98  
% 27.37/3.98  ------ Schedule dynamic 5 is on 
% 27.37/3.98  
% 27.37/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  ------ 
% 27.37/3.98  Current options:
% 27.37/3.98  ------ 
% 27.37/3.98  
% 27.37/3.98  ------ Input Options
% 27.37/3.98  
% 27.37/3.98  --out_options                           all
% 27.37/3.98  --tptp_safe_out                         true
% 27.37/3.98  --problem_path                          ""
% 27.37/3.98  --include_path                          ""
% 27.37/3.98  --clausifier                            res/vclausify_rel
% 27.37/3.98  --clausifier_options                    --mode clausify
% 27.37/3.98  --stdin                                 false
% 27.37/3.98  --stats_out                             all
% 27.37/3.98  
% 27.37/3.98  ------ General Options
% 27.37/3.98  
% 27.37/3.98  --fof                                   false
% 27.37/3.98  --time_out_real                         305.
% 27.37/3.98  --time_out_virtual                      -1.
% 27.37/3.98  --symbol_type_check                     false
% 27.37/3.98  --clausify_out                          false
% 27.37/3.98  --sig_cnt_out                           false
% 27.37/3.98  --trig_cnt_out                          false
% 27.37/3.98  --trig_cnt_out_tolerance                1.
% 27.37/3.98  --trig_cnt_out_sk_spl                   false
% 27.37/3.98  --abstr_cl_out                          false
% 27.37/3.98  
% 27.37/3.98  ------ Global Options
% 27.37/3.98  
% 27.37/3.98  --schedule                              default
% 27.37/3.98  --add_important_lit                     false
% 27.37/3.98  --prop_solver_per_cl                    1000
% 27.37/3.98  --min_unsat_core                        false
% 27.37/3.98  --soft_assumptions                      false
% 27.37/3.98  --soft_lemma_size                       3
% 27.37/3.98  --prop_impl_unit_size                   0
% 27.37/3.98  --prop_impl_unit                        []
% 27.37/3.98  --share_sel_clauses                     true
% 27.37/3.98  --reset_solvers                         false
% 27.37/3.98  --bc_imp_inh                            [conj_cone]
% 27.37/3.98  --conj_cone_tolerance                   3.
% 27.37/3.98  --extra_neg_conj                        none
% 27.37/3.98  --large_theory_mode                     true
% 27.37/3.98  --prolific_symb_bound                   200
% 27.37/3.98  --lt_threshold                          2000
% 27.37/3.98  --clause_weak_htbl                      true
% 27.37/3.98  --gc_record_bc_elim                     false
% 27.37/3.98  
% 27.37/3.98  ------ Preprocessing Options
% 27.37/3.98  
% 27.37/3.98  --preprocessing_flag                    true
% 27.37/3.98  --time_out_prep_mult                    0.1
% 27.37/3.98  --splitting_mode                        input
% 27.37/3.98  --splitting_grd                         true
% 27.37/3.98  --splitting_cvd                         false
% 27.37/3.98  --splitting_cvd_svl                     false
% 27.37/3.98  --splitting_nvd                         32
% 27.37/3.98  --sub_typing                            true
% 27.37/3.98  --prep_gs_sim                           true
% 27.37/3.98  --prep_unflatten                        true
% 27.37/3.98  --prep_res_sim                          true
% 27.37/3.98  --prep_upred                            true
% 27.37/3.98  --prep_sem_filter                       exhaustive
% 27.37/3.98  --prep_sem_filter_out                   false
% 27.37/3.98  --pred_elim                             true
% 27.37/3.98  --res_sim_input                         true
% 27.37/3.98  --eq_ax_congr_red                       true
% 27.37/3.98  --pure_diseq_elim                       true
% 27.37/3.98  --brand_transform                       false
% 27.37/3.98  --non_eq_to_eq                          false
% 27.37/3.98  --prep_def_merge                        true
% 27.37/3.98  --prep_def_merge_prop_impl              false
% 27.37/3.98  --prep_def_merge_mbd                    true
% 27.37/3.98  --prep_def_merge_tr_red                 false
% 27.37/3.98  --prep_def_merge_tr_cl                  false
% 27.37/3.98  --smt_preprocessing                     true
% 27.37/3.98  --smt_ac_axioms                         fast
% 27.37/3.98  --preprocessed_out                      false
% 27.37/3.98  --preprocessed_stats                    false
% 27.37/3.98  
% 27.37/3.98  ------ Abstraction refinement Options
% 27.37/3.98  
% 27.37/3.98  --abstr_ref                             []
% 27.37/3.98  --abstr_ref_prep                        false
% 27.37/3.98  --abstr_ref_until_sat                   false
% 27.37/3.98  --abstr_ref_sig_restrict                funpre
% 27.37/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.37/3.98  --abstr_ref_under                       []
% 27.37/3.98  
% 27.37/3.98  ------ SAT Options
% 27.37/3.98  
% 27.37/3.98  --sat_mode                              false
% 27.37/3.98  --sat_fm_restart_options                ""
% 27.37/3.98  --sat_gr_def                            false
% 27.37/3.98  --sat_epr_types                         true
% 27.37/3.98  --sat_non_cyclic_types                  false
% 27.37/3.98  --sat_finite_models                     false
% 27.37/3.98  --sat_fm_lemmas                         false
% 27.37/3.98  --sat_fm_prep                           false
% 27.37/3.98  --sat_fm_uc_incr                        true
% 27.37/3.98  --sat_out_model                         small
% 27.37/3.98  --sat_out_clauses                       false
% 27.37/3.98  
% 27.37/3.98  ------ QBF Options
% 27.37/3.98  
% 27.37/3.98  --qbf_mode                              false
% 27.37/3.98  --qbf_elim_univ                         false
% 27.37/3.98  --qbf_dom_inst                          none
% 27.37/3.98  --qbf_dom_pre_inst                      false
% 27.37/3.98  --qbf_sk_in                             false
% 27.37/3.98  --qbf_pred_elim                         true
% 27.37/3.98  --qbf_split                             512
% 27.37/3.98  
% 27.37/3.98  ------ BMC1 Options
% 27.37/3.98  
% 27.37/3.98  --bmc1_incremental                      false
% 27.37/3.98  --bmc1_axioms                           reachable_all
% 27.37/3.98  --bmc1_min_bound                        0
% 27.37/3.98  --bmc1_max_bound                        -1
% 27.37/3.98  --bmc1_max_bound_default                -1
% 27.37/3.98  --bmc1_symbol_reachability              true
% 27.37/3.98  --bmc1_property_lemmas                  false
% 27.37/3.98  --bmc1_k_induction                      false
% 27.37/3.98  --bmc1_non_equiv_states                 false
% 27.37/3.98  --bmc1_deadlock                         false
% 27.37/3.98  --bmc1_ucm                              false
% 27.37/3.98  --bmc1_add_unsat_core                   none
% 27.37/3.98  --bmc1_unsat_core_children              false
% 27.37/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.37/3.98  --bmc1_out_stat                         full
% 27.37/3.98  --bmc1_ground_init                      false
% 27.37/3.98  --bmc1_pre_inst_next_state              false
% 27.37/3.98  --bmc1_pre_inst_state                   false
% 27.37/3.98  --bmc1_pre_inst_reach_state             false
% 27.37/3.98  --bmc1_out_unsat_core                   false
% 27.37/3.98  --bmc1_aig_witness_out                  false
% 27.37/3.98  --bmc1_verbose                          false
% 27.37/3.98  --bmc1_dump_clauses_tptp                false
% 27.37/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.37/3.98  --bmc1_dump_file                        -
% 27.37/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.37/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.37/3.98  --bmc1_ucm_extend_mode                  1
% 27.37/3.98  --bmc1_ucm_init_mode                    2
% 27.37/3.98  --bmc1_ucm_cone_mode                    none
% 27.37/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.37/3.98  --bmc1_ucm_relax_model                  4
% 27.37/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.37/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.37/3.98  --bmc1_ucm_layered_model                none
% 27.37/3.98  --bmc1_ucm_max_lemma_size               10
% 27.37/3.98  
% 27.37/3.98  ------ AIG Options
% 27.37/3.98  
% 27.37/3.98  --aig_mode                              false
% 27.37/3.98  
% 27.37/3.98  ------ Instantiation Options
% 27.37/3.98  
% 27.37/3.98  --instantiation_flag                    true
% 27.37/3.98  --inst_sos_flag                         false
% 27.37/3.98  --inst_sos_phase                        true
% 27.37/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.37/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.37/3.98  --inst_lit_sel_side                     none
% 27.37/3.98  --inst_solver_per_active                1400
% 27.37/3.98  --inst_solver_calls_frac                1.
% 27.37/3.98  --inst_passive_queue_type               priority_queues
% 27.37/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.37/3.98  --inst_passive_queues_freq              [25;2]
% 27.37/3.98  --inst_dismatching                      true
% 27.37/3.98  --inst_eager_unprocessed_to_passive     true
% 27.37/3.98  --inst_prop_sim_given                   true
% 27.37/3.98  --inst_prop_sim_new                     false
% 27.37/3.98  --inst_subs_new                         false
% 27.37/3.98  --inst_eq_res_simp                      false
% 27.37/3.98  --inst_subs_given                       false
% 27.37/3.98  --inst_orphan_elimination               true
% 27.37/3.98  --inst_learning_loop_flag               true
% 27.37/3.98  --inst_learning_start                   3000
% 27.37/3.98  --inst_learning_factor                  2
% 27.37/3.98  --inst_start_prop_sim_after_learn       3
% 27.37/3.98  --inst_sel_renew                        solver
% 27.37/3.98  --inst_lit_activity_flag                true
% 27.37/3.98  --inst_restr_to_given                   false
% 27.37/3.98  --inst_activity_threshold               500
% 27.37/3.98  --inst_out_proof                        true
% 27.37/3.98  
% 27.37/3.98  ------ Resolution Options
% 27.37/3.98  
% 27.37/3.98  --resolution_flag                       false
% 27.37/3.98  --res_lit_sel                           adaptive
% 27.37/3.98  --res_lit_sel_side                      none
% 27.37/3.98  --res_ordering                          kbo
% 27.37/3.98  --res_to_prop_solver                    active
% 27.37/3.98  --res_prop_simpl_new                    false
% 27.37/3.98  --res_prop_simpl_given                  true
% 27.37/3.98  --res_passive_queue_type                priority_queues
% 27.37/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.37/3.98  --res_passive_queues_freq               [15;5]
% 27.37/3.98  --res_forward_subs                      full
% 27.37/3.98  --res_backward_subs                     full
% 27.37/3.98  --res_forward_subs_resolution           true
% 27.37/3.98  --res_backward_subs_resolution          true
% 27.37/3.98  --res_orphan_elimination                true
% 27.37/3.98  --res_time_limit                        2.
% 27.37/3.98  --res_out_proof                         true
% 27.37/3.98  
% 27.37/3.98  ------ Superposition Options
% 27.37/3.98  
% 27.37/3.98  --superposition_flag                    true
% 27.37/3.98  --sup_passive_queue_type                priority_queues
% 27.37/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.37/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.37/3.98  --demod_completeness_check              fast
% 27.37/3.98  --demod_use_ground                      true
% 27.37/3.98  --sup_to_prop_solver                    passive
% 27.37/3.98  --sup_prop_simpl_new                    true
% 27.37/3.98  --sup_prop_simpl_given                  true
% 27.37/3.98  --sup_fun_splitting                     false
% 27.37/3.98  --sup_smt_interval                      50000
% 27.37/3.98  
% 27.37/3.98  ------ Superposition Simplification Setup
% 27.37/3.98  
% 27.37/3.98  --sup_indices_passive                   []
% 27.37/3.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/3.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.37/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.37/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/3.98  --sup_full_bw                           [BwDemod]
% 27.37/3.98  --sup_immed_triv                        [TrivRules]
% 27.37/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.37/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/3.98  --sup_immed_bw_main                     []
% 27.37/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.37/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.37/3.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.37/3.98  
% 27.37/3.98  ------ Combination Options
% 27.37/3.98  
% 27.37/3.98  --comb_res_mult                         3
% 27.37/3.98  --comb_sup_mult                         2
% 27.37/3.98  --comb_inst_mult                        10
% 27.37/3.98  
% 27.37/3.98  ------ Debug Options
% 27.37/3.98  
% 27.37/3.98  --dbg_backtrace                         false
% 27.37/3.98  --dbg_dump_prop_clauses                 false
% 27.37/3.98  --dbg_dump_prop_clauses_file            -
% 27.37/3.98  --dbg_out_stat                          false
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  ------ Proving...
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  % SZS status Theorem for theBenchmark.p
% 27.37/3.98  
% 27.37/3.98   Resolution empty clause
% 27.37/3.98  
% 27.37/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.37/3.98  
% 27.37/3.98  fof(f9,axiom,(
% 27.37/3.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f19,plain,(
% 27.37/3.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.37/3.98    inference(ennf_transformation,[],[f9])).
% 27.37/3.98  
% 27.37/3.98  fof(f20,plain,(
% 27.37/3.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.37/3.98    inference(flattening,[],[f19])).
% 27.37/3.98  
% 27.37/3.98  fof(f40,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.37/3.98    inference(cnf_transformation,[],[f20])).
% 27.37/3.98  
% 27.37/3.98  fof(f10,conjecture,(
% 27.37/3.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f11,negated_conjecture,(
% 27.37/3.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 27.37/3.98    inference(negated_conjecture,[],[f10])).
% 27.37/3.98  
% 27.37/3.98  fof(f21,plain,(
% 27.37/3.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.37/3.98    inference(ennf_transformation,[],[f11])).
% 27.37/3.98  
% 27.37/3.98  fof(f27,plain,(
% 27.37/3.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.37/3.98    introduced(choice_axiom,[])).
% 27.37/3.98  
% 27.37/3.98  fof(f26,plain,(
% 27.37/3.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.37/3.98    introduced(choice_axiom,[])).
% 27.37/3.98  
% 27.37/3.98  fof(f25,plain,(
% 27.37/3.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 27.37/3.98    introduced(choice_axiom,[])).
% 27.37/3.98  
% 27.37/3.98  fof(f28,plain,(
% 27.37/3.98    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 27.37/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27,f26,f25])).
% 27.37/3.98  
% 27.37/3.98  fof(f41,plain,(
% 27.37/3.98    l1_pre_topc(sK0)),
% 27.37/3.98    inference(cnf_transformation,[],[f28])).
% 27.37/3.98  
% 27.37/3.98  fof(f3,axiom,(
% 27.37/3.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f13,plain,(
% 27.37/3.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 27.37/3.98    inference(ennf_transformation,[],[f3])).
% 27.37/3.98  
% 27.37/3.98  fof(f14,plain,(
% 27.37/3.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 27.37/3.98    inference(flattening,[],[f13])).
% 27.37/3.98  
% 27.37/3.98  fof(f33,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 27.37/3.98    inference(cnf_transformation,[],[f14])).
% 27.37/3.98  
% 27.37/3.98  fof(f6,axiom,(
% 27.37/3.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f36,plain,(
% 27.37/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.37/3.98    inference(cnf_transformation,[],[f6])).
% 27.37/3.98  
% 27.37/3.98  fof(f46,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 27.37/3.98    inference(definition_unfolding,[],[f33,f36])).
% 27.37/3.98  
% 27.37/3.98  fof(f43,plain,(
% 27.37/3.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.37/3.98    inference(cnf_transformation,[],[f28])).
% 27.37/3.98  
% 27.37/3.98  fof(f8,axiom,(
% 27.37/3.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f17,plain,(
% 27.37/3.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.37/3.98    inference(ennf_transformation,[],[f8])).
% 27.37/3.98  
% 27.37/3.98  fof(f18,plain,(
% 27.37/3.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.37/3.98    inference(flattening,[],[f17])).
% 27.37/3.98  
% 27.37/3.98  fof(f39,plain,(
% 27.37/3.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.37/3.98    inference(cnf_transformation,[],[f18])).
% 27.37/3.98  
% 27.37/3.98  fof(f7,axiom,(
% 27.37/3.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f24,plain,(
% 27.37/3.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.37/3.98    inference(nnf_transformation,[],[f7])).
% 27.37/3.98  
% 27.37/3.98  fof(f37,plain,(
% 27.37/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.37/3.98    inference(cnf_transformation,[],[f24])).
% 27.37/3.98  
% 27.37/3.98  fof(f5,axiom,(
% 27.37/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f16,plain,(
% 27.37/3.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 27.37/3.98    inference(ennf_transformation,[],[f5])).
% 27.37/3.98  
% 27.37/3.98  fof(f35,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.37/3.98    inference(cnf_transformation,[],[f16])).
% 27.37/3.98  
% 27.37/3.98  fof(f47,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.37/3.98    inference(definition_unfolding,[],[f35,f36])).
% 27.37/3.98  
% 27.37/3.98  fof(f38,plain,(
% 27.37/3.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.37/3.98    inference(cnf_transformation,[],[f24])).
% 27.37/3.98  
% 27.37/3.98  fof(f44,plain,(
% 27.37/3.98    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 27.37/3.98    inference(cnf_transformation,[],[f28])).
% 27.37/3.98  
% 27.37/3.98  fof(f42,plain,(
% 27.37/3.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.37/3.98    inference(cnf_transformation,[],[f28])).
% 27.37/3.98  
% 27.37/3.98  fof(f1,axiom,(
% 27.37/3.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f22,plain,(
% 27.37/3.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.37/3.98    inference(nnf_transformation,[],[f1])).
% 27.37/3.98  
% 27.37/3.98  fof(f23,plain,(
% 27.37/3.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.37/3.98    inference(flattening,[],[f22])).
% 27.37/3.98  
% 27.37/3.98  fof(f29,plain,(
% 27.37/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.37/3.98    inference(cnf_transformation,[],[f23])).
% 27.37/3.98  
% 27.37/3.98  fof(f49,plain,(
% 27.37/3.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.37/3.98    inference(equality_resolution,[],[f29])).
% 27.37/3.98  
% 27.37/3.98  fof(f2,axiom,(
% 27.37/3.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f12,plain,(
% 27.37/3.98    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 27.37/3.98    inference(ennf_transformation,[],[f2])).
% 27.37/3.98  
% 27.37/3.98  fof(f32,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 27.37/3.98    inference(cnf_transformation,[],[f12])).
% 27.37/3.98  
% 27.37/3.98  fof(f45,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 27.37/3.98    inference(definition_unfolding,[],[f32,f36])).
% 27.37/3.98  
% 27.37/3.98  fof(f4,axiom,(
% 27.37/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 27.37/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.37/3.98  
% 27.37/3.98  fof(f15,plain,(
% 27.37/3.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 27.37/3.98    inference(ennf_transformation,[],[f4])).
% 27.37/3.98  
% 27.37/3.98  fof(f34,plain,(
% 27.37/3.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.37/3.98    inference(cnf_transformation,[],[f15])).
% 27.37/3.98  
% 27.37/3.98  cnf(c_10,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | ~ r1_tarski(X0,X2)
% 27.37/3.98      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 27.37/3.98      | ~ l1_pre_topc(X1) ),
% 27.37/3.98      inference(cnf_transformation,[],[f40]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_14,negated_conjecture,
% 27.37/3.98      ( l1_pre_topc(sK0) ),
% 27.37/3.98      inference(cnf_transformation,[],[f41]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_200,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | ~ r1_tarski(X0,X2)
% 27.37/3.98      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 27.37/3.98      | sK0 != X1 ),
% 27.37/3.98      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_201,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ r1_tarski(X1,X0)
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 27.37/3.98      inference(unflattening,[status(thm)],[c_200]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_683,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | r1_tarski(X1,X0) != iProver_top
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_4,plain,
% 27.37/3.98      ( ~ r1_tarski(X0,X1)
% 27.37/3.98      | ~ r1_tarski(X0,X2)
% 27.37/3.98      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 27.37/3.98      inference(cnf_transformation,[],[f46]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_691,plain,
% 27.37/3.98      ( r1_tarski(X0,X1) != iProver_top
% 27.37/3.98      | r1_tarski(X0,X2) != iProver_top
% 27.37/3.98      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_12,negated_conjecture,
% 27.37/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.37/3.98      inference(cnf_transformation,[],[f43]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_687,plain,
% 27.37/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_9,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | ~ l1_pre_topc(X1) ),
% 27.37/3.98      inference(cnf_transformation,[],[f39]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_218,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.37/3.98      | sK0 != X1 ),
% 27.37/3.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_219,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.37/3.98      inference(unflattening,[status(thm)],[c_218]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_682,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_8,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.37/3.98      inference(cnf_transformation,[],[f37]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_689,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.37/3.98      | r1_tarski(X0,X1) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1109,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_682,c_689]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_6,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.37/3.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 27.37/3.98      inference(cnf_transformation,[],[f47]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_7,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.37/3.98      inference(cnf_transformation,[],[f38]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_116,plain,
% 27.37/3.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.37/3.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_117,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.37/3.98      inference(renaming,[status(thm)],[c_116]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_140,plain,
% 27.37/3.98      ( ~ r1_tarski(X0,X1)
% 27.37/3.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 27.37/3.98      inference(bin_hyper_res,[status(thm)],[c_6,c_117]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_684,plain,
% 27.37/3.98      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 27.37/3.98      | r1_tarski(X2,X0) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_2024,plain,
% 27.37/3.98      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
% 27.37/3.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_1109,c_684]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_8505,plain,
% 27.37/3.98      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_687,c_2024]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1107,plain,
% 27.37/3.98      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_687,c_689]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1234,plain,
% 27.37/3.98      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_1107,c_684]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_11,negated_conjecture,
% 27.37/3.98      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 27.37/3.98      inference(cnf_transformation,[],[f44]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_688,plain,
% 27.37/3.98      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1679,plain,
% 27.37/3.98      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 27.37/3.98      inference(demodulation,[status(thm)],[c_1234,c_688]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_8536,plain,
% 27.37/3.98      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
% 27.37/3.98      inference(demodulation,[status(thm)],[c_8505,c_1679]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_9345,plain,
% 27.37/3.98      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_691,c_8536]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_20111,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
% 27.37/3.98      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_683,c_9345]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_13,negated_conjecture,
% 27.37/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.37/3.98      inference(cnf_transformation,[],[f42]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_16,plain,
% 27.37/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_17,plain,
% 27.37/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f49]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_935,plain,
% 27.37/3.98      ( r1_tarski(sK1,sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_2]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_938,plain,
% 27.37/3.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_686,plain,
% 27.37/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1108,plain,
% 27.37/3.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_686,c_689]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_791,plain,
% 27.37/3.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_7]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_992,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_791]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_11076,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_992]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_45667,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_11076]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_45701,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 27.37/3.98      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_45667]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_786,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ r1_tarski(X0,sK1)
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_201]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_940,plain,
% 27.37/3.98      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0,X1))),k2_pre_topc(sK0,sK1))
% 27.37/3.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_786]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_2845,plain,
% 27.37/3.98      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,X0))),k2_pre_topc(sK0,sK1))
% 27.37/3.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_940]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_45806,plain,
% 27.37/3.98      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))
% 27.37/3.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_2845]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_45811,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.37/3.98      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) = iProver_top
% 27.37/3.98      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_45806]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_3,plain,
% 27.37/3.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 27.37/3.98      inference(cnf_transformation,[],[f45]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_993,plain,
% 27.37/3.98      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 27.37/3.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_3]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_3008,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
% 27.37/3.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_993]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_54218,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 27.37/3.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_3008]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_54219,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) = iProver_top
% 27.37/3.98      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_54218]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_941,plain,
% 27.37/3.98      ( ~ r1_tarski(X0,sK1) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_3]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1415,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) | ~ r1_tarski(sK1,sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_941]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_54341,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | ~ r1_tarski(sK1,sK1) ),
% 27.37/3.98      inference(instantiation,[status(thm)],[c_1415]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_54342,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top
% 27.37/3.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_54341]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_105547,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 27.37/3.98      inference(global_propositional_subsumption,
% 27.37/3.98                [status(thm)],
% 27.37/3.98                [c_20111,c_16,c_17,c_938,c_1108,c_45701,c_45811,c_54219,
% 27.37/3.98                 c_54342]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_693,plain,
% 27.37/3.98      ( r1_tarski(X0,X0) = iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_1233,plain,
% 27.37/3.98      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_693,c_684]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_5,plain,
% 27.37/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.37/3.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 27.37/3.98      inference(cnf_transformation,[],[f34]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_139,plain,
% 27.37/3.98      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 27.37/3.98      | ~ r1_tarski(X2,X0) ),
% 27.37/3.98      inference(bin_hyper_res,[status(thm)],[c_5,c_117]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_685,plain,
% 27.37/3.98      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 27.37/3.98      | r1_tarski(X2,X0) != iProver_top ),
% 27.37/3.98      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_2398,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
% 27.37/3.98      | r1_tarski(X1,X1) != iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_1233,c_685]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_16382,plain,
% 27.37/3.98      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 27.37/3.98      inference(forward_subsumption_resolution,[status(thm)],[c_2398,c_693]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_16400,plain,
% 27.37/3.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 27.37/3.98      inference(superposition,[status(thm)],[c_16382,c_689]) ).
% 27.37/3.98  
% 27.37/3.98  cnf(c_105552,plain,
% 27.37/3.98      ( $false ),
% 27.37/3.98      inference(forward_subsumption_resolution,
% 27.37/3.98                [status(thm)],
% 27.37/3.98                [c_105547,c_16400]) ).
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.37/3.98  
% 27.37/3.98  ------                               Statistics
% 27.37/3.98  
% 27.37/3.98  ------ General
% 27.37/3.98  
% 27.37/3.98  abstr_ref_over_cycles:                  0
% 27.37/3.98  abstr_ref_under_cycles:                 0
% 27.37/3.98  gc_basic_clause_elim:                   0
% 27.37/3.98  forced_gc_time:                         0
% 27.37/3.98  parsing_time:                           0.009
% 27.37/3.98  unif_index_cands_time:                  0.
% 27.37/3.98  unif_index_add_time:                    0.
% 27.37/3.98  orderings_time:                         0.
% 27.37/3.98  out_proof_time:                         0.016
% 27.37/3.98  total_time:                             3.222
% 27.37/3.98  num_of_symbols:                         43
% 27.37/3.98  num_of_terms:                           127060
% 27.37/3.98  
% 27.37/3.98  ------ Preprocessing
% 27.37/3.98  
% 27.37/3.98  num_of_splits:                          0
% 27.37/3.98  num_of_split_atoms:                     0
% 27.37/3.98  num_of_reused_defs:                     0
% 27.37/3.98  num_eq_ax_congr_red:                    6
% 27.37/3.98  num_of_sem_filtered_clauses:            1
% 27.37/3.98  num_of_subtypes:                        0
% 27.37/3.98  monotx_restored_types:                  0
% 27.37/3.98  sat_num_of_epr_types:                   0
% 27.37/3.98  sat_num_of_non_cyclic_types:            0
% 27.37/3.98  sat_guarded_non_collapsed_types:        0
% 27.37/3.98  num_pure_diseq_elim:                    0
% 27.37/3.98  simp_replaced_by:                       0
% 27.37/3.98  res_preprocessed:                       72
% 27.37/3.98  prep_upred:                             0
% 27.37/3.98  prep_unflattend:                        2
% 27.37/3.98  smt_new_axioms:                         0
% 27.37/3.98  pred_elim_cands:                        2
% 27.37/3.98  pred_elim:                              1
% 27.37/3.98  pred_elim_cl:                           1
% 27.37/3.98  pred_elim_cycles:                       3
% 27.37/3.98  merged_defs:                            8
% 27.37/3.98  merged_defs_ncl:                        0
% 27.37/3.98  bin_hyper_res:                          10
% 27.37/3.98  prep_cycles:                            4
% 27.37/3.98  pred_elim_time:                         0.001
% 27.37/3.98  splitting_time:                         0.
% 27.37/3.98  sem_filter_time:                        0.
% 27.37/3.98  monotx_time:                            0.
% 27.37/3.98  subtype_inf_time:                       0.
% 27.37/3.98  
% 27.37/3.98  ------ Problem properties
% 27.37/3.98  
% 27.37/3.98  clauses:                                13
% 27.37/3.98  conjectures:                            3
% 27.37/3.98  epr:                                    2
% 27.37/3.98  horn:                                   13
% 27.37/3.98  ground:                                 3
% 27.37/3.98  unary:                                  4
% 27.37/3.98  binary:                                 6
% 27.37/3.98  lits:                                   26
% 27.37/3.98  lits_eq:                                2
% 27.37/3.98  fd_pure:                                0
% 27.37/3.98  fd_pseudo:                              0
% 27.37/3.98  fd_cond:                                0
% 27.37/3.98  fd_pseudo_cond:                         1
% 27.37/3.98  ac_symbols:                             0
% 27.37/3.98  
% 27.37/3.98  ------ Propositional Solver
% 27.37/3.98  
% 27.37/3.98  prop_solver_calls:                      44
% 27.37/3.98  prop_fast_solver_calls:                 1937
% 27.37/3.98  smt_solver_calls:                       0
% 27.37/3.98  smt_fast_solver_calls:                  0
% 27.37/3.98  prop_num_of_clauses:                    40540
% 27.37/3.98  prop_preprocess_simplified:             41943
% 27.37/3.98  prop_fo_subsumed:                       62
% 27.37/3.98  prop_solver_time:                       0.
% 27.37/3.98  smt_solver_time:                        0.
% 27.37/3.98  smt_fast_solver_time:                   0.
% 27.37/3.98  prop_fast_solver_time:                  0.
% 27.37/3.98  prop_unsat_core_time:                   0.
% 27.37/3.98  
% 27.37/3.98  ------ QBF
% 27.37/3.98  
% 27.37/3.98  qbf_q_res:                              0
% 27.37/3.98  qbf_num_tautologies:                    0
% 27.37/3.98  qbf_prep_cycles:                        0
% 27.37/3.98  
% 27.37/3.98  ------ BMC1
% 27.37/3.98  
% 27.37/3.98  bmc1_current_bound:                     -1
% 27.37/3.98  bmc1_last_solved_bound:                 -1
% 27.37/3.98  bmc1_unsat_core_size:                   -1
% 27.37/3.98  bmc1_unsat_core_parents_size:           -1
% 27.37/3.98  bmc1_merge_next_fun:                    0
% 27.37/3.98  bmc1_unsat_core_clauses_time:           0.
% 27.37/3.98  
% 27.37/3.98  ------ Instantiation
% 27.37/3.98  
% 27.37/3.98  inst_num_of_clauses:                    767
% 27.37/3.98  inst_num_in_passive:                    47
% 27.37/3.98  inst_num_in_active:                     3153
% 27.37/3.98  inst_num_in_unprocessed:                373
% 27.37/3.98  inst_num_of_loops:                      3349
% 27.37/3.98  inst_num_of_learning_restarts:          1
% 27.37/3.98  inst_num_moves_active_passive:          192
% 27.37/3.98  inst_lit_activity:                      0
% 27.37/3.98  inst_lit_activity_moves:                2
% 27.37/3.98  inst_num_tautologies:                   0
% 27.37/3.98  inst_num_prop_implied:                  0
% 27.37/3.98  inst_num_existing_simplified:           0
% 27.37/3.98  inst_num_eq_res_simplified:             0
% 27.37/3.98  inst_num_child_elim:                    0
% 27.37/3.98  inst_num_of_dismatching_blockings:      5881
% 27.37/3.98  inst_num_of_non_proper_insts:           11062
% 27.37/3.98  inst_num_of_duplicates:                 0
% 27.37/3.98  inst_inst_num_from_inst_to_res:         0
% 27.37/3.98  inst_dismatching_checking_time:         0.
% 27.37/3.98  
% 27.37/3.98  ------ Resolution
% 27.37/3.98  
% 27.37/3.98  res_num_of_clauses:                     22
% 27.37/3.98  res_num_in_passive:                     22
% 27.37/3.98  res_num_in_active:                      0
% 27.37/3.98  res_num_of_loops:                       76
% 27.37/3.98  res_forward_subset_subsumed:            509
% 27.37/3.98  res_backward_subset_subsumed:           4
% 27.37/3.98  res_forward_subsumed:                   0
% 27.37/3.98  res_backward_subsumed:                  0
% 27.37/3.98  res_forward_subsumption_resolution:     0
% 27.37/3.98  res_backward_subsumption_resolution:    0
% 27.37/3.98  res_clause_to_clause_subsumption:       58933
% 27.37/3.98  res_orphan_elimination:                 0
% 27.37/3.98  res_tautology_del:                      487
% 27.37/3.98  res_num_eq_res_simplified:              0
% 27.37/3.98  res_num_sel_changes:                    0
% 27.37/3.98  res_moves_from_active_to_pass:          0
% 27.37/3.98  
% 27.37/3.98  ------ Superposition
% 27.37/3.98  
% 27.37/3.98  sup_time_total:                         0.
% 27.37/3.98  sup_time_generating:                    0.
% 27.37/3.98  sup_time_sim_full:                      0.
% 27.37/3.98  sup_time_sim_immed:                     0.
% 27.37/3.98  
% 27.37/3.98  sup_num_of_clauses:                     5106
% 27.37/3.98  sup_num_in_active:                      660
% 27.37/3.98  sup_num_in_passive:                     4446
% 27.37/3.98  sup_num_of_loops:                       669
% 27.37/3.98  sup_fw_superposition:                   5446
% 27.37/3.98  sup_bw_superposition:                   3315
% 27.37/3.98  sup_immediate_simplified:               4608
% 27.37/3.98  sup_given_eliminated:                   0
% 27.37/3.98  comparisons_done:                       0
% 27.37/3.98  comparisons_avoided:                    0
% 27.37/3.98  
% 27.37/3.98  ------ Simplifications
% 27.37/3.98  
% 27.37/3.98  
% 27.37/3.98  sim_fw_subset_subsumed:                 217
% 27.37/3.98  sim_bw_subset_subsumed:                 58
% 27.37/3.98  sim_fw_subsumed:                        1296
% 27.37/3.98  sim_bw_subsumed:                        23
% 27.37/3.98  sim_fw_subsumption_res:                 12
% 27.37/3.98  sim_bw_subsumption_res:                 0
% 27.37/3.98  sim_tautology_del:                      89
% 27.37/3.98  sim_eq_tautology_del:                   412
% 27.37/3.98  sim_eq_res_simp:                        0
% 27.37/3.98  sim_fw_demodulated:                     1711
% 27.37/3.98  sim_bw_demodulated:                     49
% 27.37/3.98  sim_light_normalised:                   2011
% 27.37/3.98  sim_joinable_taut:                      0
% 27.37/3.98  sim_joinable_simp:                      0
% 27.37/3.98  sim_ac_normalised:                      0
% 27.37/3.98  sim_smt_subsumption:                    0
% 27.37/3.98  
%------------------------------------------------------------------------------
