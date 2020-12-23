%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:35 EST 2020

% Result     : Theorem 39.40s
% Output     : CNFRefutation 39.40s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 226 expanded)
%              Number of clauses        :   58 (  82 expanded)
%              Number of leaves         :   14 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  231 ( 638 expanded)
%              Number of equality atoms :   74 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
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
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f42,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_650,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_651,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1180,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_650,c_651])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_652,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2045,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_652])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_648,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_649,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_645,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_647])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_105,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_105])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_106])).

cnf(c_643,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_1926,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_643])).

cnf(c_7417,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_645,c_1926])).

cnf(c_1283,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_647])).

cnf(c_1422,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1283,c_643])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_646,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1648,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1422,c_646])).

cnf(c_7877,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7417,c_1648])).

cnf(c_7991,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_7877])).

cnf(c_163958,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_7991])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_164576,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_163958,c_16])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1037,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_650])).

cnf(c_164583,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_164576,c_1037])).

cnf(c_164585,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_642,c_164583])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_907,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2734,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_2739,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2734])).

cnf(c_164689,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_164585,c_15,c_2739])).

cnf(c_164694,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_164689])).

cnf(c_168826,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_164694])).

cnf(c_751,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_752,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_168826,c_752,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:55:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.40/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.40/5.49  
% 39.40/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.40/5.49  
% 39.40/5.49  ------  iProver source info
% 39.40/5.49  
% 39.40/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.40/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.40/5.49  git: non_committed_changes: false
% 39.40/5.49  git: last_make_outside_of_git: false
% 39.40/5.49  
% 39.40/5.49  ------ 
% 39.40/5.49  
% 39.40/5.49  ------ Input Options
% 39.40/5.49  
% 39.40/5.49  --out_options                           all
% 39.40/5.49  --tptp_safe_out                         true
% 39.40/5.49  --problem_path                          ""
% 39.40/5.49  --include_path                          ""
% 39.40/5.49  --clausifier                            res/vclausify_rel
% 39.40/5.49  --clausifier_options                    --mode clausify
% 39.40/5.49  --stdin                                 false
% 39.40/5.49  --stats_out                             all
% 39.40/5.49  
% 39.40/5.49  ------ General Options
% 39.40/5.49  
% 39.40/5.49  --fof                                   false
% 39.40/5.49  --time_out_real                         305.
% 39.40/5.49  --time_out_virtual                      -1.
% 39.40/5.49  --symbol_type_check                     false
% 39.40/5.49  --clausify_out                          false
% 39.40/5.49  --sig_cnt_out                           false
% 39.40/5.49  --trig_cnt_out                          false
% 39.40/5.49  --trig_cnt_out_tolerance                1.
% 39.40/5.49  --trig_cnt_out_sk_spl                   false
% 39.40/5.49  --abstr_cl_out                          false
% 39.40/5.49  
% 39.40/5.49  ------ Global Options
% 39.40/5.49  
% 39.40/5.49  --schedule                              default
% 39.40/5.49  --add_important_lit                     false
% 39.40/5.49  --prop_solver_per_cl                    1000
% 39.40/5.49  --min_unsat_core                        false
% 39.40/5.49  --soft_assumptions                      false
% 39.40/5.49  --soft_lemma_size                       3
% 39.40/5.49  --prop_impl_unit_size                   0
% 39.40/5.49  --prop_impl_unit                        []
% 39.40/5.49  --share_sel_clauses                     true
% 39.40/5.49  --reset_solvers                         false
% 39.40/5.49  --bc_imp_inh                            [conj_cone]
% 39.40/5.49  --conj_cone_tolerance                   3.
% 39.40/5.49  --extra_neg_conj                        none
% 39.40/5.49  --large_theory_mode                     true
% 39.40/5.49  --prolific_symb_bound                   200
% 39.40/5.49  --lt_threshold                          2000
% 39.40/5.49  --clause_weak_htbl                      true
% 39.40/5.49  --gc_record_bc_elim                     false
% 39.40/5.49  
% 39.40/5.49  ------ Preprocessing Options
% 39.40/5.49  
% 39.40/5.49  --preprocessing_flag                    true
% 39.40/5.49  --time_out_prep_mult                    0.1
% 39.40/5.49  --splitting_mode                        input
% 39.40/5.49  --splitting_grd                         true
% 39.40/5.49  --splitting_cvd                         false
% 39.40/5.49  --splitting_cvd_svl                     false
% 39.40/5.49  --splitting_nvd                         32
% 39.40/5.49  --sub_typing                            true
% 39.40/5.49  --prep_gs_sim                           true
% 39.40/5.49  --prep_unflatten                        true
% 39.40/5.49  --prep_res_sim                          true
% 39.40/5.49  --prep_upred                            true
% 39.40/5.49  --prep_sem_filter                       exhaustive
% 39.40/5.49  --prep_sem_filter_out                   false
% 39.40/5.49  --pred_elim                             true
% 39.40/5.49  --res_sim_input                         true
% 39.40/5.49  --eq_ax_congr_red                       true
% 39.40/5.49  --pure_diseq_elim                       true
% 39.40/5.49  --brand_transform                       false
% 39.40/5.49  --non_eq_to_eq                          false
% 39.40/5.49  --prep_def_merge                        true
% 39.40/5.49  --prep_def_merge_prop_impl              false
% 39.40/5.49  --prep_def_merge_mbd                    true
% 39.40/5.49  --prep_def_merge_tr_red                 false
% 39.40/5.49  --prep_def_merge_tr_cl                  false
% 39.40/5.49  --smt_preprocessing                     true
% 39.40/5.49  --smt_ac_axioms                         fast
% 39.40/5.49  --preprocessed_out                      false
% 39.40/5.49  --preprocessed_stats                    false
% 39.40/5.49  
% 39.40/5.49  ------ Abstraction refinement Options
% 39.40/5.49  
% 39.40/5.49  --abstr_ref                             []
% 39.40/5.49  --abstr_ref_prep                        false
% 39.40/5.49  --abstr_ref_until_sat                   false
% 39.40/5.49  --abstr_ref_sig_restrict                funpre
% 39.40/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.40/5.49  --abstr_ref_under                       []
% 39.40/5.49  
% 39.40/5.49  ------ SAT Options
% 39.40/5.49  
% 39.40/5.49  --sat_mode                              false
% 39.40/5.49  --sat_fm_restart_options                ""
% 39.40/5.49  --sat_gr_def                            false
% 39.40/5.49  --sat_epr_types                         true
% 39.40/5.49  --sat_non_cyclic_types                  false
% 39.40/5.49  --sat_finite_models                     false
% 39.40/5.49  --sat_fm_lemmas                         false
% 39.40/5.49  --sat_fm_prep                           false
% 39.40/5.49  --sat_fm_uc_incr                        true
% 39.40/5.49  --sat_out_model                         small
% 39.40/5.49  --sat_out_clauses                       false
% 39.40/5.49  
% 39.40/5.49  ------ QBF Options
% 39.40/5.49  
% 39.40/5.49  --qbf_mode                              false
% 39.40/5.49  --qbf_elim_univ                         false
% 39.40/5.49  --qbf_dom_inst                          none
% 39.40/5.49  --qbf_dom_pre_inst                      false
% 39.40/5.49  --qbf_sk_in                             false
% 39.40/5.49  --qbf_pred_elim                         true
% 39.40/5.49  --qbf_split                             512
% 39.40/5.49  
% 39.40/5.49  ------ BMC1 Options
% 39.40/5.49  
% 39.40/5.49  --bmc1_incremental                      false
% 39.40/5.49  --bmc1_axioms                           reachable_all
% 39.40/5.49  --bmc1_min_bound                        0
% 39.40/5.49  --bmc1_max_bound                        -1
% 39.40/5.49  --bmc1_max_bound_default                -1
% 39.40/5.49  --bmc1_symbol_reachability              true
% 39.40/5.49  --bmc1_property_lemmas                  false
% 39.40/5.49  --bmc1_k_induction                      false
% 39.40/5.49  --bmc1_non_equiv_states                 false
% 39.40/5.49  --bmc1_deadlock                         false
% 39.40/5.49  --bmc1_ucm                              false
% 39.40/5.49  --bmc1_add_unsat_core                   none
% 39.40/5.49  --bmc1_unsat_core_children              false
% 39.40/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.40/5.49  --bmc1_out_stat                         full
% 39.40/5.49  --bmc1_ground_init                      false
% 39.40/5.49  --bmc1_pre_inst_next_state              false
% 39.40/5.49  --bmc1_pre_inst_state                   false
% 39.40/5.49  --bmc1_pre_inst_reach_state             false
% 39.40/5.49  --bmc1_out_unsat_core                   false
% 39.40/5.49  --bmc1_aig_witness_out                  false
% 39.40/5.49  --bmc1_verbose                          false
% 39.40/5.49  --bmc1_dump_clauses_tptp                false
% 39.40/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.40/5.49  --bmc1_dump_file                        -
% 39.40/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.40/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.40/5.49  --bmc1_ucm_extend_mode                  1
% 39.40/5.49  --bmc1_ucm_init_mode                    2
% 39.40/5.49  --bmc1_ucm_cone_mode                    none
% 39.40/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.40/5.49  --bmc1_ucm_relax_model                  4
% 39.40/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.40/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.40/5.49  --bmc1_ucm_layered_model                none
% 39.40/5.49  --bmc1_ucm_max_lemma_size               10
% 39.40/5.49  
% 39.40/5.49  ------ AIG Options
% 39.40/5.49  
% 39.40/5.49  --aig_mode                              false
% 39.40/5.49  
% 39.40/5.49  ------ Instantiation Options
% 39.40/5.49  
% 39.40/5.49  --instantiation_flag                    true
% 39.40/5.49  --inst_sos_flag                         false
% 39.40/5.49  --inst_sos_phase                        true
% 39.40/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.40/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.40/5.49  --inst_lit_sel_side                     num_symb
% 39.40/5.49  --inst_solver_per_active                1400
% 39.40/5.49  --inst_solver_calls_frac                1.
% 39.40/5.49  --inst_passive_queue_type               priority_queues
% 39.40/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.40/5.49  --inst_passive_queues_freq              [25;2]
% 39.40/5.49  --inst_dismatching                      true
% 39.40/5.49  --inst_eager_unprocessed_to_passive     true
% 39.40/5.49  --inst_prop_sim_given                   true
% 39.40/5.49  --inst_prop_sim_new                     false
% 39.40/5.49  --inst_subs_new                         false
% 39.40/5.49  --inst_eq_res_simp                      false
% 39.40/5.49  --inst_subs_given                       false
% 39.40/5.49  --inst_orphan_elimination               true
% 39.40/5.49  --inst_learning_loop_flag               true
% 39.40/5.49  --inst_learning_start                   3000
% 39.40/5.49  --inst_learning_factor                  2
% 39.40/5.49  --inst_start_prop_sim_after_learn       3
% 39.40/5.49  --inst_sel_renew                        solver
% 39.40/5.49  --inst_lit_activity_flag                true
% 39.40/5.49  --inst_restr_to_given                   false
% 39.40/5.49  --inst_activity_threshold               500
% 39.40/5.49  --inst_out_proof                        true
% 39.40/5.49  
% 39.40/5.49  ------ Resolution Options
% 39.40/5.49  
% 39.40/5.49  --resolution_flag                       true
% 39.40/5.49  --res_lit_sel                           adaptive
% 39.40/5.49  --res_lit_sel_side                      none
% 39.40/5.49  --res_ordering                          kbo
% 39.40/5.49  --res_to_prop_solver                    active
% 39.40/5.49  --res_prop_simpl_new                    false
% 39.40/5.49  --res_prop_simpl_given                  true
% 39.40/5.49  --res_passive_queue_type                priority_queues
% 39.40/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.40/5.49  --res_passive_queues_freq               [15;5]
% 39.40/5.49  --res_forward_subs                      full
% 39.40/5.49  --res_backward_subs                     full
% 39.40/5.49  --res_forward_subs_resolution           true
% 39.40/5.49  --res_backward_subs_resolution          true
% 39.40/5.49  --res_orphan_elimination                true
% 39.40/5.49  --res_time_limit                        2.
% 39.40/5.49  --res_out_proof                         true
% 39.40/5.49  
% 39.40/5.49  ------ Superposition Options
% 39.40/5.49  
% 39.40/5.49  --superposition_flag                    true
% 39.40/5.49  --sup_passive_queue_type                priority_queues
% 39.40/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.40/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.40/5.49  --demod_completeness_check              fast
% 39.40/5.49  --demod_use_ground                      true
% 39.40/5.49  --sup_to_prop_solver                    passive
% 39.40/5.49  --sup_prop_simpl_new                    true
% 39.40/5.49  --sup_prop_simpl_given                  true
% 39.40/5.49  --sup_fun_splitting                     false
% 39.40/5.49  --sup_smt_interval                      50000
% 39.40/5.49  
% 39.40/5.49  ------ Superposition Simplification Setup
% 39.40/5.49  
% 39.40/5.49  --sup_indices_passive                   []
% 39.40/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.40/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.40/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.40/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.40/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.40/5.49  --sup_full_bw                           [BwDemod]
% 39.40/5.49  --sup_immed_triv                        [TrivRules]
% 39.40/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.40/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.40/5.49  --sup_immed_bw_main                     []
% 39.40/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.40/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.40/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.40/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.40/5.49  
% 39.40/5.49  ------ Combination Options
% 39.40/5.49  
% 39.40/5.49  --comb_res_mult                         3
% 39.40/5.49  --comb_sup_mult                         2
% 39.40/5.49  --comb_inst_mult                        10
% 39.40/5.49  
% 39.40/5.49  ------ Debug Options
% 39.40/5.49  
% 39.40/5.49  --dbg_backtrace                         false
% 39.40/5.49  --dbg_dump_prop_clauses                 false
% 39.40/5.49  --dbg_dump_prop_clauses_file            -
% 39.40/5.49  --dbg_out_stat                          false
% 39.40/5.49  ------ Parsing...
% 39.40/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.40/5.49  
% 39.40/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.40/5.49  
% 39.40/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.40/5.49  
% 39.40/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.40/5.49  ------ Proving...
% 39.40/5.49  ------ Problem Properties 
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  clauses                                 13
% 39.40/5.49  conjectures                             3
% 39.40/5.49  EPR                                     0
% 39.40/5.49  Horn                                    13
% 39.40/5.49  unary                                   5
% 39.40/5.49  binary                                  6
% 39.40/5.49  lits                                    24
% 39.40/5.49  lits eq                                 3
% 39.40/5.49  fd_pure                                 0
% 39.40/5.49  fd_pseudo                               0
% 39.40/5.49  fd_cond                                 0
% 39.40/5.49  fd_pseudo_cond                          0
% 39.40/5.49  AC symbols                              0
% 39.40/5.49  
% 39.40/5.49  ------ Schedule dynamic 5 is on 
% 39.40/5.49  
% 39.40/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  ------ 
% 39.40/5.49  Current options:
% 39.40/5.49  ------ 
% 39.40/5.49  
% 39.40/5.49  ------ Input Options
% 39.40/5.49  
% 39.40/5.49  --out_options                           all
% 39.40/5.49  --tptp_safe_out                         true
% 39.40/5.49  --problem_path                          ""
% 39.40/5.49  --include_path                          ""
% 39.40/5.49  --clausifier                            res/vclausify_rel
% 39.40/5.49  --clausifier_options                    --mode clausify
% 39.40/5.49  --stdin                                 false
% 39.40/5.49  --stats_out                             all
% 39.40/5.49  
% 39.40/5.49  ------ General Options
% 39.40/5.49  
% 39.40/5.49  --fof                                   false
% 39.40/5.49  --time_out_real                         305.
% 39.40/5.49  --time_out_virtual                      -1.
% 39.40/5.49  --symbol_type_check                     false
% 39.40/5.49  --clausify_out                          false
% 39.40/5.49  --sig_cnt_out                           false
% 39.40/5.49  --trig_cnt_out                          false
% 39.40/5.49  --trig_cnt_out_tolerance                1.
% 39.40/5.49  --trig_cnt_out_sk_spl                   false
% 39.40/5.49  --abstr_cl_out                          false
% 39.40/5.49  
% 39.40/5.49  ------ Global Options
% 39.40/5.49  
% 39.40/5.49  --schedule                              default
% 39.40/5.49  --add_important_lit                     false
% 39.40/5.49  --prop_solver_per_cl                    1000
% 39.40/5.49  --min_unsat_core                        false
% 39.40/5.49  --soft_assumptions                      false
% 39.40/5.49  --soft_lemma_size                       3
% 39.40/5.49  --prop_impl_unit_size                   0
% 39.40/5.49  --prop_impl_unit                        []
% 39.40/5.49  --share_sel_clauses                     true
% 39.40/5.49  --reset_solvers                         false
% 39.40/5.49  --bc_imp_inh                            [conj_cone]
% 39.40/5.49  --conj_cone_tolerance                   3.
% 39.40/5.49  --extra_neg_conj                        none
% 39.40/5.49  --large_theory_mode                     true
% 39.40/5.49  --prolific_symb_bound                   200
% 39.40/5.49  --lt_threshold                          2000
% 39.40/5.49  --clause_weak_htbl                      true
% 39.40/5.49  --gc_record_bc_elim                     false
% 39.40/5.49  
% 39.40/5.49  ------ Preprocessing Options
% 39.40/5.49  
% 39.40/5.49  --preprocessing_flag                    true
% 39.40/5.49  --time_out_prep_mult                    0.1
% 39.40/5.49  --splitting_mode                        input
% 39.40/5.49  --splitting_grd                         true
% 39.40/5.49  --splitting_cvd                         false
% 39.40/5.49  --splitting_cvd_svl                     false
% 39.40/5.49  --splitting_nvd                         32
% 39.40/5.49  --sub_typing                            true
% 39.40/5.49  --prep_gs_sim                           true
% 39.40/5.49  --prep_unflatten                        true
% 39.40/5.49  --prep_res_sim                          true
% 39.40/5.49  --prep_upred                            true
% 39.40/5.49  --prep_sem_filter                       exhaustive
% 39.40/5.49  --prep_sem_filter_out                   false
% 39.40/5.49  --pred_elim                             true
% 39.40/5.49  --res_sim_input                         true
% 39.40/5.49  --eq_ax_congr_red                       true
% 39.40/5.49  --pure_diseq_elim                       true
% 39.40/5.49  --brand_transform                       false
% 39.40/5.49  --non_eq_to_eq                          false
% 39.40/5.49  --prep_def_merge                        true
% 39.40/5.49  --prep_def_merge_prop_impl              false
% 39.40/5.49  --prep_def_merge_mbd                    true
% 39.40/5.49  --prep_def_merge_tr_red                 false
% 39.40/5.49  --prep_def_merge_tr_cl                  false
% 39.40/5.49  --smt_preprocessing                     true
% 39.40/5.49  --smt_ac_axioms                         fast
% 39.40/5.49  --preprocessed_out                      false
% 39.40/5.49  --preprocessed_stats                    false
% 39.40/5.49  
% 39.40/5.49  ------ Abstraction refinement Options
% 39.40/5.49  
% 39.40/5.49  --abstr_ref                             []
% 39.40/5.49  --abstr_ref_prep                        false
% 39.40/5.49  --abstr_ref_until_sat                   false
% 39.40/5.49  --abstr_ref_sig_restrict                funpre
% 39.40/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.40/5.49  --abstr_ref_under                       []
% 39.40/5.49  
% 39.40/5.49  ------ SAT Options
% 39.40/5.49  
% 39.40/5.49  --sat_mode                              false
% 39.40/5.49  --sat_fm_restart_options                ""
% 39.40/5.49  --sat_gr_def                            false
% 39.40/5.49  --sat_epr_types                         true
% 39.40/5.49  --sat_non_cyclic_types                  false
% 39.40/5.49  --sat_finite_models                     false
% 39.40/5.49  --sat_fm_lemmas                         false
% 39.40/5.49  --sat_fm_prep                           false
% 39.40/5.49  --sat_fm_uc_incr                        true
% 39.40/5.49  --sat_out_model                         small
% 39.40/5.49  --sat_out_clauses                       false
% 39.40/5.49  
% 39.40/5.49  ------ QBF Options
% 39.40/5.49  
% 39.40/5.49  --qbf_mode                              false
% 39.40/5.49  --qbf_elim_univ                         false
% 39.40/5.49  --qbf_dom_inst                          none
% 39.40/5.49  --qbf_dom_pre_inst                      false
% 39.40/5.49  --qbf_sk_in                             false
% 39.40/5.49  --qbf_pred_elim                         true
% 39.40/5.49  --qbf_split                             512
% 39.40/5.49  
% 39.40/5.49  ------ BMC1 Options
% 39.40/5.49  
% 39.40/5.49  --bmc1_incremental                      false
% 39.40/5.49  --bmc1_axioms                           reachable_all
% 39.40/5.49  --bmc1_min_bound                        0
% 39.40/5.49  --bmc1_max_bound                        -1
% 39.40/5.49  --bmc1_max_bound_default                -1
% 39.40/5.49  --bmc1_symbol_reachability              true
% 39.40/5.49  --bmc1_property_lemmas                  false
% 39.40/5.49  --bmc1_k_induction                      false
% 39.40/5.49  --bmc1_non_equiv_states                 false
% 39.40/5.49  --bmc1_deadlock                         false
% 39.40/5.49  --bmc1_ucm                              false
% 39.40/5.49  --bmc1_add_unsat_core                   none
% 39.40/5.49  --bmc1_unsat_core_children              false
% 39.40/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.40/5.49  --bmc1_out_stat                         full
% 39.40/5.49  --bmc1_ground_init                      false
% 39.40/5.49  --bmc1_pre_inst_next_state              false
% 39.40/5.49  --bmc1_pre_inst_state                   false
% 39.40/5.49  --bmc1_pre_inst_reach_state             false
% 39.40/5.49  --bmc1_out_unsat_core                   false
% 39.40/5.49  --bmc1_aig_witness_out                  false
% 39.40/5.49  --bmc1_verbose                          false
% 39.40/5.49  --bmc1_dump_clauses_tptp                false
% 39.40/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.40/5.49  --bmc1_dump_file                        -
% 39.40/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.40/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.40/5.49  --bmc1_ucm_extend_mode                  1
% 39.40/5.49  --bmc1_ucm_init_mode                    2
% 39.40/5.49  --bmc1_ucm_cone_mode                    none
% 39.40/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.40/5.49  --bmc1_ucm_relax_model                  4
% 39.40/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.40/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.40/5.49  --bmc1_ucm_layered_model                none
% 39.40/5.49  --bmc1_ucm_max_lemma_size               10
% 39.40/5.49  
% 39.40/5.49  ------ AIG Options
% 39.40/5.49  
% 39.40/5.49  --aig_mode                              false
% 39.40/5.49  
% 39.40/5.49  ------ Instantiation Options
% 39.40/5.49  
% 39.40/5.49  --instantiation_flag                    true
% 39.40/5.49  --inst_sos_flag                         false
% 39.40/5.49  --inst_sos_phase                        true
% 39.40/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.40/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.40/5.49  --inst_lit_sel_side                     none
% 39.40/5.49  --inst_solver_per_active                1400
% 39.40/5.49  --inst_solver_calls_frac                1.
% 39.40/5.49  --inst_passive_queue_type               priority_queues
% 39.40/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.40/5.49  --inst_passive_queues_freq              [25;2]
% 39.40/5.49  --inst_dismatching                      true
% 39.40/5.49  --inst_eager_unprocessed_to_passive     true
% 39.40/5.49  --inst_prop_sim_given                   true
% 39.40/5.49  --inst_prop_sim_new                     false
% 39.40/5.49  --inst_subs_new                         false
% 39.40/5.49  --inst_eq_res_simp                      false
% 39.40/5.49  --inst_subs_given                       false
% 39.40/5.49  --inst_orphan_elimination               true
% 39.40/5.49  --inst_learning_loop_flag               true
% 39.40/5.49  --inst_learning_start                   3000
% 39.40/5.49  --inst_learning_factor                  2
% 39.40/5.49  --inst_start_prop_sim_after_learn       3
% 39.40/5.49  --inst_sel_renew                        solver
% 39.40/5.49  --inst_lit_activity_flag                true
% 39.40/5.49  --inst_restr_to_given                   false
% 39.40/5.49  --inst_activity_threshold               500
% 39.40/5.49  --inst_out_proof                        true
% 39.40/5.49  
% 39.40/5.49  ------ Resolution Options
% 39.40/5.49  
% 39.40/5.49  --resolution_flag                       false
% 39.40/5.49  --res_lit_sel                           adaptive
% 39.40/5.49  --res_lit_sel_side                      none
% 39.40/5.49  --res_ordering                          kbo
% 39.40/5.49  --res_to_prop_solver                    active
% 39.40/5.49  --res_prop_simpl_new                    false
% 39.40/5.49  --res_prop_simpl_given                  true
% 39.40/5.49  --res_passive_queue_type                priority_queues
% 39.40/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.40/5.49  --res_passive_queues_freq               [15;5]
% 39.40/5.49  --res_forward_subs                      full
% 39.40/5.49  --res_backward_subs                     full
% 39.40/5.49  --res_forward_subs_resolution           true
% 39.40/5.49  --res_backward_subs_resolution          true
% 39.40/5.49  --res_orphan_elimination                true
% 39.40/5.49  --res_time_limit                        2.
% 39.40/5.49  --res_out_proof                         true
% 39.40/5.49  
% 39.40/5.49  ------ Superposition Options
% 39.40/5.49  
% 39.40/5.49  --superposition_flag                    true
% 39.40/5.49  --sup_passive_queue_type                priority_queues
% 39.40/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.40/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.40/5.49  --demod_completeness_check              fast
% 39.40/5.49  --demod_use_ground                      true
% 39.40/5.49  --sup_to_prop_solver                    passive
% 39.40/5.49  --sup_prop_simpl_new                    true
% 39.40/5.49  --sup_prop_simpl_given                  true
% 39.40/5.49  --sup_fun_splitting                     false
% 39.40/5.49  --sup_smt_interval                      50000
% 39.40/5.49  
% 39.40/5.49  ------ Superposition Simplification Setup
% 39.40/5.49  
% 39.40/5.49  --sup_indices_passive                   []
% 39.40/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.40/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.40/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.40/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.40/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.40/5.49  --sup_full_bw                           [BwDemod]
% 39.40/5.49  --sup_immed_triv                        [TrivRules]
% 39.40/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.40/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.40/5.49  --sup_immed_bw_main                     []
% 39.40/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.40/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.40/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.40/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.40/5.49  
% 39.40/5.49  ------ Combination Options
% 39.40/5.49  
% 39.40/5.49  --comb_res_mult                         3
% 39.40/5.49  --comb_sup_mult                         2
% 39.40/5.49  --comb_inst_mult                        10
% 39.40/5.49  
% 39.40/5.49  ------ Debug Options
% 39.40/5.49  
% 39.40/5.49  --dbg_backtrace                         false
% 39.40/5.49  --dbg_dump_prop_clauses                 false
% 39.40/5.49  --dbg_dump_prop_clauses_file            -
% 39.40/5.49  --dbg_out_stat                          false
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  ------ Proving...
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  % SZS status Theorem for theBenchmark.p
% 39.40/5.49  
% 39.40/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.40/5.49  
% 39.40/5.49  fof(f3,axiom,(
% 39.40/5.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f30,plain,(
% 39.40/5.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f3])).
% 39.40/5.49  
% 39.40/5.49  fof(f7,axiom,(
% 39.40/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f34,plain,(
% 39.40/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 39.40/5.49    inference(cnf_transformation,[],[f7])).
% 39.40/5.49  
% 39.40/5.49  fof(f43,plain,(
% 39.40/5.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 39.40/5.49    inference(definition_unfolding,[],[f30,f34])).
% 39.40/5.49  
% 39.40/5.49  fof(f2,axiom,(
% 39.40/5.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f14,plain,(
% 39.40/5.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.40/5.49    inference(ennf_transformation,[],[f2])).
% 39.40/5.49  
% 39.40/5.49  fof(f29,plain,(
% 39.40/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f14])).
% 39.40/5.49  
% 39.40/5.49  fof(f1,axiom,(
% 39.40/5.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f13,plain,(
% 39.40/5.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 39.40/5.49    inference(ennf_transformation,[],[f1])).
% 39.40/5.49  
% 39.40/5.49  fof(f28,plain,(
% 39.40/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f13])).
% 39.40/5.49  
% 39.40/5.49  fof(f8,axiom,(
% 39.40/5.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f23,plain,(
% 39.40/5.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.40/5.49    inference(nnf_transformation,[],[f8])).
% 39.40/5.49  
% 39.40/5.49  fof(f36,plain,(
% 39.40/5.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f23])).
% 39.40/5.49  
% 39.40/5.49  fof(f10,axiom,(
% 39.40/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f20,plain,(
% 39.40/5.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.40/5.49    inference(ennf_transformation,[],[f10])).
% 39.40/5.49  
% 39.40/5.49  fof(f21,plain,(
% 39.40/5.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.40/5.49    inference(flattening,[],[f20])).
% 39.40/5.49  
% 39.40/5.49  fof(f38,plain,(
% 39.40/5.49    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f21])).
% 39.40/5.49  
% 39.40/5.49  fof(f11,conjecture,(
% 39.40/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f12,negated_conjecture,(
% 39.40/5.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 39.40/5.49    inference(negated_conjecture,[],[f11])).
% 39.40/5.49  
% 39.40/5.49  fof(f22,plain,(
% 39.40/5.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 39.40/5.49    inference(ennf_transformation,[],[f12])).
% 39.40/5.49  
% 39.40/5.49  fof(f26,plain,(
% 39.40/5.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.40/5.49    introduced(choice_axiom,[])).
% 39.40/5.49  
% 39.40/5.49  fof(f25,plain,(
% 39.40/5.49    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.40/5.49    introduced(choice_axiom,[])).
% 39.40/5.49  
% 39.40/5.49  fof(f24,plain,(
% 39.40/5.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 39.40/5.49    introduced(choice_axiom,[])).
% 39.40/5.49  
% 39.40/5.49  fof(f27,plain,(
% 39.40/5.49    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 39.40/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).
% 39.40/5.49  
% 39.40/5.49  fof(f39,plain,(
% 39.40/5.49    l1_pre_topc(sK0)),
% 39.40/5.49    inference(cnf_transformation,[],[f27])).
% 39.40/5.49  
% 39.40/5.49  fof(f4,axiom,(
% 39.40/5.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f15,plain,(
% 39.40/5.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 39.40/5.49    inference(ennf_transformation,[],[f4])).
% 39.40/5.49  
% 39.40/5.49  fof(f16,plain,(
% 39.40/5.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 39.40/5.49    inference(flattening,[],[f15])).
% 39.40/5.49  
% 39.40/5.49  fof(f31,plain,(
% 39.40/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f16])).
% 39.40/5.49  
% 39.40/5.49  fof(f44,plain,(
% 39.40/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 39.40/5.49    inference(definition_unfolding,[],[f31,f34])).
% 39.40/5.49  
% 39.40/5.49  fof(f41,plain,(
% 39.40/5.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.40/5.49    inference(cnf_transformation,[],[f27])).
% 39.40/5.49  
% 39.40/5.49  fof(f9,axiom,(
% 39.40/5.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f18,plain,(
% 39.40/5.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.40/5.49    inference(ennf_transformation,[],[f9])).
% 39.40/5.49  
% 39.40/5.49  fof(f19,plain,(
% 39.40/5.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.40/5.49    inference(flattening,[],[f18])).
% 39.40/5.49  
% 39.40/5.49  fof(f37,plain,(
% 39.40/5.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f19])).
% 39.40/5.49  
% 39.40/5.49  fof(f35,plain,(
% 39.40/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.40/5.49    inference(cnf_transformation,[],[f23])).
% 39.40/5.49  
% 39.40/5.49  fof(f6,axiom,(
% 39.40/5.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f17,plain,(
% 39.40/5.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 39.40/5.49    inference(ennf_transformation,[],[f6])).
% 39.40/5.49  
% 39.40/5.49  fof(f33,plain,(
% 39.40/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 39.40/5.49    inference(cnf_transformation,[],[f17])).
% 39.40/5.49  
% 39.40/5.49  fof(f45,plain,(
% 39.40/5.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 39.40/5.49    inference(definition_unfolding,[],[f33,f34])).
% 39.40/5.49  
% 39.40/5.49  fof(f42,plain,(
% 39.40/5.49    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 39.40/5.49    inference(cnf_transformation,[],[f27])).
% 39.40/5.49  
% 39.40/5.49  fof(f5,axiom,(
% 39.40/5.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 39.40/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.40/5.49  
% 39.40/5.49  fof(f32,plain,(
% 39.40/5.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 39.40/5.49    inference(cnf_transformation,[],[f5])).
% 39.40/5.49  
% 39.40/5.49  fof(f40,plain,(
% 39.40/5.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.40/5.49    inference(cnf_transformation,[],[f27])).
% 39.40/5.49  
% 39.40/5.49  cnf(c_2,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 39.40/5.49      inference(cnf_transformation,[],[f43]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_650,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1,plain,
% 39.40/5.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 39.40/5.49      inference(cnf_transformation,[],[f29]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_651,plain,
% 39.40/5.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1180,plain,
% 39.40/5.49      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = X0 ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_650,c_651]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_0,plain,
% 39.40/5.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 39.40/5.49      inference(cnf_transformation,[],[f28]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_652,plain,
% 39.40/5.49      ( r1_tarski(X0,X1) = iProver_top
% 39.40/5.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_2045,plain,
% 39.40/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.40/5.49      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_1180,c_652]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_6,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.40/5.49      inference(cnf_transformation,[],[f36]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_648,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.40/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_9,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | ~ r1_tarski(X0,X2)
% 39.40/5.49      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 39.40/5.49      | ~ l1_pre_topc(X1) ),
% 39.40/5.49      inference(cnf_transformation,[],[f38]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_13,negated_conjecture,
% 39.40/5.49      ( l1_pre_topc(sK0) ),
% 39.40/5.49      inference(cnf_transformation,[],[f39]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_182,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | ~ r1_tarski(X0,X2)
% 39.40/5.49      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 39.40/5.49      | sK0 != X1 ),
% 39.40/5.49      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_183,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.40/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.40/5.49      | ~ r1_tarski(X1,X0)
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 39.40/5.49      inference(unflattening,[status(thm)],[c_182]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_642,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(X1,X0) != iProver_top
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_3,plain,
% 39.40/5.49      ( ~ r1_tarski(X0,X1)
% 39.40/5.49      | ~ r1_tarski(X0,X2)
% 39.40/5.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 39.40/5.49      inference(cnf_transformation,[],[f44]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_649,plain,
% 39.40/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.40/5.49      | r1_tarski(X0,X2) != iProver_top
% 39.40/5.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_11,negated_conjecture,
% 39.40/5.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.40/5.49      inference(cnf_transformation,[],[f41]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_645,plain,
% 39.40/5.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_8,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | ~ l1_pre_topc(X1) ),
% 39.40/5.49      inference(cnf_transformation,[],[f37]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_200,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.40/5.49      | sK0 != X1 ),
% 39.40/5.49      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_201,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.40/5.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.40/5.49      inference(unflattening,[status(thm)],[c_200]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_641,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_7,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.40/5.49      inference(cnf_transformation,[],[f35]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_647,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.40/5.49      | r1_tarski(X0,X1) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1285,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_641,c_647]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_5,plain,
% 39.40/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.40/5.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 39.40/5.49      inference(cnf_transformation,[],[f45]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_105,plain,
% 39.40/5.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 39.40/5.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_106,plain,
% 39.40/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.40/5.49      inference(renaming,[status(thm)],[c_105]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_127,plain,
% 39.40/5.49      ( ~ r1_tarski(X0,X1)
% 39.40/5.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 39.40/5.49      inference(bin_hyper_res,[status(thm)],[c_5,c_106]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_643,plain,
% 39.40/5.49      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 39.40/5.49      | r1_tarski(X2,X0) != iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1926,plain,
% 39.40/5.49      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
% 39.40/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_1285,c_643]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_7417,plain,
% 39.40/5.49      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_645,c_1926]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1283,plain,
% 39.40/5.49      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_645,c_647]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1422,plain,
% 39.40/5.49      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_1283,c_643]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_10,negated_conjecture,
% 39.40/5.49      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 39.40/5.49      inference(cnf_transformation,[],[f42]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_646,plain,
% 39.40/5.49      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1648,plain,
% 39.40/5.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 39.40/5.49      inference(demodulation,[status(thm)],[c_1422,c_646]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_7877,plain,
% 39.40/5.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
% 39.40/5.49      inference(demodulation,[status(thm)],[c_7417,c_1648]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_7991,plain,
% 39.40/5.49      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_649,c_7877]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_163958,plain,
% 39.40/5.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
% 39.40/5.49      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_642,c_7991]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_16,plain,
% 39.40/5.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_164576,plain,
% 39.40/5.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top
% 39.40/5.49      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 39.40/5.49      inference(global_propositional_subsumption,
% 39.40/5.49                [status(thm)],
% 39.40/5.49                [c_163958,c_16]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_4,plain,
% 39.40/5.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 39.40/5.49      inference(cnf_transformation,[],[f32]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_1037,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_4,c_650]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_164583,plain,
% 39.40/5.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 39.40/5.49      inference(forward_subsumption_resolution,
% 39.40/5.49                [status(thm)],
% 39.40/5.49                [c_164576,c_1037]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_164585,plain,
% 39.40/5.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_642,c_164583]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_12,negated_conjecture,
% 39.40/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.40/5.49      inference(cnf_transformation,[],[f40]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_15,plain,
% 39.40/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_907,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) ),
% 39.40/5.49      inference(instantiation,[status(thm)],[c_2]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_2734,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
% 39.40/5.49      inference(instantiation,[status(thm)],[c_907]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_2739,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_2734]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_164689,plain,
% 39.40/5.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.40/5.49      inference(global_propositional_subsumption,
% 39.40/5.49                [status(thm)],
% 39.40/5.49                [c_164585,c_15,c_2739]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_164694,plain,
% 39.40/5.49      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_648,c_164689]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_168826,plain,
% 39.40/5.49      ( r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 39.40/5.49      inference(superposition,[status(thm)],[c_2045,c_164694]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_751,plain,
% 39.40/5.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.40/5.49      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 39.40/5.49      inference(instantiation,[status(thm)],[c_7]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(c_752,plain,
% 39.40/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.40/5.49      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 39.40/5.49      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 39.40/5.49  
% 39.40/5.49  cnf(contradiction,plain,
% 39.40/5.49      ( $false ),
% 39.40/5.49      inference(minisat,[status(thm)],[c_168826,c_752,c_15]) ).
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.40/5.49  
% 39.40/5.49  ------                               Statistics
% 39.40/5.49  
% 39.40/5.49  ------ General
% 39.40/5.49  
% 39.40/5.49  abstr_ref_over_cycles:                  0
% 39.40/5.49  abstr_ref_under_cycles:                 0
% 39.40/5.49  gc_basic_clause_elim:                   0
% 39.40/5.49  forced_gc_time:                         0
% 39.40/5.49  parsing_time:                           0.012
% 39.40/5.49  unif_index_cands_time:                  0.
% 39.40/5.49  unif_index_add_time:                    0.
% 39.40/5.49  orderings_time:                         0.
% 39.40/5.49  out_proof_time:                         0.03
% 39.40/5.49  total_time:                             4.918
% 39.40/5.49  num_of_symbols:                         44
% 39.40/5.49  num_of_terms:                           124646
% 39.40/5.49  
% 39.40/5.49  ------ Preprocessing
% 39.40/5.49  
% 39.40/5.49  num_of_splits:                          0
% 39.40/5.49  num_of_split_atoms:                     0
% 39.40/5.49  num_of_reused_defs:                     0
% 39.40/5.49  num_eq_ax_congr_red:                    12
% 39.40/5.49  num_of_sem_filtered_clauses:            1
% 39.40/5.49  num_of_subtypes:                        0
% 39.40/5.49  monotx_restored_types:                  0
% 39.40/5.49  sat_num_of_epr_types:                   0
% 39.40/5.49  sat_num_of_non_cyclic_types:            0
% 39.40/5.49  sat_guarded_non_collapsed_types:        0
% 39.40/5.49  num_pure_diseq_elim:                    0
% 39.40/5.49  simp_replaced_by:                       0
% 39.40/5.49  res_preprocessed:                       72
% 39.40/5.49  prep_upred:                             0
% 39.40/5.49  prep_unflattend:                        2
% 39.40/5.49  smt_new_axioms:                         0
% 39.40/5.49  pred_elim_cands:                        2
% 39.40/5.49  pred_elim:                              1
% 39.40/5.49  pred_elim_cl:                           1
% 39.40/5.49  pred_elim_cycles:                       3
% 39.40/5.49  merged_defs:                            8
% 39.40/5.49  merged_defs_ncl:                        0
% 39.40/5.49  bin_hyper_res:                          9
% 39.40/5.49  prep_cycles:                            4
% 39.40/5.49  pred_elim_time:                         0.001
% 39.40/5.49  splitting_time:                         0.
% 39.40/5.49  sem_filter_time:                        0.
% 39.40/5.49  monotx_time:                            0.
% 39.40/5.49  subtype_inf_time:                       0.
% 39.40/5.49  
% 39.40/5.49  ------ Problem properties
% 39.40/5.49  
% 39.40/5.49  clauses:                                13
% 39.40/5.49  conjectures:                            3
% 39.40/5.49  epr:                                    0
% 39.40/5.49  horn:                                   13
% 39.40/5.49  ground:                                 3
% 39.40/5.49  unary:                                  5
% 39.40/5.49  binary:                                 6
% 39.40/5.49  lits:                                   24
% 39.40/5.49  lits_eq:                                3
% 39.40/5.49  fd_pure:                                0
% 39.40/5.49  fd_pseudo:                              0
% 39.40/5.49  fd_cond:                                0
% 39.40/5.49  fd_pseudo_cond:                         0
% 39.40/5.49  ac_symbols:                             0
% 39.40/5.49  
% 39.40/5.49  ------ Propositional Solver
% 39.40/5.49  
% 39.40/5.49  prop_solver_calls:                      67
% 39.40/5.49  prop_fast_solver_calls:                 2710
% 39.40/5.49  smt_solver_calls:                       0
% 39.40/5.49  smt_fast_solver_calls:                  0
% 39.40/5.49  prop_num_of_clauses:                    66773
% 39.40/5.49  prop_preprocess_simplified:             88925
% 39.40/5.49  prop_fo_subsumed:                       87
% 39.40/5.49  prop_solver_time:                       0.
% 39.40/5.49  smt_solver_time:                        0.
% 39.40/5.49  smt_fast_solver_time:                   0.
% 39.40/5.49  prop_fast_solver_time:                  0.
% 39.40/5.49  prop_unsat_core_time:                   0.008
% 39.40/5.49  
% 39.40/5.49  ------ QBF
% 39.40/5.49  
% 39.40/5.49  qbf_q_res:                              0
% 39.40/5.49  qbf_num_tautologies:                    0
% 39.40/5.49  qbf_prep_cycles:                        0
% 39.40/5.49  
% 39.40/5.49  ------ BMC1
% 39.40/5.49  
% 39.40/5.49  bmc1_current_bound:                     -1
% 39.40/5.49  bmc1_last_solved_bound:                 -1
% 39.40/5.49  bmc1_unsat_core_size:                   -1
% 39.40/5.49  bmc1_unsat_core_parents_size:           -1
% 39.40/5.49  bmc1_merge_next_fun:                    0
% 39.40/5.49  bmc1_unsat_core_clauses_time:           0.
% 39.40/5.49  
% 39.40/5.49  ------ Instantiation
% 39.40/5.49  
% 39.40/5.49  inst_num_of_clauses:                    2713
% 39.40/5.49  inst_num_in_passive:                    118
% 39.40/5.49  inst_num_in_active:                     4220
% 39.40/5.49  inst_num_in_unprocessed:                1057
% 39.40/5.49  inst_num_of_loops:                      4599
% 39.40/5.49  inst_num_of_learning_restarts:          1
% 39.40/5.49  inst_num_moves_active_passive:          376
% 39.40/5.49  inst_lit_activity:                      0
% 39.40/5.49  inst_lit_activity_moves:                8
% 39.40/5.49  inst_num_tautologies:                   0
% 39.40/5.49  inst_num_prop_implied:                  0
% 39.40/5.49  inst_num_existing_simplified:           0
% 39.40/5.49  inst_num_eq_res_simplified:             0
% 39.40/5.49  inst_num_child_elim:                    0
% 39.40/5.49  inst_num_of_dismatching_blockings:      16162
% 39.40/5.49  inst_num_of_non_proper_insts:           13999
% 39.40/5.49  inst_num_of_duplicates:                 0
% 39.40/5.49  inst_inst_num_from_inst_to_res:         0
% 39.40/5.49  inst_dismatching_checking_time:         0.
% 39.40/5.49  
% 39.40/5.49  ------ Resolution
% 39.40/5.49  
% 39.40/5.49  res_num_of_clauses:                     22
% 39.40/5.49  res_num_in_passive:                     22
% 39.40/5.49  res_num_in_active:                      0
% 39.40/5.49  res_num_of_loops:                       76
% 39.40/5.49  res_forward_subset_subsumed:            364
% 39.40/5.49  res_backward_subset_subsumed:           8
% 39.40/5.49  res_forward_subsumed:                   0
% 39.40/5.49  res_backward_subsumed:                  0
% 39.40/5.49  res_forward_subsumption_resolution:     0
% 39.40/5.49  res_backward_subsumption_resolution:    0
% 39.40/5.49  res_clause_to_clause_subsumption:       101799
% 39.40/5.49  res_orphan_elimination:                 0
% 39.40/5.49  res_tautology_del:                      331
% 39.40/5.49  res_num_eq_res_simplified:              0
% 39.40/5.49  res_num_sel_changes:                    0
% 39.40/5.49  res_moves_from_active_to_pass:          0
% 39.40/5.49  
% 39.40/5.49  ------ Superposition
% 39.40/5.49  
% 39.40/5.49  sup_time_total:                         0.
% 39.40/5.49  sup_time_generating:                    0.
% 39.40/5.49  sup_time_sim_full:                      0.
% 39.40/5.49  sup_time_sim_immed:                     0.
% 39.40/5.49  
% 39.40/5.49  sup_num_of_clauses:                     5878
% 39.40/5.49  sup_num_in_active:                      903
% 39.40/5.49  sup_num_in_passive:                     4975
% 39.40/5.49  sup_num_of_loops:                       919
% 39.40/5.49  sup_fw_superposition:                   11518
% 39.40/5.49  sup_bw_superposition:                   3152
% 39.40/5.49  sup_immediate_simplified:               930
% 39.40/5.49  sup_given_eliminated:                   0
% 39.40/5.49  comparisons_done:                       0
% 39.40/5.49  comparisons_avoided:                    0
% 39.40/5.49  
% 39.40/5.49  ------ Simplifications
% 39.40/5.49  
% 39.40/5.49  
% 39.40/5.49  sim_fw_subset_subsumed:                 30
% 39.40/5.49  sim_bw_subset_subsumed:                 107
% 39.40/5.49  sim_fw_subsumed:                        739
% 39.40/5.49  sim_bw_subsumed:                        39
% 39.40/5.49  sim_fw_subsumption_res:                 1
% 39.40/5.49  sim_bw_subsumption_res:                 0
% 39.40/5.49  sim_tautology_del:                      1
% 39.40/5.49  sim_eq_tautology_del:                   36
% 39.40/5.49  sim_eq_res_simp:                        0
% 39.40/5.49  sim_fw_demodulated:                     50
% 39.40/5.49  sim_bw_demodulated:                     6
% 39.40/5.49  sim_light_normalised:                   73
% 39.40/5.49  sim_joinable_taut:                      0
% 39.40/5.49  sim_joinable_simp:                      0
% 39.40/5.49  sim_ac_normalised:                      0
% 39.40/5.49  sim_smt_subsumption:                    0
% 39.40/5.49  
%------------------------------------------------------------------------------
