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
% DateTime   : Thu Dec  3 12:11:36 EST 2020

% Result     : Theorem 15.73s
% Output     : CNFRefutation 15.73s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 360 expanded)
%              Number of clauses        :   57 ( 142 expanded)
%              Number of leaves         :   14 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          :  223 ( 966 expanded)
%              Number of equality atoms :   69 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f33])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_652,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_652,c_2])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_650,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1260,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_650])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_104])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_105])).

cnf(c_645,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_1524,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1260,c_645])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_126,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_105])).

cnf(c_646,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_4562,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_646])).

cnf(c_58596,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4562,c_1260])).

cnf(c_58600,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_58596,c_650])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_644,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_653,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_648,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_643,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_650])).

cnf(c_2055,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_645])).

cnf(c_6031,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_648,c_2055])).

cnf(c_1257,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_650])).

cnf(c_1528,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1257,c_645])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_649,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1769,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1528,c_649])).

cnf(c_6187,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6031,c_1769])).

cnf(c_6765,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_6187])).

cnf(c_8998,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_6765])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_24474,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8998,c_15])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_654,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2342,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_646])).

cnf(c_9819,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2342,c_1257])).

cnf(c_24481,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24474,c_654,c_9819])).

cnf(c_24483,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_24481])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_24486,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24483,c_16])).

cnf(c_24492,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24486,c_9819])).

cnf(c_59160,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_58600,c_24492])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.73/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.73/2.51  
% 15.73/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.73/2.51  
% 15.73/2.51  ------  iProver source info
% 15.73/2.51  
% 15.73/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.73/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.73/2.51  git: non_committed_changes: false
% 15.73/2.51  git: last_make_outside_of_git: false
% 15.73/2.51  
% 15.73/2.51  ------ 
% 15.73/2.51  
% 15.73/2.51  ------ Input Options
% 15.73/2.51  
% 15.73/2.51  --out_options                           all
% 15.73/2.51  --tptp_safe_out                         true
% 15.73/2.51  --problem_path                          ""
% 15.73/2.51  --include_path                          ""
% 15.73/2.51  --clausifier                            res/vclausify_rel
% 15.73/2.51  --clausifier_options                    --mode clausify
% 15.73/2.51  --stdin                                 false
% 15.73/2.51  --stats_out                             all
% 15.73/2.51  
% 15.73/2.51  ------ General Options
% 15.73/2.51  
% 15.73/2.51  --fof                                   false
% 15.73/2.51  --time_out_real                         305.
% 15.73/2.51  --time_out_virtual                      -1.
% 15.73/2.51  --symbol_type_check                     false
% 15.73/2.51  --clausify_out                          false
% 15.73/2.51  --sig_cnt_out                           false
% 15.73/2.51  --trig_cnt_out                          false
% 15.73/2.51  --trig_cnt_out_tolerance                1.
% 15.73/2.51  --trig_cnt_out_sk_spl                   false
% 15.73/2.51  --abstr_cl_out                          false
% 15.73/2.51  
% 15.73/2.51  ------ Global Options
% 15.73/2.51  
% 15.73/2.51  --schedule                              default
% 15.73/2.51  --add_important_lit                     false
% 15.73/2.51  --prop_solver_per_cl                    1000
% 15.73/2.51  --min_unsat_core                        false
% 15.73/2.51  --soft_assumptions                      false
% 15.73/2.51  --soft_lemma_size                       3
% 15.73/2.51  --prop_impl_unit_size                   0
% 15.73/2.51  --prop_impl_unit                        []
% 15.73/2.51  --share_sel_clauses                     true
% 15.73/2.51  --reset_solvers                         false
% 15.73/2.51  --bc_imp_inh                            [conj_cone]
% 15.73/2.51  --conj_cone_tolerance                   3.
% 15.73/2.51  --extra_neg_conj                        none
% 15.73/2.51  --large_theory_mode                     true
% 15.73/2.51  --prolific_symb_bound                   200
% 15.73/2.51  --lt_threshold                          2000
% 15.73/2.51  --clause_weak_htbl                      true
% 15.73/2.51  --gc_record_bc_elim                     false
% 15.73/2.51  
% 15.73/2.51  ------ Preprocessing Options
% 15.73/2.51  
% 15.73/2.51  --preprocessing_flag                    true
% 15.73/2.51  --time_out_prep_mult                    0.1
% 15.73/2.51  --splitting_mode                        input
% 15.73/2.51  --splitting_grd                         true
% 15.73/2.51  --splitting_cvd                         false
% 15.73/2.51  --splitting_cvd_svl                     false
% 15.73/2.51  --splitting_nvd                         32
% 15.73/2.51  --sub_typing                            true
% 15.73/2.51  --prep_gs_sim                           true
% 15.73/2.51  --prep_unflatten                        true
% 15.73/2.51  --prep_res_sim                          true
% 15.73/2.51  --prep_upred                            true
% 15.73/2.51  --prep_sem_filter                       exhaustive
% 15.73/2.51  --prep_sem_filter_out                   false
% 15.73/2.51  --pred_elim                             true
% 15.73/2.51  --res_sim_input                         true
% 15.73/2.51  --eq_ax_congr_red                       true
% 15.73/2.51  --pure_diseq_elim                       true
% 15.73/2.51  --brand_transform                       false
% 15.73/2.51  --non_eq_to_eq                          false
% 15.73/2.51  --prep_def_merge                        true
% 15.73/2.51  --prep_def_merge_prop_impl              false
% 15.73/2.51  --prep_def_merge_mbd                    true
% 15.73/2.51  --prep_def_merge_tr_red                 false
% 15.73/2.51  --prep_def_merge_tr_cl                  false
% 15.73/2.51  --smt_preprocessing                     true
% 15.73/2.51  --smt_ac_axioms                         fast
% 15.73/2.51  --preprocessed_out                      false
% 15.73/2.51  --preprocessed_stats                    false
% 15.73/2.51  
% 15.73/2.51  ------ Abstraction refinement Options
% 15.73/2.51  
% 15.73/2.51  --abstr_ref                             []
% 15.73/2.51  --abstr_ref_prep                        false
% 15.73/2.51  --abstr_ref_until_sat                   false
% 15.73/2.51  --abstr_ref_sig_restrict                funpre
% 15.73/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.73/2.51  --abstr_ref_under                       []
% 15.73/2.51  
% 15.73/2.51  ------ SAT Options
% 15.73/2.51  
% 15.73/2.51  --sat_mode                              false
% 15.73/2.51  --sat_fm_restart_options                ""
% 15.73/2.51  --sat_gr_def                            false
% 15.73/2.51  --sat_epr_types                         true
% 15.73/2.51  --sat_non_cyclic_types                  false
% 15.73/2.51  --sat_finite_models                     false
% 15.73/2.51  --sat_fm_lemmas                         false
% 15.73/2.51  --sat_fm_prep                           false
% 15.73/2.51  --sat_fm_uc_incr                        true
% 15.73/2.51  --sat_out_model                         small
% 15.73/2.51  --sat_out_clauses                       false
% 15.73/2.51  
% 15.73/2.51  ------ QBF Options
% 15.73/2.51  
% 15.73/2.51  --qbf_mode                              false
% 15.73/2.51  --qbf_elim_univ                         false
% 15.73/2.51  --qbf_dom_inst                          none
% 15.73/2.51  --qbf_dom_pre_inst                      false
% 15.73/2.51  --qbf_sk_in                             false
% 15.73/2.51  --qbf_pred_elim                         true
% 15.73/2.51  --qbf_split                             512
% 15.73/2.51  
% 15.73/2.51  ------ BMC1 Options
% 15.73/2.51  
% 15.73/2.51  --bmc1_incremental                      false
% 15.73/2.51  --bmc1_axioms                           reachable_all
% 15.73/2.51  --bmc1_min_bound                        0
% 15.73/2.51  --bmc1_max_bound                        -1
% 15.73/2.51  --bmc1_max_bound_default                -1
% 15.73/2.51  --bmc1_symbol_reachability              true
% 15.73/2.51  --bmc1_property_lemmas                  false
% 15.73/2.51  --bmc1_k_induction                      false
% 15.73/2.51  --bmc1_non_equiv_states                 false
% 15.73/2.51  --bmc1_deadlock                         false
% 15.73/2.51  --bmc1_ucm                              false
% 15.73/2.51  --bmc1_add_unsat_core                   none
% 15.73/2.51  --bmc1_unsat_core_children              false
% 15.73/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.73/2.51  --bmc1_out_stat                         full
% 15.73/2.51  --bmc1_ground_init                      false
% 15.73/2.51  --bmc1_pre_inst_next_state              false
% 15.73/2.51  --bmc1_pre_inst_state                   false
% 15.73/2.51  --bmc1_pre_inst_reach_state             false
% 15.73/2.51  --bmc1_out_unsat_core                   false
% 15.73/2.51  --bmc1_aig_witness_out                  false
% 15.73/2.51  --bmc1_verbose                          false
% 15.73/2.51  --bmc1_dump_clauses_tptp                false
% 15.73/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.73/2.51  --bmc1_dump_file                        -
% 15.73/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.73/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.73/2.51  --bmc1_ucm_extend_mode                  1
% 15.73/2.51  --bmc1_ucm_init_mode                    2
% 15.73/2.51  --bmc1_ucm_cone_mode                    none
% 15.73/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.73/2.51  --bmc1_ucm_relax_model                  4
% 15.73/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.73/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.73/2.51  --bmc1_ucm_layered_model                none
% 15.73/2.51  --bmc1_ucm_max_lemma_size               10
% 15.73/2.51  
% 15.73/2.51  ------ AIG Options
% 15.73/2.51  
% 15.73/2.51  --aig_mode                              false
% 15.73/2.51  
% 15.73/2.51  ------ Instantiation Options
% 15.73/2.51  
% 15.73/2.51  --instantiation_flag                    true
% 15.73/2.51  --inst_sos_flag                         false
% 15.73/2.51  --inst_sos_phase                        true
% 15.73/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.73/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.73/2.51  --inst_lit_sel_side                     num_symb
% 15.73/2.51  --inst_solver_per_active                1400
% 15.73/2.51  --inst_solver_calls_frac                1.
% 15.73/2.51  --inst_passive_queue_type               priority_queues
% 15.73/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.73/2.51  --inst_passive_queues_freq              [25;2]
% 15.73/2.51  --inst_dismatching                      true
% 15.73/2.51  --inst_eager_unprocessed_to_passive     true
% 15.73/2.51  --inst_prop_sim_given                   true
% 15.73/2.51  --inst_prop_sim_new                     false
% 15.73/2.51  --inst_subs_new                         false
% 15.73/2.51  --inst_eq_res_simp                      false
% 15.73/2.51  --inst_subs_given                       false
% 15.73/2.51  --inst_orphan_elimination               true
% 15.73/2.51  --inst_learning_loop_flag               true
% 15.73/2.51  --inst_learning_start                   3000
% 15.73/2.51  --inst_learning_factor                  2
% 15.73/2.51  --inst_start_prop_sim_after_learn       3
% 15.73/2.51  --inst_sel_renew                        solver
% 15.73/2.51  --inst_lit_activity_flag                true
% 15.73/2.51  --inst_restr_to_given                   false
% 15.73/2.51  --inst_activity_threshold               500
% 15.73/2.51  --inst_out_proof                        true
% 15.73/2.51  
% 15.73/2.51  ------ Resolution Options
% 15.73/2.51  
% 15.73/2.51  --resolution_flag                       true
% 15.73/2.51  --res_lit_sel                           adaptive
% 15.73/2.51  --res_lit_sel_side                      none
% 15.73/2.51  --res_ordering                          kbo
% 15.73/2.51  --res_to_prop_solver                    active
% 15.73/2.51  --res_prop_simpl_new                    false
% 15.73/2.51  --res_prop_simpl_given                  true
% 15.73/2.51  --res_passive_queue_type                priority_queues
% 15.73/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.73/2.51  --res_passive_queues_freq               [15;5]
% 15.73/2.51  --res_forward_subs                      full
% 15.73/2.51  --res_backward_subs                     full
% 15.73/2.51  --res_forward_subs_resolution           true
% 15.73/2.51  --res_backward_subs_resolution          true
% 15.73/2.51  --res_orphan_elimination                true
% 15.73/2.51  --res_time_limit                        2.
% 15.73/2.51  --res_out_proof                         true
% 15.73/2.51  
% 15.73/2.51  ------ Superposition Options
% 15.73/2.51  
% 15.73/2.51  --superposition_flag                    true
% 15.73/2.51  --sup_passive_queue_type                priority_queues
% 15.73/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.73/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.73/2.51  --demod_completeness_check              fast
% 15.73/2.51  --demod_use_ground                      true
% 15.73/2.51  --sup_to_prop_solver                    passive
% 15.73/2.51  --sup_prop_simpl_new                    true
% 15.73/2.51  --sup_prop_simpl_given                  true
% 15.73/2.51  --sup_fun_splitting                     false
% 15.73/2.51  --sup_smt_interval                      50000
% 15.73/2.51  
% 15.73/2.51  ------ Superposition Simplification Setup
% 15.73/2.51  
% 15.73/2.51  --sup_indices_passive                   []
% 15.73/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.73/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.73/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.73/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.73/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.73/2.51  --sup_full_bw                           [BwDemod]
% 15.73/2.51  --sup_immed_triv                        [TrivRules]
% 15.73/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.73/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.73/2.51  --sup_immed_bw_main                     []
% 15.73/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.73/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.73/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.73/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.73/2.51  
% 15.73/2.51  ------ Combination Options
% 15.73/2.51  
% 15.73/2.51  --comb_res_mult                         3
% 15.73/2.51  --comb_sup_mult                         2
% 15.73/2.51  --comb_inst_mult                        10
% 15.73/2.51  
% 15.73/2.51  ------ Debug Options
% 15.73/2.51  
% 15.73/2.51  --dbg_backtrace                         false
% 15.73/2.51  --dbg_dump_prop_clauses                 false
% 15.73/2.51  --dbg_dump_prop_clauses_file            -
% 15.73/2.51  --dbg_out_stat                          false
% 15.73/2.51  ------ Parsing...
% 15.73/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.73/2.51  
% 15.73/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.73/2.51  
% 15.73/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.73/2.51  
% 15.73/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.73/2.51  ------ Proving...
% 15.73/2.51  ------ Problem Properties 
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  clauses                                 13
% 15.73/2.51  conjectures                             3
% 15.73/2.51  EPR                                     0
% 15.73/2.51  Horn                                    13
% 15.73/2.51  unary                                   6
% 15.73/2.51  binary                                  5
% 15.73/2.51  lits                                    23
% 15.73/2.51  lits eq                                 2
% 15.73/2.51  fd_pure                                 0
% 15.73/2.51  fd_pseudo                               0
% 15.73/2.51  fd_cond                                 0
% 15.73/2.51  fd_pseudo_cond                          0
% 15.73/2.51  AC symbols                              0
% 15.73/2.51  
% 15.73/2.51  ------ Schedule dynamic 5 is on 
% 15.73/2.51  
% 15.73/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  ------ 
% 15.73/2.51  Current options:
% 15.73/2.51  ------ 
% 15.73/2.51  
% 15.73/2.51  ------ Input Options
% 15.73/2.51  
% 15.73/2.51  --out_options                           all
% 15.73/2.51  --tptp_safe_out                         true
% 15.73/2.51  --problem_path                          ""
% 15.73/2.51  --include_path                          ""
% 15.73/2.51  --clausifier                            res/vclausify_rel
% 15.73/2.51  --clausifier_options                    --mode clausify
% 15.73/2.51  --stdin                                 false
% 15.73/2.51  --stats_out                             all
% 15.73/2.51  
% 15.73/2.51  ------ General Options
% 15.73/2.51  
% 15.73/2.51  --fof                                   false
% 15.73/2.51  --time_out_real                         305.
% 15.73/2.51  --time_out_virtual                      -1.
% 15.73/2.51  --symbol_type_check                     false
% 15.73/2.51  --clausify_out                          false
% 15.73/2.51  --sig_cnt_out                           false
% 15.73/2.51  --trig_cnt_out                          false
% 15.73/2.51  --trig_cnt_out_tolerance                1.
% 15.73/2.51  --trig_cnt_out_sk_spl                   false
% 15.73/2.51  --abstr_cl_out                          false
% 15.73/2.51  
% 15.73/2.51  ------ Global Options
% 15.73/2.51  
% 15.73/2.51  --schedule                              default
% 15.73/2.51  --add_important_lit                     false
% 15.73/2.51  --prop_solver_per_cl                    1000
% 15.73/2.51  --min_unsat_core                        false
% 15.73/2.51  --soft_assumptions                      false
% 15.73/2.51  --soft_lemma_size                       3
% 15.73/2.51  --prop_impl_unit_size                   0
% 15.73/2.51  --prop_impl_unit                        []
% 15.73/2.51  --share_sel_clauses                     true
% 15.73/2.51  --reset_solvers                         false
% 15.73/2.51  --bc_imp_inh                            [conj_cone]
% 15.73/2.51  --conj_cone_tolerance                   3.
% 15.73/2.51  --extra_neg_conj                        none
% 15.73/2.51  --large_theory_mode                     true
% 15.73/2.51  --prolific_symb_bound                   200
% 15.73/2.51  --lt_threshold                          2000
% 15.73/2.51  --clause_weak_htbl                      true
% 15.73/2.51  --gc_record_bc_elim                     false
% 15.73/2.51  
% 15.73/2.51  ------ Preprocessing Options
% 15.73/2.51  
% 15.73/2.51  --preprocessing_flag                    true
% 15.73/2.51  --time_out_prep_mult                    0.1
% 15.73/2.51  --splitting_mode                        input
% 15.73/2.51  --splitting_grd                         true
% 15.73/2.51  --splitting_cvd                         false
% 15.73/2.51  --splitting_cvd_svl                     false
% 15.73/2.51  --splitting_nvd                         32
% 15.73/2.51  --sub_typing                            true
% 15.73/2.51  --prep_gs_sim                           true
% 15.73/2.51  --prep_unflatten                        true
% 15.73/2.51  --prep_res_sim                          true
% 15.73/2.51  --prep_upred                            true
% 15.73/2.51  --prep_sem_filter                       exhaustive
% 15.73/2.51  --prep_sem_filter_out                   false
% 15.73/2.51  --pred_elim                             true
% 15.73/2.51  --res_sim_input                         true
% 15.73/2.51  --eq_ax_congr_red                       true
% 15.73/2.51  --pure_diseq_elim                       true
% 15.73/2.51  --brand_transform                       false
% 15.73/2.51  --non_eq_to_eq                          false
% 15.73/2.51  --prep_def_merge                        true
% 15.73/2.51  --prep_def_merge_prop_impl              false
% 15.73/2.51  --prep_def_merge_mbd                    true
% 15.73/2.51  --prep_def_merge_tr_red                 false
% 15.73/2.51  --prep_def_merge_tr_cl                  false
% 15.73/2.51  --smt_preprocessing                     true
% 15.73/2.51  --smt_ac_axioms                         fast
% 15.73/2.51  --preprocessed_out                      false
% 15.73/2.51  --preprocessed_stats                    false
% 15.73/2.51  
% 15.73/2.51  ------ Abstraction refinement Options
% 15.73/2.51  
% 15.73/2.51  --abstr_ref                             []
% 15.73/2.51  --abstr_ref_prep                        false
% 15.73/2.51  --abstr_ref_until_sat                   false
% 15.73/2.51  --abstr_ref_sig_restrict                funpre
% 15.73/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.73/2.51  --abstr_ref_under                       []
% 15.73/2.51  
% 15.73/2.51  ------ SAT Options
% 15.73/2.51  
% 15.73/2.51  --sat_mode                              false
% 15.73/2.51  --sat_fm_restart_options                ""
% 15.73/2.51  --sat_gr_def                            false
% 15.73/2.51  --sat_epr_types                         true
% 15.73/2.51  --sat_non_cyclic_types                  false
% 15.73/2.51  --sat_finite_models                     false
% 15.73/2.51  --sat_fm_lemmas                         false
% 15.73/2.51  --sat_fm_prep                           false
% 15.73/2.51  --sat_fm_uc_incr                        true
% 15.73/2.51  --sat_out_model                         small
% 15.73/2.51  --sat_out_clauses                       false
% 15.73/2.51  
% 15.73/2.51  ------ QBF Options
% 15.73/2.51  
% 15.73/2.51  --qbf_mode                              false
% 15.73/2.51  --qbf_elim_univ                         false
% 15.73/2.51  --qbf_dom_inst                          none
% 15.73/2.51  --qbf_dom_pre_inst                      false
% 15.73/2.51  --qbf_sk_in                             false
% 15.73/2.51  --qbf_pred_elim                         true
% 15.73/2.51  --qbf_split                             512
% 15.73/2.51  
% 15.73/2.51  ------ BMC1 Options
% 15.73/2.51  
% 15.73/2.51  --bmc1_incremental                      false
% 15.73/2.51  --bmc1_axioms                           reachable_all
% 15.73/2.51  --bmc1_min_bound                        0
% 15.73/2.51  --bmc1_max_bound                        -1
% 15.73/2.51  --bmc1_max_bound_default                -1
% 15.73/2.51  --bmc1_symbol_reachability              true
% 15.73/2.51  --bmc1_property_lemmas                  false
% 15.73/2.51  --bmc1_k_induction                      false
% 15.73/2.51  --bmc1_non_equiv_states                 false
% 15.73/2.51  --bmc1_deadlock                         false
% 15.73/2.51  --bmc1_ucm                              false
% 15.73/2.51  --bmc1_add_unsat_core                   none
% 15.73/2.51  --bmc1_unsat_core_children              false
% 15.73/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.73/2.51  --bmc1_out_stat                         full
% 15.73/2.51  --bmc1_ground_init                      false
% 15.73/2.51  --bmc1_pre_inst_next_state              false
% 15.73/2.51  --bmc1_pre_inst_state                   false
% 15.73/2.51  --bmc1_pre_inst_reach_state             false
% 15.73/2.51  --bmc1_out_unsat_core                   false
% 15.73/2.51  --bmc1_aig_witness_out                  false
% 15.73/2.51  --bmc1_verbose                          false
% 15.73/2.51  --bmc1_dump_clauses_tptp                false
% 15.73/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.73/2.51  --bmc1_dump_file                        -
% 15.73/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.73/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.73/2.51  --bmc1_ucm_extend_mode                  1
% 15.73/2.51  --bmc1_ucm_init_mode                    2
% 15.73/2.51  --bmc1_ucm_cone_mode                    none
% 15.73/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.73/2.51  --bmc1_ucm_relax_model                  4
% 15.73/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.73/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.73/2.51  --bmc1_ucm_layered_model                none
% 15.73/2.51  --bmc1_ucm_max_lemma_size               10
% 15.73/2.51  
% 15.73/2.51  ------ AIG Options
% 15.73/2.51  
% 15.73/2.51  --aig_mode                              false
% 15.73/2.51  
% 15.73/2.51  ------ Instantiation Options
% 15.73/2.51  
% 15.73/2.51  --instantiation_flag                    true
% 15.73/2.51  --inst_sos_flag                         false
% 15.73/2.51  --inst_sos_phase                        true
% 15.73/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.73/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.73/2.51  --inst_lit_sel_side                     none
% 15.73/2.51  --inst_solver_per_active                1400
% 15.73/2.51  --inst_solver_calls_frac                1.
% 15.73/2.51  --inst_passive_queue_type               priority_queues
% 15.73/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.73/2.51  --inst_passive_queues_freq              [25;2]
% 15.73/2.51  --inst_dismatching                      true
% 15.73/2.51  --inst_eager_unprocessed_to_passive     true
% 15.73/2.51  --inst_prop_sim_given                   true
% 15.73/2.51  --inst_prop_sim_new                     false
% 15.73/2.51  --inst_subs_new                         false
% 15.73/2.51  --inst_eq_res_simp                      false
% 15.73/2.51  --inst_subs_given                       false
% 15.73/2.51  --inst_orphan_elimination               true
% 15.73/2.51  --inst_learning_loop_flag               true
% 15.73/2.51  --inst_learning_start                   3000
% 15.73/2.51  --inst_learning_factor                  2
% 15.73/2.51  --inst_start_prop_sim_after_learn       3
% 15.73/2.51  --inst_sel_renew                        solver
% 15.73/2.51  --inst_lit_activity_flag                true
% 15.73/2.51  --inst_restr_to_given                   false
% 15.73/2.51  --inst_activity_threshold               500
% 15.73/2.51  --inst_out_proof                        true
% 15.73/2.51  
% 15.73/2.51  ------ Resolution Options
% 15.73/2.51  
% 15.73/2.51  --resolution_flag                       false
% 15.73/2.51  --res_lit_sel                           adaptive
% 15.73/2.51  --res_lit_sel_side                      none
% 15.73/2.51  --res_ordering                          kbo
% 15.73/2.51  --res_to_prop_solver                    active
% 15.73/2.51  --res_prop_simpl_new                    false
% 15.73/2.51  --res_prop_simpl_given                  true
% 15.73/2.51  --res_passive_queue_type                priority_queues
% 15.73/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.73/2.51  --res_passive_queues_freq               [15;5]
% 15.73/2.51  --res_forward_subs                      full
% 15.73/2.51  --res_backward_subs                     full
% 15.73/2.51  --res_forward_subs_resolution           true
% 15.73/2.51  --res_backward_subs_resolution          true
% 15.73/2.51  --res_orphan_elimination                true
% 15.73/2.51  --res_time_limit                        2.
% 15.73/2.51  --res_out_proof                         true
% 15.73/2.51  
% 15.73/2.51  ------ Superposition Options
% 15.73/2.51  
% 15.73/2.51  --superposition_flag                    true
% 15.73/2.51  --sup_passive_queue_type                priority_queues
% 15.73/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.73/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.73/2.51  --demod_completeness_check              fast
% 15.73/2.51  --demod_use_ground                      true
% 15.73/2.51  --sup_to_prop_solver                    passive
% 15.73/2.51  --sup_prop_simpl_new                    true
% 15.73/2.51  --sup_prop_simpl_given                  true
% 15.73/2.51  --sup_fun_splitting                     false
% 15.73/2.51  --sup_smt_interval                      50000
% 15.73/2.51  
% 15.73/2.51  ------ Superposition Simplification Setup
% 15.73/2.51  
% 15.73/2.51  --sup_indices_passive                   []
% 15.73/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.73/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.73/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.73/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.73/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.73/2.51  --sup_full_bw                           [BwDemod]
% 15.73/2.51  --sup_immed_triv                        [TrivRules]
% 15.73/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.73/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.73/2.51  --sup_immed_bw_main                     []
% 15.73/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.73/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.73/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.73/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.73/2.51  
% 15.73/2.51  ------ Combination Options
% 15.73/2.51  
% 15.73/2.51  --comb_res_mult                         3
% 15.73/2.51  --comb_sup_mult                         2
% 15.73/2.51  --comb_inst_mult                        10
% 15.73/2.51  
% 15.73/2.51  ------ Debug Options
% 15.73/2.51  
% 15.73/2.51  --dbg_backtrace                         false
% 15.73/2.51  --dbg_dump_prop_clauses                 false
% 15.73/2.51  --dbg_dump_prop_clauses_file            -
% 15.73/2.51  --dbg_out_stat                          false
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  ------ Proving...
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  % SZS status Theorem for theBenchmark.p
% 15.73/2.51  
% 15.73/2.51   Resolution empty clause
% 15.73/2.51  
% 15.73/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.73/2.51  
% 15.73/2.51  fof(f4,axiom,(
% 15.73/2.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f30,plain,(
% 15.73/2.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.73/2.51    inference(cnf_transformation,[],[f4])).
% 15.73/2.51  
% 15.73/2.51  fof(f3,axiom,(
% 15.73/2.51    ! [X0] : k2_subset_1(X0) = X0),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f29,plain,(
% 15.73/2.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.73/2.51    inference(cnf_transformation,[],[f3])).
% 15.73/2.51  
% 15.73/2.51  fof(f8,axiom,(
% 15.73/2.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f22,plain,(
% 15.73/2.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.73/2.51    inference(nnf_transformation,[],[f8])).
% 15.73/2.51  
% 15.73/2.51  fof(f34,plain,(
% 15.73/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.73/2.51    inference(cnf_transformation,[],[f22])).
% 15.73/2.51  
% 15.73/2.51  fof(f6,axiom,(
% 15.73/2.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f16,plain,(
% 15.73/2.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.73/2.51    inference(ennf_transformation,[],[f6])).
% 15.73/2.51  
% 15.73/2.51  fof(f32,plain,(
% 15.73/2.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.73/2.51    inference(cnf_transformation,[],[f16])).
% 15.73/2.51  
% 15.73/2.51  fof(f7,axiom,(
% 15.73/2.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f33,plain,(
% 15.73/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.73/2.51    inference(cnf_transformation,[],[f7])).
% 15.73/2.51  
% 15.73/2.51  fof(f44,plain,(
% 15.73/2.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.73/2.51    inference(definition_unfolding,[],[f32,f33])).
% 15.73/2.51  
% 15.73/2.51  fof(f35,plain,(
% 15.73/2.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.73/2.51    inference(cnf_transformation,[],[f22])).
% 15.73/2.51  
% 15.73/2.51  fof(f5,axiom,(
% 15.73/2.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f15,plain,(
% 15.73/2.51    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.73/2.51    inference(ennf_transformation,[],[f5])).
% 15.73/2.51  
% 15.73/2.51  fof(f31,plain,(
% 15.73/2.51    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.73/2.51    inference(cnf_transformation,[],[f15])).
% 15.73/2.51  
% 15.73/2.51  fof(f10,axiom,(
% 15.73/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f19,plain,(
% 15.73/2.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.73/2.51    inference(ennf_transformation,[],[f10])).
% 15.73/2.51  
% 15.73/2.51  fof(f20,plain,(
% 15.73/2.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.73/2.51    inference(flattening,[],[f19])).
% 15.73/2.51  
% 15.73/2.51  fof(f37,plain,(
% 15.73/2.51    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.73/2.51    inference(cnf_transformation,[],[f20])).
% 15.73/2.51  
% 15.73/2.51  fof(f11,conjecture,(
% 15.73/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f12,negated_conjecture,(
% 15.73/2.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 15.73/2.51    inference(negated_conjecture,[],[f11])).
% 15.73/2.51  
% 15.73/2.51  fof(f21,plain,(
% 15.73/2.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.73/2.51    inference(ennf_transformation,[],[f12])).
% 15.73/2.51  
% 15.73/2.51  fof(f25,plain,(
% 15.73/2.51    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.73/2.51    introduced(choice_axiom,[])).
% 15.73/2.51  
% 15.73/2.51  fof(f24,plain,(
% 15.73/2.51    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.73/2.51    introduced(choice_axiom,[])).
% 15.73/2.51  
% 15.73/2.51  fof(f23,plain,(
% 15.73/2.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.73/2.51    introduced(choice_axiom,[])).
% 15.73/2.51  
% 15.73/2.51  fof(f26,plain,(
% 15.73/2.51    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.73/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).
% 15.73/2.51  
% 15.73/2.51  fof(f38,plain,(
% 15.73/2.51    l1_pre_topc(sK0)),
% 15.73/2.51    inference(cnf_transformation,[],[f26])).
% 15.73/2.51  
% 15.73/2.51  fof(f2,axiom,(
% 15.73/2.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f13,plain,(
% 15.73/2.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 15.73/2.51    inference(ennf_transformation,[],[f2])).
% 15.73/2.51  
% 15.73/2.51  fof(f14,plain,(
% 15.73/2.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 15.73/2.51    inference(flattening,[],[f13])).
% 15.73/2.51  
% 15.73/2.51  fof(f28,plain,(
% 15.73/2.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.73/2.51    inference(cnf_transformation,[],[f14])).
% 15.73/2.51  
% 15.73/2.51  fof(f43,plain,(
% 15.73/2.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.73/2.51    inference(definition_unfolding,[],[f28,f33])).
% 15.73/2.51  
% 15.73/2.51  fof(f40,plain,(
% 15.73/2.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.73/2.51    inference(cnf_transformation,[],[f26])).
% 15.73/2.51  
% 15.73/2.51  fof(f9,axiom,(
% 15.73/2.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f17,plain,(
% 15.73/2.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.73/2.51    inference(ennf_transformation,[],[f9])).
% 15.73/2.51  
% 15.73/2.51  fof(f18,plain,(
% 15.73/2.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.73/2.51    inference(flattening,[],[f17])).
% 15.73/2.51  
% 15.73/2.51  fof(f36,plain,(
% 15.73/2.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.73/2.51    inference(cnf_transformation,[],[f18])).
% 15.73/2.51  
% 15.73/2.51  fof(f41,plain,(
% 15.73/2.51    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 15.73/2.51    inference(cnf_transformation,[],[f26])).
% 15.73/2.51  
% 15.73/2.51  fof(f39,plain,(
% 15.73/2.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.73/2.51    inference(cnf_transformation,[],[f26])).
% 15.73/2.51  
% 15.73/2.51  fof(f1,axiom,(
% 15.73/2.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.73/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.73/2.51  
% 15.73/2.51  fof(f27,plain,(
% 15.73/2.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.73/2.51    inference(cnf_transformation,[],[f1])).
% 15.73/2.51  
% 15.73/2.51  fof(f42,plain,(
% 15.73/2.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 15.73/2.51    inference(definition_unfolding,[],[f27,f33])).
% 15.73/2.51  
% 15.73/2.51  cnf(c_3,plain,
% 15.73/2.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.73/2.51      inference(cnf_transformation,[],[f30]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_652,plain,
% 15.73/2.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_2,plain,
% 15.73/2.51      ( k2_subset_1(X0) = X0 ),
% 15.73/2.51      inference(cnf_transformation,[],[f29]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_661,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.73/2.51      inference(light_normalisation,[status(thm)],[c_652,c_2]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_7,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.73/2.51      inference(cnf_transformation,[],[f34]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_650,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.73/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1260,plain,
% 15.73/2.51      ( r1_tarski(X0,X0) = iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_661,c_650]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_5,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.73/2.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 15.73/2.51      inference(cnf_transformation,[],[f44]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_6,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.73/2.51      inference(cnf_transformation,[],[f35]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_104,plain,
% 15.73/2.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.73/2.51      inference(prop_impl,[status(thm)],[c_6]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_105,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.73/2.51      inference(renaming,[status(thm)],[c_104]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_127,plain,
% 15.73/2.51      ( ~ r1_tarski(X0,X1)
% 15.73/2.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 15.73/2.51      inference(bin_hyper_res,[status(thm)],[c_5,c_105]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_645,plain,
% 15.73/2.51      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 15.73/2.51      | r1_tarski(X2,X0) != iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1524,plain,
% 15.73/2.51      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_1260,c_645]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_4,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.73/2.51      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 15.73/2.51      inference(cnf_transformation,[],[f31]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_126,plain,
% 15.73/2.51      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 15.73/2.51      | ~ r1_tarski(X2,X0) ),
% 15.73/2.51      inference(bin_hyper_res,[status(thm)],[c_4,c_105]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_646,plain,
% 15.73/2.51      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 15.73/2.51      | r1_tarski(X2,X0) != iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_4562,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
% 15.73/2.51      | r1_tarski(X1,X1) != iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_1524,c_646]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_58596,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 15.73/2.51      inference(forward_subsumption_resolution,[status(thm)],[c_4562,c_1260]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_58600,plain,
% 15.73/2.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_58596,c_650]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_9,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | ~ r1_tarski(X0,X2)
% 15.73/2.51      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 15.73/2.51      | ~ l1_pre_topc(X1) ),
% 15.73/2.51      inference(cnf_transformation,[],[f37]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_13,negated_conjecture,
% 15.73/2.51      ( l1_pre_topc(sK0) ),
% 15.73/2.51      inference(cnf_transformation,[],[f38]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_184,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | ~ r1_tarski(X0,X2)
% 15.73/2.51      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 15.73/2.51      | sK0 != X1 ),
% 15.73/2.51      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_185,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.73/2.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.73/2.51      | ~ r1_tarski(X1,X0)
% 15.73/2.51      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 15.73/2.51      inference(unflattening,[status(thm)],[c_184]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_644,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | r1_tarski(X1,X0) != iProver_top
% 15.73/2.51      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1,plain,
% 15.73/2.51      ( ~ r1_tarski(X0,X1)
% 15.73/2.51      | ~ r1_tarski(X0,X2)
% 15.73/2.51      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 15.73/2.51      inference(cnf_transformation,[],[f43]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_653,plain,
% 15.73/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.73/2.51      | r1_tarski(X0,X2) != iProver_top
% 15.73/2.51      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_11,negated_conjecture,
% 15.73/2.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.73/2.51      inference(cnf_transformation,[],[f40]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_648,plain,
% 15.73/2.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_8,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | ~ l1_pre_topc(X1) ),
% 15.73/2.51      inference(cnf_transformation,[],[f36]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_202,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.73/2.51      | sK0 != X1 ),
% 15.73/2.51      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_203,plain,
% 15.73/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.73/2.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.73/2.51      inference(unflattening,[status(thm)],[c_202]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_643,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1259,plain,
% 15.73/2.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_643,c_650]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_2055,plain,
% 15.73/2.51      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,X1)))
% 15.73/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_1259,c_645]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_6031,plain,
% 15.73/2.51      ( k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X0,k2_pre_topc(sK0,sK2))) ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_648,c_2055]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1257,plain,
% 15.73/2.51      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_648,c_650]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1528,plain,
% 15.73/2.51      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_1257,c_645]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_10,negated_conjecture,
% 15.73/2.51      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 15.73/2.51      inference(cnf_transformation,[],[f41]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_649,plain,
% 15.73/2.51      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_1769,plain,
% 15.73/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 15.73/2.51      inference(demodulation,[status(thm)],[c_1528,c_649]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_6187,plain,
% 15.73/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) != iProver_top ),
% 15.73/2.51      inference(demodulation,[status(thm)],[c_6031,c_1769]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_6765,plain,
% 15.73/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 15.73/2.51      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_653,c_6187]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_8998,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 15.73/2.51      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_644,c_6765]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_12,negated_conjecture,
% 15.73/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.73/2.51      inference(cnf_transformation,[],[f39]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_15,plain,
% 15.73/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_24474,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 15.73/2.51      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
% 15.73/2.51      inference(global_propositional_subsumption,[status(thm)],[c_8998,c_15]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_0,plain,
% 15.73/2.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 15.73/2.51      inference(cnf_transformation,[],[f42]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_654,plain,
% 15.73/2.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_2342,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.73/2.51      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_1528,c_646]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_9819,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.73/2.51      inference(global_propositional_subsumption,[status(thm)],[c_2342,c_1257]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_24481,plain,
% 15.73/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top ),
% 15.73/2.51      inference(forward_subsumption_resolution,
% 15.73/2.51                [status(thm)],
% 15.73/2.51                [c_24474,c_654,c_9819]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_24483,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_644,c_24481]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_16,plain,
% 15.73/2.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.73/2.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_24486,plain,
% 15.73/2.51      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.73/2.51      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 15.73/2.51      inference(global_propositional_subsumption,[status(thm)],[c_24483,c_16]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_24492,plain,
% 15.73/2.51      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 15.73/2.51      inference(forward_subsumption_resolution,[status(thm)],[c_24486,c_9819]) ).
% 15.73/2.51  
% 15.73/2.51  cnf(c_59160,plain,
% 15.73/2.51      ( $false ),
% 15.73/2.51      inference(superposition,[status(thm)],[c_58600,c_24492]) ).
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.73/2.51  
% 15.73/2.51  ------                               Statistics
% 15.73/2.51  
% 15.73/2.51  ------ General
% 15.73/2.51  
% 15.73/2.51  abstr_ref_over_cycles:                  0
% 15.73/2.51  abstr_ref_under_cycles:                 0
% 15.73/2.51  gc_basic_clause_elim:                   0
% 15.73/2.51  forced_gc_time:                         0
% 15.73/2.51  parsing_time:                           0.015
% 15.73/2.51  unif_index_cands_time:                  0.
% 15.73/2.51  unif_index_add_time:                    0.
% 15.73/2.51  orderings_time:                         0.
% 15.73/2.51  out_proof_time:                         0.015
% 15.73/2.51  total_time:                             1.795
% 15.73/2.51  num_of_symbols:                         44
% 15.73/2.51  num_of_terms:                           58787
% 15.73/2.51  
% 15.73/2.51  ------ Preprocessing
% 15.73/2.51  
% 15.73/2.51  num_of_splits:                          0
% 15.73/2.51  num_of_split_atoms:                     0
% 15.73/2.51  num_of_reused_defs:                     0
% 15.73/2.51  num_eq_ax_congr_red:                    9
% 15.73/2.51  num_of_sem_filtered_clauses:            1
% 15.73/2.51  num_of_subtypes:                        0
% 15.73/2.51  monotx_restored_types:                  0
% 15.73/2.51  sat_num_of_epr_types:                   0
% 15.73/2.51  sat_num_of_non_cyclic_types:            0
% 15.73/2.51  sat_guarded_non_collapsed_types:        0
% 15.73/2.51  num_pure_diseq_elim:                    0
% 15.73/2.51  simp_replaced_by:                       0
% 15.73/2.51  res_preprocessed:                       72
% 15.73/2.51  prep_upred:                             0
% 15.73/2.51  prep_unflattend:                        2
% 15.73/2.51  smt_new_axioms:                         0
% 15.73/2.51  pred_elim_cands:                        2
% 15.73/2.51  pred_elim:                              1
% 15.73/2.51  pred_elim_cl:                           1
% 15.73/2.51  pred_elim_cycles:                       3
% 15.73/2.51  merged_defs:                            8
% 15.73/2.51  merged_defs_ncl:                        0
% 15.73/2.51  bin_hyper_res:                          10
% 15.73/2.51  prep_cycles:                            4
% 15.73/2.51  pred_elim_time:                         0.002
% 15.73/2.51  splitting_time:                         0.
% 15.73/2.51  sem_filter_time:                        0.
% 15.73/2.51  monotx_time:                            0.001
% 15.73/2.51  subtype_inf_time:                       0.
% 15.73/2.51  
% 15.73/2.51  ------ Problem properties
% 15.73/2.51  
% 15.73/2.51  clauses:                                13
% 15.73/2.51  conjectures:                            3
% 15.73/2.51  epr:                                    0
% 15.73/2.51  horn:                                   13
% 15.73/2.51  ground:                                 3
% 15.73/2.51  unary:                                  6
% 15.73/2.51  binary:                                 5
% 15.73/2.51  lits:                                   23
% 15.73/2.51  lits_eq:                                2
% 15.73/2.51  fd_pure:                                0
% 15.73/2.51  fd_pseudo:                              0
% 15.73/2.51  fd_cond:                                0
% 15.73/2.51  fd_pseudo_cond:                         0
% 15.73/2.51  ac_symbols:                             0
% 15.73/2.51  
% 15.73/2.51  ------ Propositional Solver
% 15.73/2.51  
% 15.73/2.51  prop_solver_calls:                      34
% 15.73/2.51  prop_fast_solver_calls:                 1618
% 15.73/2.51  smt_solver_calls:                       0
% 15.73/2.51  smt_fast_solver_calls:                  0
% 15.73/2.51  prop_num_of_clauses:                    26179
% 15.73/2.51  prop_preprocess_simplified:             27359
% 15.73/2.51  prop_fo_subsumed:                       58
% 15.73/2.51  prop_solver_time:                       0.
% 15.73/2.51  smt_solver_time:                        0.
% 15.73/2.51  smt_fast_solver_time:                   0.
% 15.73/2.51  prop_fast_solver_time:                  0.
% 15.73/2.51  prop_unsat_core_time:                   0.
% 15.73/2.51  
% 15.73/2.51  ------ QBF
% 15.73/2.51  
% 15.73/2.51  qbf_q_res:                              0
% 15.73/2.51  qbf_num_tautologies:                    0
% 15.73/2.51  qbf_prep_cycles:                        0
% 15.73/2.51  
% 15.73/2.51  ------ BMC1
% 15.73/2.51  
% 15.73/2.51  bmc1_current_bound:                     -1
% 15.73/2.51  bmc1_last_solved_bound:                 -1
% 15.73/2.51  bmc1_unsat_core_size:                   -1
% 15.73/2.51  bmc1_unsat_core_parents_size:           -1
% 15.73/2.51  bmc1_merge_next_fun:                    0
% 15.73/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.73/2.51  
% 15.73/2.51  ------ Instantiation
% 15.73/2.51  
% 15.73/2.51  inst_num_of_clauses:                    5192
% 15.73/2.51  inst_num_in_passive:                    742
% 15.73/2.51  inst_num_in_active:                     2688
% 15.73/2.51  inst_num_in_unprocessed:                1762
% 15.73/2.51  inst_num_of_loops:                      2840
% 15.73/2.51  inst_num_of_learning_restarts:          0
% 15.73/2.51  inst_num_moves_active_passive:          150
% 15.73/2.51  inst_lit_activity:                      0
% 15.73/2.51  inst_lit_activity_moves:                1
% 15.73/2.51  inst_num_tautologies:                   0
% 15.73/2.51  inst_num_prop_implied:                  0
% 15.73/2.51  inst_num_existing_simplified:           0
% 15.73/2.51  inst_num_eq_res_simplified:             0
% 15.73/2.51  inst_num_child_elim:                    0
% 15.73/2.51  inst_num_of_dismatching_blockings:      2663
% 15.73/2.51  inst_num_of_non_proper_insts:           7608
% 15.73/2.51  inst_num_of_duplicates:                 0
% 15.73/2.51  inst_inst_num_from_inst_to_res:         0
% 15.73/2.51  inst_dismatching_checking_time:         0.
% 15.73/2.51  
% 15.73/2.51  ------ Resolution
% 15.73/2.51  
% 15.73/2.51  res_num_of_clauses:                     0
% 15.73/2.51  res_num_in_passive:                     0
% 15.73/2.51  res_num_in_active:                      0
% 15.73/2.51  res_num_of_loops:                       76
% 15.73/2.51  res_forward_subset_subsumed:            187
% 15.73/2.51  res_backward_subset_subsumed:           6
% 15.73/2.51  res_forward_subsumed:                   0
% 15.73/2.51  res_backward_subsumed:                  0
% 15.73/2.51  res_forward_subsumption_resolution:     0
% 15.73/2.51  res_backward_subsumption_resolution:    0
% 15.73/2.51  res_clause_to_clause_subsumption:       18493
% 15.73/2.51  res_orphan_elimination:                 0
% 15.73/2.51  res_tautology_del:                      327
% 15.73/2.51  res_num_eq_res_simplified:              0
% 15.73/2.51  res_num_sel_changes:                    0
% 15.73/2.51  res_moves_from_active_to_pass:          0
% 15.73/2.51  
% 15.73/2.51  ------ Superposition
% 15.73/2.51  
% 15.73/2.51  sup_time_total:                         0.
% 15.73/2.51  sup_time_generating:                    0.
% 15.73/2.51  sup_time_sim_full:                      0.
% 15.73/2.51  sup_time_sim_immed:                     0.
% 15.73/2.51  
% 15.73/2.51  sup_num_of_clauses:                     2822
% 15.73/2.51  sup_num_in_active:                      563
% 15.73/2.51  sup_num_in_passive:                     2259
% 15.73/2.51  sup_num_of_loops:                       566
% 15.73/2.51  sup_fw_superposition:                   2264
% 15.73/2.51  sup_bw_superposition:                   1273
% 15.73/2.51  sup_immediate_simplified:               444
% 15.73/2.51  sup_given_eliminated:                   0
% 15.73/2.51  comparisons_done:                       0
% 15.73/2.51  comparisons_avoided:                    0
% 15.73/2.51  
% 15.73/2.51  ------ Simplifications
% 15.73/2.51  
% 15.73/2.51  
% 15.73/2.51  sim_fw_subset_subsumed:                 30
% 15.73/2.51  sim_bw_subset_subsumed:                 25
% 15.73/2.51  sim_fw_subsumed:                        25
% 15.73/2.51  sim_bw_subsumed:                        16
% 15.73/2.51  sim_fw_subsumption_res:                 19
% 15.73/2.51  sim_bw_subsumption_res:                 0
% 15.73/2.51  sim_tautology_del:                      1
% 15.73/2.51  sim_eq_tautology_del:                   13
% 15.73/2.51  sim_eq_res_simp:                        0
% 15.73/2.51  sim_fw_demodulated:                     308
% 15.73/2.51  sim_bw_demodulated:                     9
% 15.73/2.51  sim_light_normalised:                   82
% 15.73/2.51  sim_joinable_taut:                      0
% 15.73/2.51  sim_joinable_simp:                      0
% 15.73/2.51  sim_ac_normalised:                      0
% 15.73/2.51  sim_smt_subsumption:                    0
% 15.73/2.51  
%------------------------------------------------------------------------------
