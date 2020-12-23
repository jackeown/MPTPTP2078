%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:01 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 590 expanded)
%              Number of clauses        :   62 ( 166 expanded)
%              Number of leaves         :   14 ( 172 expanded)
%              Depth                    :   19
%              Number of atoms          :  364 (3177 expanded)
%              Number of equality atoms :  126 ( 329 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_compts_1(X2,X0)
          & v2_compts_1(X1,X0)
          & v8_pre_topc(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_compts_1(sK2,X0)
        & v2_compts_1(X1,X0)
        & v8_pre_topc(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_compts_1(X2,X0)
            & v2_compts_1(sK1,X0)
            & v8_pre_topc(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_447,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_447,c_0])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k1_enumset1(X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_445,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1464,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_464,c_445])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1462,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_436,c_445])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_444,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1208,plain,
    ( r1_tarski(k9_subset_1(X0,X1,X2),X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_444])).

cnf(c_1592,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,sK2)),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_1208])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2889,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,sK2)),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1592,c_19])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_443,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1966,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_443])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,plain,
    ( v8_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_619,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_620,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v8_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_4080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1966,c_16,c_17,c_19,c_20,c_22,c_620])).

cnf(c_4081,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4080])).

cnf(c_1593,plain,
    ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_446])).

cnf(c_3059,plain,
    ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_19])).

cnf(c_7,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_441,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X2,X1) = iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3069,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) = iProver_top
    | v4_pre_topc(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,sK2)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_441])).

cnf(c_8381,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) = iProver_top
    | v4_pre_topc(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,sK2)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3069,c_16,c_17])).

cnf(c_8392,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,sK2)),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4081,c_8381])).

cnf(c_8430,plain,
    ( v2_compts_1(u1_struct_0(sK0),sK0) != iProver_top
    | v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_8392])).

cnf(c_2016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_446])).

cnf(c_2187,plain,
    ( m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2016,c_464])).

cnf(c_2188,plain,
    ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2187])).

cnf(c_2195,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2188,c_444])).

cnf(c_8431,plain,
    ( v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
    | v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_8392])).

cnf(c_9044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8430,c_19,c_22,c_8431])).

cnf(c_9045,plain,
    ( v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9044])).

cnf(c_9053,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_9045])).

cnf(c_8,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_440,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1590,plain,
    ( v2_compts_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1462,c_440])).

cnf(c_2003,plain,
    ( v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1464,c_1590])).

cnf(c_14511,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9053,c_2003])).

cnf(c_622,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_623,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v8_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_10,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14511,c_623,c_21,c_20,c_18,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.78/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.99  
% 3.78/0.99  ------  iProver source info
% 3.78/0.99  
% 3.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.99  git: non_committed_changes: false
% 3.78/0.99  git: last_make_outside_of_git: false
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 16
% 3.78/0.99  conjectures                             8
% 3.78/0.99  EPR                                     5
% 3.78/0.99  Horn                                    16
% 3.78/0.99  unary                                   10
% 3.78/0.99  binary                                  3
% 3.78/0.99  lits                                    37
% 3.78/0.99  lits eq                                 2
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 0
% 3.78/0.99  fd_pseudo_cond                          0
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Input Options Time Limit: Unbounded
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.78/0.99    inference(cnf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f15,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f5])).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.78/0.99    inference(definition_unfolding,[],[f34,f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f48,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(definition_unfolding,[],[f33,f47])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,conjecture,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f12,negated_conjecture,(
% 3.78/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.78/0.99    inference(negated_conjecture,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f12])).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.99    inference(flattening,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f4,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f14,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f4])).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f14])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f13,plain,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.78/0.99    inference(unused_predicate_definition_removal,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f16,plain,(
% 3.78/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.78/0.99    inference(ennf_transformation,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f17,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f18,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.99    inference(flattening,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f39,plain,(
% 3.78/0.99    v2_pre_topc(sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f40,plain,(
% 3.78/0.99    l1_pre_topc(sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    v8_pre_topc(sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f45,plain,(
% 3.78/0.99    v2_compts_1(sK2,sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.99    inference(flattening,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.99    inference(flattening,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f38,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f44,plain,(
% 3.78/0.99    v2_compts_1(sK1,sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f41,plain,(
% 3.78/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1,plain,
% 3.78/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_447,plain,
% 3.78/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_0,plain,
% 3.78/0.99      ( k2_subset_1(X0) = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_464,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_447,c_0]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | k1_setfam_1(k1_enumset1(X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_445,plain,
% 3.78/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1464,plain,
% 3.78/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_464,c_445]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_436,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1462,plain,
% 3.78/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_436,c_445]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_446,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_444,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1208,plain,
% 3.78/0.99      ( r1_tarski(k9_subset_1(X0,X1,X2),X0) = iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_446,c_444]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1592,plain,
% 3.78/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,sK2)),u1_struct_0(sK0)) = iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1462,c_1208]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2889,plain,
% 3.78/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,sK2)),u1_struct_0(sK0)) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1592,c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5,plain,
% 3.78/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.78/0.99      | ~ v4_pre_topc(X2,X1)
% 3.78/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/0.99      | ~ v2_pre_topc(X1)
% 3.78/0.99      | ~ l1_pre_topc(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_443,plain,
% 3.78/0.99      ( v4_pre_topc(X0,X1) != iProver_top
% 3.78/0.99      | v4_pre_topc(X2,X1) != iProver_top
% 3.78/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X0,X2),X1) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1966,plain,
% 3.78/0.99      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | v4_pre_topc(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(sK2,sK0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1462,c_443]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15,negated_conjecture,
% 3.78/0.99      ( v2_pre_topc(sK0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_16,plain,
% 3.78/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14,negated_conjecture,
% 3.78/0.99      ( l1_pre_topc(sK0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_17,plain,
% 3.78/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11,negated_conjecture,
% 3.78/0.99      ( v8_pre_topc(sK0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,plain,
% 3.78/0.99      ( v8_pre_topc(sK0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9,negated_conjecture,
% 3.78/0.99      ( v2_compts_1(sK2,sK0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_22,plain,
% 3.78/0.99      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6,plain,
% 3.78/0.99      ( ~ v2_compts_1(X0,X1)
% 3.78/0.99      | v4_pre_topc(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/0.99      | ~ v8_pre_topc(X1)
% 3.78/0.99      | ~ v2_pre_topc(X1)
% 3.78/0.99      | ~ l1_pre_topc(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_619,plain,
% 3.78/0.99      ( ~ v2_compts_1(sK2,sK0)
% 3.78/0.99      | v4_pre_topc(sK2,sK0)
% 3.78/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.78/0.99      | ~ v8_pre_topc(sK0)
% 3.78/0.99      | ~ v2_pre_topc(sK0)
% 3.78/0.99      | ~ l1_pre_topc(sK0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_620,plain,
% 3.78/0.99      ( v2_compts_1(sK2,sK0) != iProver_top
% 3.78/0.99      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | v8_pre_topc(sK0) != iProver_top
% 3.78/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4080,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | v4_pre_topc(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1966,c_16,c_17,c_19,c_20,c_22,c_620]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4081,plain,
% 3.78/0.99      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | v4_pre_topc(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_4080]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1593,plain,
% 3.78/0.99      ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1462,c_446]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3059,plain,
% 3.78/0.99      ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1593,c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( ~ v2_compts_1(X0,X1)
% 3.78/0.99      | v2_compts_1(X2,X1)
% 3.78/0.99      | ~ v4_pre_topc(X2,X1)
% 3.78/0.99      | ~ r1_tarski(X2,X0)
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/0.99      | ~ v2_pre_topc(X1)
% 3.78/0.99      | ~ l1_pre_topc(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_441,plain,
% 3.78/0.99      ( v2_compts_1(X0,X1) != iProver_top
% 3.78/0.99      | v2_compts_1(X2,X1) = iProver_top
% 3.78/0.99      | v4_pre_topc(X2,X1) != iProver_top
% 3.78/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.78/0.99      | v2_pre_topc(X1) != iProver_top
% 3.78/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3069,plain,
% 3.78/0.99      ( v2_compts_1(X0,sK0) != iProver_top
% 3.78/0.99      | v2_compts_1(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) != iProver_top
% 3.78/0.99      | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,sK2)),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.78/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3059,c_441]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8381,plain,
% 3.78/0.99      ( v2_compts_1(X0,sK0) != iProver_top
% 3.78/0.99      | v2_compts_1(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) != iProver_top
% 3.78/0.99      | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,sK2)),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_3069,c_16,c_17]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8392,plain,
% 3.78/0.99      ( v2_compts_1(X0,sK0) != iProver_top
% 3.78/0.99      | v2_compts_1(k1_setfam_1(k1_enumset1(X1,X1,sK2)),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(X1,sK0) != iProver_top
% 3.78/0.99      | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,sK2)),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4081,c_8381]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8430,plain,
% 3.78/0.99      ( v2_compts_1(u1_struct_0(sK0),sK0) != iProver_top
% 3.78/0.99      | v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2889,c_8392]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2016,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 3.78/0.99      | m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1464,c_446]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2187,plain,
% 3.78/0.99      ( m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_2016,c_464]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2188,plain,
% 3.78/0.99      ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_2187]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2195,plain,
% 3.78/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2188,c_444]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8431,plain,
% 3.78/0.99      ( v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
% 3.78/0.99      | v2_compts_1(sK2,sK0) != iProver_top
% 3.78/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2195,c_8392]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9044,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_8430,c_19,c_22,c_8431]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9045,plain,
% 3.78/0.99      ( v2_compts_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_9044]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9053,plain,
% 3.78/0.99      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.78/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1464,c_9045]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8,negated_conjecture,
% 3.78/0.99      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_440,plain,
% 3.78/0.99      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1590,plain,
% 3.78/0.99      ( v2_compts_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_1462,c_440]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2003,plain,
% 3.78/0.99      ( v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_1464,c_1590]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14511,plain,
% 3.78/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.78/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_9053,c_2003]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_622,plain,
% 3.78/0.99      ( ~ v2_compts_1(sK1,sK0)
% 3.78/0.99      | v4_pre_topc(sK1,sK0)
% 3.78/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.78/0.99      | ~ v8_pre_topc(sK0)
% 3.78/0.99      | ~ v2_pre_topc(sK0)
% 3.78/0.99      | ~ l1_pre_topc(sK0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_623,plain,
% 3.78/0.99      ( v2_compts_1(sK1,sK0) != iProver_top
% 3.78/0.99      | v4_pre_topc(sK1,sK0) = iProver_top
% 3.78/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.78/1.00      | v8_pre_topc(sK0) != iProver_top
% 3.78/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.78/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_10,negated_conjecture,
% 3.78/1.00      ( v2_compts_1(sK1,sK0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_21,plain,
% 3.78/1.00      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_13,negated_conjecture,
% 3.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.78/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_18,plain,
% 3.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(contradiction,plain,
% 3.78/1.00      ( $false ),
% 3.78/1.00      inference(minisat,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_14511,c_623,c_21,c_20,c_18,c_17,c_16]) ).
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  ------                               Statistics
% 3.78/1.00  
% 3.78/1.00  ------ Selected
% 3.78/1.00  
% 3.78/1.00  total_time:                             0.477
% 3.78/1.00  
%------------------------------------------------------------------------------
