%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:00 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 368 expanded)
%              Number of clauses        :   69 ( 116 expanded)
%              Number of leaves         :   13 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          :  433 (2067 expanded)
%              Number of equality atoms :  104 ( 146 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f22])).

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,
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

fof(f30,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29,f28,f27])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_850,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1381,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_854])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_135,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_135])).

cnf(c_169,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_136])).

cnf(c_847,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_3050,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1381,c_847])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_294,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_295,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_18])).

cnf(c_300,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_844,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_3504,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3050,c_844])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_243,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_244,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_248,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_18,c_17])).

cnf(c_960,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_961,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_3779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3504,c_22,c_25,c_961])).

cnf(c_3780,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3779])).

cnf(c_855,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_268,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_269,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_271,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_269,c_18])).

cnf(c_272,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_845,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_1538,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_845])).

cnf(c_1856,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_1538])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_856,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2788,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1856,c_856])).

cnf(c_2791,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_2788])).

cnf(c_2827,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2791,c_25])).

cnf(c_3789,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3780,c_2827])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_857,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3049,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_857,c_847])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_168,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_136])).

cnf(c_848,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_3088,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_848])).

cnf(c_5861,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3088,c_857])).

cnf(c_5865,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5861,c_854])).

cnf(c_8003,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3789,c_5865])).

cnf(c_11,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_853,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3500,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3050,c_853])).

cnf(c_8007,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8003,c_3500])).

cnf(c_963,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_964,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_13,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8007,c_964,c_24,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/1.00  
% 3.45/1.00  ------  iProver source info
% 3.45/1.00  
% 3.45/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.45/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/1.00  git: non_committed_changes: false
% 3.45/1.00  git: last_make_outside_of_git: false
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     num_symb
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       true
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  ------ Parsing...
% 3.45/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/1.00  ------ Proving...
% 3.45/1.00  ------ Problem Properties 
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  clauses                                 15
% 3.45/1.00  conjectures                             5
% 3.45/1.00  EPR                                     5
% 3.45/1.00  Horn                                    15
% 3.45/1.00  unary                                   6
% 3.45/1.00  binary                                  4
% 3.45/1.00  lits                                    34
% 3.45/1.00  lits eq                                 2
% 3.45/1.00  fd_pure                                 0
% 3.45/1.00  fd_pseudo                               0
% 3.45/1.00  fd_cond                                 0
% 3.45/1.00  fd_pseudo_cond                          1
% 3.45/1.00  AC symbols                              0
% 3.45/1.00  
% 3.45/1.00  ------ Schedule dynamic 5 is on 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ 
% 3.45/1.00  Current options:
% 3.45/1.00  ------ 
% 3.45/1.00  
% 3.45/1.00  ------ Input Options
% 3.45/1.00  
% 3.45/1.00  --out_options                           all
% 3.45/1.00  --tptp_safe_out                         true
% 3.45/1.00  --problem_path                          ""
% 3.45/1.00  --include_path                          ""
% 3.45/1.00  --clausifier                            res/vclausify_rel
% 3.45/1.00  --clausifier_options                    --mode clausify
% 3.45/1.00  --stdin                                 false
% 3.45/1.00  --stats_out                             all
% 3.45/1.00  
% 3.45/1.00  ------ General Options
% 3.45/1.00  
% 3.45/1.00  --fof                                   false
% 3.45/1.00  --time_out_real                         305.
% 3.45/1.00  --time_out_virtual                      -1.
% 3.45/1.00  --symbol_type_check                     false
% 3.45/1.00  --clausify_out                          false
% 3.45/1.00  --sig_cnt_out                           false
% 3.45/1.00  --trig_cnt_out                          false
% 3.45/1.00  --trig_cnt_out_tolerance                1.
% 3.45/1.00  --trig_cnt_out_sk_spl                   false
% 3.45/1.00  --abstr_cl_out                          false
% 3.45/1.00  
% 3.45/1.00  ------ Global Options
% 3.45/1.00  
% 3.45/1.00  --schedule                              default
% 3.45/1.00  --add_important_lit                     false
% 3.45/1.00  --prop_solver_per_cl                    1000
% 3.45/1.00  --min_unsat_core                        false
% 3.45/1.00  --soft_assumptions                      false
% 3.45/1.00  --soft_lemma_size                       3
% 3.45/1.00  --prop_impl_unit_size                   0
% 3.45/1.00  --prop_impl_unit                        []
% 3.45/1.00  --share_sel_clauses                     true
% 3.45/1.00  --reset_solvers                         false
% 3.45/1.00  --bc_imp_inh                            [conj_cone]
% 3.45/1.00  --conj_cone_tolerance                   3.
% 3.45/1.00  --extra_neg_conj                        none
% 3.45/1.00  --large_theory_mode                     true
% 3.45/1.00  --prolific_symb_bound                   200
% 3.45/1.00  --lt_threshold                          2000
% 3.45/1.00  --clause_weak_htbl                      true
% 3.45/1.00  --gc_record_bc_elim                     false
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing Options
% 3.45/1.00  
% 3.45/1.00  --preprocessing_flag                    true
% 3.45/1.00  --time_out_prep_mult                    0.1
% 3.45/1.00  --splitting_mode                        input
% 3.45/1.00  --splitting_grd                         true
% 3.45/1.00  --splitting_cvd                         false
% 3.45/1.00  --splitting_cvd_svl                     false
% 3.45/1.00  --splitting_nvd                         32
% 3.45/1.00  --sub_typing                            true
% 3.45/1.00  --prep_gs_sim                           true
% 3.45/1.00  --prep_unflatten                        true
% 3.45/1.00  --prep_res_sim                          true
% 3.45/1.00  --prep_upred                            true
% 3.45/1.00  --prep_sem_filter                       exhaustive
% 3.45/1.00  --prep_sem_filter_out                   false
% 3.45/1.00  --pred_elim                             true
% 3.45/1.00  --res_sim_input                         true
% 3.45/1.00  --eq_ax_congr_red                       true
% 3.45/1.00  --pure_diseq_elim                       true
% 3.45/1.00  --brand_transform                       false
% 3.45/1.00  --non_eq_to_eq                          false
% 3.45/1.00  --prep_def_merge                        true
% 3.45/1.00  --prep_def_merge_prop_impl              false
% 3.45/1.00  --prep_def_merge_mbd                    true
% 3.45/1.00  --prep_def_merge_tr_red                 false
% 3.45/1.00  --prep_def_merge_tr_cl                  false
% 3.45/1.00  --smt_preprocessing                     true
% 3.45/1.00  --smt_ac_axioms                         fast
% 3.45/1.00  --preprocessed_out                      false
% 3.45/1.00  --preprocessed_stats                    false
% 3.45/1.00  
% 3.45/1.00  ------ Abstraction refinement Options
% 3.45/1.00  
% 3.45/1.00  --abstr_ref                             []
% 3.45/1.00  --abstr_ref_prep                        false
% 3.45/1.00  --abstr_ref_until_sat                   false
% 3.45/1.00  --abstr_ref_sig_restrict                funpre
% 3.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.00  --abstr_ref_under                       []
% 3.45/1.00  
% 3.45/1.00  ------ SAT Options
% 3.45/1.00  
% 3.45/1.00  --sat_mode                              false
% 3.45/1.00  --sat_fm_restart_options                ""
% 3.45/1.00  --sat_gr_def                            false
% 3.45/1.00  --sat_epr_types                         true
% 3.45/1.00  --sat_non_cyclic_types                  false
% 3.45/1.00  --sat_finite_models                     false
% 3.45/1.00  --sat_fm_lemmas                         false
% 3.45/1.00  --sat_fm_prep                           false
% 3.45/1.00  --sat_fm_uc_incr                        true
% 3.45/1.00  --sat_out_model                         small
% 3.45/1.00  --sat_out_clauses                       false
% 3.45/1.00  
% 3.45/1.00  ------ QBF Options
% 3.45/1.00  
% 3.45/1.00  --qbf_mode                              false
% 3.45/1.00  --qbf_elim_univ                         false
% 3.45/1.00  --qbf_dom_inst                          none
% 3.45/1.00  --qbf_dom_pre_inst                      false
% 3.45/1.00  --qbf_sk_in                             false
% 3.45/1.00  --qbf_pred_elim                         true
% 3.45/1.00  --qbf_split                             512
% 3.45/1.00  
% 3.45/1.00  ------ BMC1 Options
% 3.45/1.00  
% 3.45/1.00  --bmc1_incremental                      false
% 3.45/1.00  --bmc1_axioms                           reachable_all
% 3.45/1.00  --bmc1_min_bound                        0
% 3.45/1.00  --bmc1_max_bound                        -1
% 3.45/1.00  --bmc1_max_bound_default                -1
% 3.45/1.00  --bmc1_symbol_reachability              true
% 3.45/1.00  --bmc1_property_lemmas                  false
% 3.45/1.00  --bmc1_k_induction                      false
% 3.45/1.00  --bmc1_non_equiv_states                 false
% 3.45/1.00  --bmc1_deadlock                         false
% 3.45/1.00  --bmc1_ucm                              false
% 3.45/1.00  --bmc1_add_unsat_core                   none
% 3.45/1.00  --bmc1_unsat_core_children              false
% 3.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.00  --bmc1_out_stat                         full
% 3.45/1.00  --bmc1_ground_init                      false
% 3.45/1.00  --bmc1_pre_inst_next_state              false
% 3.45/1.00  --bmc1_pre_inst_state                   false
% 3.45/1.00  --bmc1_pre_inst_reach_state             false
% 3.45/1.00  --bmc1_out_unsat_core                   false
% 3.45/1.00  --bmc1_aig_witness_out                  false
% 3.45/1.00  --bmc1_verbose                          false
% 3.45/1.00  --bmc1_dump_clauses_tptp                false
% 3.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.00  --bmc1_dump_file                        -
% 3.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.00  --bmc1_ucm_extend_mode                  1
% 3.45/1.00  --bmc1_ucm_init_mode                    2
% 3.45/1.00  --bmc1_ucm_cone_mode                    none
% 3.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.00  --bmc1_ucm_relax_model                  4
% 3.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.00  --bmc1_ucm_layered_model                none
% 3.45/1.00  --bmc1_ucm_max_lemma_size               10
% 3.45/1.00  
% 3.45/1.00  ------ AIG Options
% 3.45/1.00  
% 3.45/1.00  --aig_mode                              false
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation Options
% 3.45/1.00  
% 3.45/1.00  --instantiation_flag                    true
% 3.45/1.00  --inst_sos_flag                         false
% 3.45/1.00  --inst_sos_phase                        true
% 3.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.00  --inst_lit_sel_side                     none
% 3.45/1.00  --inst_solver_per_active                1400
% 3.45/1.00  --inst_solver_calls_frac                1.
% 3.45/1.00  --inst_passive_queue_type               priority_queues
% 3.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.00  --inst_passive_queues_freq              [25;2]
% 3.45/1.00  --inst_dismatching                      true
% 3.45/1.00  --inst_eager_unprocessed_to_passive     true
% 3.45/1.00  --inst_prop_sim_given                   true
% 3.45/1.00  --inst_prop_sim_new                     false
% 3.45/1.00  --inst_subs_new                         false
% 3.45/1.00  --inst_eq_res_simp                      false
% 3.45/1.00  --inst_subs_given                       false
% 3.45/1.00  --inst_orphan_elimination               true
% 3.45/1.00  --inst_learning_loop_flag               true
% 3.45/1.00  --inst_learning_start                   3000
% 3.45/1.00  --inst_learning_factor                  2
% 3.45/1.00  --inst_start_prop_sim_after_learn       3
% 3.45/1.00  --inst_sel_renew                        solver
% 3.45/1.00  --inst_lit_activity_flag                true
% 3.45/1.00  --inst_restr_to_given                   false
% 3.45/1.00  --inst_activity_threshold               500
% 3.45/1.00  --inst_out_proof                        true
% 3.45/1.00  
% 3.45/1.00  ------ Resolution Options
% 3.45/1.00  
% 3.45/1.00  --resolution_flag                       false
% 3.45/1.00  --res_lit_sel                           adaptive
% 3.45/1.00  --res_lit_sel_side                      none
% 3.45/1.00  --res_ordering                          kbo
% 3.45/1.00  --res_to_prop_solver                    active
% 3.45/1.00  --res_prop_simpl_new                    false
% 3.45/1.00  --res_prop_simpl_given                  true
% 3.45/1.00  --res_passive_queue_type                priority_queues
% 3.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.00  --res_passive_queues_freq               [15;5]
% 3.45/1.00  --res_forward_subs                      full
% 3.45/1.00  --res_backward_subs                     full
% 3.45/1.00  --res_forward_subs_resolution           true
% 3.45/1.00  --res_backward_subs_resolution          true
% 3.45/1.00  --res_orphan_elimination                true
% 3.45/1.00  --res_time_limit                        2.
% 3.45/1.00  --res_out_proof                         true
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Options
% 3.45/1.00  
% 3.45/1.00  --superposition_flag                    true
% 3.45/1.00  --sup_passive_queue_type                priority_queues
% 3.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.00  --demod_completeness_check              fast
% 3.45/1.00  --demod_use_ground                      true
% 3.45/1.00  --sup_to_prop_solver                    passive
% 3.45/1.00  --sup_prop_simpl_new                    true
% 3.45/1.00  --sup_prop_simpl_given                  true
% 3.45/1.00  --sup_fun_splitting                     false
% 3.45/1.00  --sup_smt_interval                      50000
% 3.45/1.00  
% 3.45/1.00  ------ Superposition Simplification Setup
% 3.45/1.00  
% 3.45/1.00  --sup_indices_passive                   []
% 3.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_full_bw                           [BwDemod]
% 3.45/1.00  --sup_immed_triv                        [TrivRules]
% 3.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_immed_bw_main                     []
% 3.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.00  
% 3.45/1.00  ------ Combination Options
% 3.45/1.00  
% 3.45/1.00  --comb_res_mult                         3
% 3.45/1.00  --comb_sup_mult                         2
% 3.45/1.00  --comb_inst_mult                        10
% 3.45/1.00  
% 3.45/1.00  ------ Debug Options
% 3.45/1.00  
% 3.45/1.00  --dbg_backtrace                         false
% 3.45/1.00  --dbg_dump_prop_clauses                 false
% 3.45/1.00  --dbg_dump_prop_clauses_file            -
% 3.45/1.00  --dbg_out_stat                          false
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  ------ Proving...
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS status Theorem for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  fof(f10,conjecture,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f11,negated_conjecture,(
% 3.45/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.45/1.00    inference(negated_conjecture,[],[f10])).
% 3.45/1.00  
% 3.45/1.00  fof(f22,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f11])).
% 3.45/1.00  
% 3.45/1.00  fof(f23,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f22])).
% 3.45/1.00  
% 3.45/1.00  fof(f29,plain,(
% 3.45/1.00    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f28,plain,(
% 3.45/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f27,plain,(
% 3.45/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f30,plain,(
% 3.45/1.00    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29,f28,f27])).
% 3.45/1.00  
% 3.45/1.00  fof(f46,plain,(
% 3.45/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f6,axiom,(
% 3.45/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f26,plain,(
% 3.45/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.45/1.00    inference(nnf_transformation,[],[f6])).
% 3.45/1.00  
% 3.45/1.00  fof(f38,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f26])).
% 3.45/1.00  
% 3.45/1.00  fof(f4,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f15,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f4])).
% 3.45/1.00  
% 3.45/1.00  fof(f36,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f15])).
% 3.45/1.00  
% 3.45/1.00  fof(f5,axiom,(
% 3.45/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f37,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f5])).
% 3.45/1.00  
% 3.45/1.00  fof(f51,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.45/1.00    inference(definition_unfolding,[],[f36,f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f39,plain,(
% 3.45/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f26])).
% 3.45/1.00  
% 3.45/1.00  fof(f7,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f16,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f7])).
% 3.45/1.00  
% 3.45/1.00  fof(f17,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f16])).
% 3.45/1.00  
% 3.45/1.00  fof(f40,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f17])).
% 3.45/1.00  
% 3.45/1.00  fof(f44,plain,(
% 3.45/1.00    l1_pre_topc(sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f43,plain,(
% 3.45/1.00    v2_pre_topc(sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f49,plain,(
% 3.45/1.00    v2_compts_1(sK2,sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f8,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f18,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f8])).
% 3.45/1.00  
% 3.45/1.00  fof(f19,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f18])).
% 3.45/1.00  
% 3.45/1.00  fof(f41,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f19])).
% 3.45/1.00  
% 3.45/1.00  fof(f47,plain,(
% 3.45/1.00    v8_pre_topc(sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f9,axiom,(
% 3.45/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f20,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f9])).
% 3.45/1.00  
% 3.45/1.00  fof(f21,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.45/1.00    inference(flattening,[],[f20])).
% 3.45/1.00  
% 3.45/1.00  fof(f42,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f2,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f12,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.45/1.00    inference(ennf_transformation,[],[f2])).
% 3.45/1.00  
% 3.45/1.00  fof(f13,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.45/1.00    inference(flattening,[],[f12])).
% 3.45/1.00  
% 3.45/1.00  fof(f34,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f13])).
% 3.45/1.00  
% 3.45/1.00  fof(f1,axiom,(
% 3.45/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f24,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(nnf_transformation,[],[f1])).
% 3.45/1.00  
% 3.45/1.00  fof(f25,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(flattening,[],[f24])).
% 3.45/1.00  
% 3.45/1.00  fof(f32,plain,(
% 3.45/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.45/1.00    inference(cnf_transformation,[],[f25])).
% 3.45/1.00  
% 3.45/1.00  fof(f52,plain,(
% 3.45/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.45/1.00    inference(equality_resolution,[],[f32])).
% 3.45/1.00  
% 3.45/1.00  fof(f3,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f14,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f3])).
% 3.45/1.00  
% 3.45/1.00  fof(f35,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f14])).
% 3.45/1.00  
% 3.45/1.00  fof(f50,plain,(
% 3.45/1.00    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f48,plain,(
% 3.45/1.00    v2_compts_1(sK1,sK0)),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f45,plain,(
% 3.45/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  cnf(c_15,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_850,plain,
% 3.45/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_854,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.45/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1381,plain,
% 3.45/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_850,c_854]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_135,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.45/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_136,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_135]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_169,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1)
% 3.45/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.45/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_136]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_847,plain,
% 3.45/1.00      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.45/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3050,plain,
% 3.45/1.00      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1381,c_847]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8,plain,
% 3.45/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.45/1.00      | ~ v4_pre_topc(X2,X1)
% 3.45/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_17,negated_conjecture,
% 3.45/1.00      ( l1_pre_topc(sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_294,plain,
% 3.45/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.45/1.00      | ~ v4_pre_topc(X2,X1)
% 3.45/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | sK0 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_295,plain,
% 3.45/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.45/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.45/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ v2_pre_topc(sK0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_294]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_18,negated_conjecture,
% 3.45/1.00      ( v2_pre_topc(sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_299,plain,
% 3.45/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.45/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.45/1.00      | ~ v4_pre_topc(X0,sK0) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_295,c_18]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_300,plain,
% 3.45/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.45/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.45/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_299]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_844,plain,
% 3.45/1.00      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(X1,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3504,plain,
% 3.45/1.00      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(sK2,sK0) != iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3050,c_844]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_22,plain,
% 3.45/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12,negated_conjecture,
% 3.45/1.00      ( v2_compts_1(sK2,sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_25,plain,
% 3.45/1.00      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,X1)
% 3.45/1.00      | v4_pre_topc(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ v8_pre_topc(X1)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_14,negated_conjecture,
% 3.45/1.00      ( v8_pre_topc(sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_243,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,X1)
% 3.45/1.00      | v4_pre_topc(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1)
% 3.45/1.00      | sK0 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_244,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.45/1.00      | v4_pre_topc(X0,sK0)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ v2_pre_topc(sK0)
% 3.45/1.00      | ~ l1_pre_topc(sK0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_243]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_248,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.45/1.00      | v4_pre_topc(X0,sK0)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_244,c_18,c_17]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_960,plain,
% 3.45/1.00      ( ~ v2_compts_1(sK2,sK0)
% 3.45/1.00      | v4_pre_topc(sK2,sK0)
% 3.45/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_248]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_961,plain,
% 3.45/1.00      ( v2_compts_1(sK2,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.45/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3779,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3504,c_22,c_25,c_961]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3780,plain,
% 3.45/1.00      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_3779]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_855,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.45/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,X1)
% 3.45/1.00      | v2_compts_1(X2,X1)
% 3.45/1.00      | ~ v4_pre_topc(X2,X1)
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ r1_tarski(X2,X0)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | ~ l1_pre_topc(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_268,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,X1)
% 3.45/1.00      | v2_compts_1(X2,X1)
% 3.45/1.00      | ~ v4_pre_topc(X2,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.45/1.00      | ~ r1_tarski(X2,X0)
% 3.45/1.00      | ~ v2_pre_topc(X1)
% 3.45/1.00      | sK0 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_269,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.45/1.00      | v2_compts_1(X1,sK0)
% 3.45/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ r1_tarski(X1,X0)
% 3.45/1.00      | ~ v2_pre_topc(sK0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_268]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_271,plain,
% 3.45/1.00      ( ~ r1_tarski(X1,X0)
% 3.45/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.45/1.00      | v2_compts_1(X1,sK0)
% 3.45/1.00      | ~ v2_compts_1(X0,sK0) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_269,c_18]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_272,plain,
% 3.45/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.45/1.00      | v2_compts_1(X1,sK0)
% 3.45/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.45/1.00      | ~ r1_tarski(X1,X0) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_271]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_845,plain,
% 3.45/1.00      ( v2_compts_1(X0,sK0) != iProver_top
% 3.45/1.00      | v2_compts_1(X1,sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X1,sK0) != iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1538,plain,
% 3.45/1.00      ( v2_compts_1(X0,sK0) != iProver_top
% 3.45/1.00      | v2_compts_1(X1,sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X1,sK0) != iProver_top
% 3.45/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.45/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_855,c_845]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1856,plain,
% 3.45/1.00      ( v2_compts_1(X0,sK0) != iProver_top
% 3.45/1.00      | v2_compts_1(X1,sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X1,sK0) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.45/1.00      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 3.45/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_855,c_1538]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.45/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_856,plain,
% 3.45/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.45/1.00      | r1_tarski(X0,X2) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2788,plain,
% 3.45/1.00      ( v2_compts_1(X0,sK0) != iProver_top
% 3.45/1.00      | v2_compts_1(X1,sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X1,sK0) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.45/1.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1856,c_856]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2791,plain,
% 3.45/1.00      ( v2_compts_1(X0,sK0) = iProver_top
% 3.45/1.00      | v2_compts_1(sK2,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | r1_tarski(X0,sK2) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1381,c_2788]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2827,plain,
% 3.45/1.00      ( v2_compts_1(X0,sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | r1_tarski(X0,sK2) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_2791,c_25]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3789,plain,
% 3.45/1.00      ( v2_compts_1(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.45/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK2) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3780,c_2827]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1,plain,
% 3.45/1.00      ( r1_tarski(X0,X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_857,plain,
% 3.45/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3049,plain,
% 3.45/1.00      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_857,c_847]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_168,plain,
% 3.45/1.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.45/1.00      | ~ r1_tarski(X2,X0) ),
% 3.45/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_136]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_848,plain,
% 3.45/1.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.45/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3088,plain,
% 3.45/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
% 3.45/1.00      | r1_tarski(X1,X1) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3049,c_848]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5861,plain,
% 3.45/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3088,c_857]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5865,plain,
% 3.45/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5861,c_854]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8003,plain,
% 3.45/1.00      ( v2_compts_1(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 3.45/1.00      | v4_pre_topc(X0,sK0) != iProver_top
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3789,c_5865]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11,negated_conjecture,
% 3.45/1.00      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_853,plain,
% 3.45/1.00      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3500,plain,
% 3.45/1.00      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3050,c_853]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8007,plain,
% 3.45/1.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.45/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8003,c_3500]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_963,plain,
% 3.45/1.00      ( ~ v2_compts_1(sK1,sK0)
% 3.45/1.00      | v4_pre_topc(sK1,sK0)
% 3.45/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_248]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_964,plain,
% 3.45/1.00      ( v2_compts_1(sK1,sK0) != iProver_top
% 3.45/1.00      | v4_pre_topc(sK1,sK0) = iProver_top
% 3.45/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13,negated_conjecture,
% 3.45/1.00      ( v2_compts_1(sK1,sK0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_24,plain,
% 3.45/1.00      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_16,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_21,plain,
% 3.45/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(contradiction,plain,
% 3.45/1.00      ( $false ),
% 3.45/1.00      inference(minisat,[status(thm)],[c_8007,c_964,c_24,c_21]) ).
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  ------                               Statistics
% 3.45/1.00  
% 3.45/1.00  ------ General
% 3.45/1.00  
% 3.45/1.00  abstr_ref_over_cycles:                  0
% 3.45/1.00  abstr_ref_under_cycles:                 0
% 3.45/1.00  gc_basic_clause_elim:                   0
% 3.45/1.00  forced_gc_time:                         0
% 3.45/1.00  parsing_time:                           0.01
% 3.45/1.00  unif_index_cands_time:                  0.
% 3.45/1.00  unif_index_add_time:                    0.
% 3.45/1.00  orderings_time:                         0.
% 3.45/1.00  out_proof_time:                         0.013
% 3.45/1.00  total_time:                             0.352
% 3.45/1.00  num_of_symbols:                         46
% 3.45/1.00  num_of_terms:                           7161
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing
% 3.45/1.00  
% 3.45/1.00  num_of_splits:                          0
% 3.45/1.00  num_of_split_atoms:                     0
% 3.45/1.00  num_of_reused_defs:                     0
% 3.45/1.00  num_eq_ax_congr_red:                    13
% 3.45/1.00  num_of_sem_filtered_clauses:            1
% 3.45/1.00  num_of_subtypes:                        0
% 3.45/1.00  monotx_restored_types:                  0
% 3.45/1.00  sat_num_of_epr_types:                   0
% 3.45/1.00  sat_num_of_non_cyclic_types:            0
% 3.45/1.00  sat_guarded_non_collapsed_types:        0
% 3.45/1.00  num_pure_diseq_elim:                    0
% 3.45/1.00  simp_replaced_by:                       0
% 3.45/1.00  res_preprocessed:                       82
% 3.45/1.00  prep_upred:                             0
% 3.45/1.00  prep_unflattend:                        3
% 3.45/1.00  smt_new_axioms:                         0
% 3.45/1.00  pred_elim_cands:                        4
% 3.45/1.00  pred_elim:                              3
% 3.45/1.00  pred_elim_cl:                           3
% 3.45/1.00  pred_elim_cycles:                       5
% 3.45/1.00  merged_defs:                            8
% 3.45/1.00  merged_defs_ncl:                        0
% 3.45/1.00  bin_hyper_res:                          10
% 3.45/1.00  prep_cycles:                            4
% 3.45/1.00  pred_elim_time:                         0.002
% 3.45/1.00  splitting_time:                         0.
% 3.45/1.00  sem_filter_time:                        0.
% 3.45/1.00  monotx_time:                            0.001
% 3.45/1.00  subtype_inf_time:                       0.
% 3.45/1.00  
% 3.45/1.00  ------ Problem properties
% 3.45/1.00  
% 3.45/1.00  clauses:                                15
% 3.45/1.00  conjectures:                            5
% 3.45/1.00  epr:                                    5
% 3.45/1.00  horn:                                   15
% 3.45/1.00  ground:                                 5
% 3.45/1.00  unary:                                  6
% 3.45/1.00  binary:                                 4
% 3.45/1.00  lits:                                   34
% 3.45/1.00  lits_eq:                                2
% 3.45/1.00  fd_pure:                                0
% 3.45/1.00  fd_pseudo:                              0
% 3.45/1.00  fd_cond:                                0
% 3.45/1.00  fd_pseudo_cond:                         1
% 3.45/1.00  ac_symbols:                             0
% 3.45/1.00  
% 3.45/1.00  ------ Propositional Solver
% 3.45/1.00  
% 3.45/1.00  prop_solver_calls:                      30
% 3.45/1.00  prop_fast_solver_calls:                 790
% 3.45/1.00  smt_solver_calls:                       0
% 3.45/1.00  smt_fast_solver_calls:                  0
% 3.45/1.00  prop_num_of_clauses:                    2857
% 3.45/1.00  prop_preprocess_simplified:             5369
% 3.45/1.00  prop_fo_subsumed:                       23
% 3.45/1.00  prop_solver_time:                       0.
% 3.45/1.00  smt_solver_time:                        0.
% 3.45/1.00  smt_fast_solver_time:                   0.
% 3.45/1.00  prop_fast_solver_time:                  0.
% 3.45/1.00  prop_unsat_core_time:                   0.
% 3.45/1.00  
% 3.45/1.00  ------ QBF
% 3.45/1.00  
% 3.45/1.00  qbf_q_res:                              0
% 3.45/1.00  qbf_num_tautologies:                    0
% 3.45/1.00  qbf_prep_cycles:                        0
% 3.45/1.00  
% 3.45/1.00  ------ BMC1
% 3.45/1.00  
% 3.45/1.00  bmc1_current_bound:                     -1
% 3.45/1.00  bmc1_last_solved_bound:                 -1
% 3.45/1.00  bmc1_unsat_core_size:                   -1
% 3.45/1.00  bmc1_unsat_core_parents_size:           -1
% 3.45/1.00  bmc1_merge_next_fun:                    0
% 3.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation
% 3.45/1.00  
% 3.45/1.00  inst_num_of_clauses:                    813
% 3.45/1.00  inst_num_in_passive:                    8
% 3.45/1.00  inst_num_in_active:                     419
% 3.45/1.00  inst_num_in_unprocessed:                386
% 3.45/1.00  inst_num_of_loops:                      470
% 3.45/1.00  inst_num_of_learning_restarts:          0
% 3.45/1.00  inst_num_moves_active_passive:          47
% 3.45/1.00  inst_lit_activity:                      0
% 3.45/1.00  inst_lit_activity_moves:                1
% 3.45/1.00  inst_num_tautologies:                   0
% 3.45/1.00  inst_num_prop_implied:                  0
% 3.45/1.00  inst_num_existing_simplified:           0
% 3.45/1.00  inst_num_eq_res_simplified:             0
% 3.45/1.00  inst_num_child_elim:                    0
% 3.45/1.00  inst_num_of_dismatching_blockings:      173
% 3.45/1.00  inst_num_of_non_proper_insts:           1163
% 3.45/1.00  inst_num_of_duplicates:                 0
% 3.45/1.00  inst_inst_num_from_inst_to_res:         0
% 3.45/1.00  inst_dismatching_checking_time:         0.
% 3.45/1.00  
% 3.45/1.00  ------ Resolution
% 3.45/1.00  
% 3.45/1.00  res_num_of_clauses:                     0
% 3.45/1.00  res_num_in_passive:                     0
% 3.45/1.00  res_num_in_active:                      0
% 3.45/1.00  res_num_of_loops:                       86
% 3.45/1.00  res_forward_subset_subsumed:            37
% 3.45/1.00  res_backward_subset_subsumed:           4
% 3.45/1.00  res_forward_subsumed:                   0
% 3.45/1.00  res_backward_subsumed:                  0
% 3.45/1.00  res_forward_subsumption_resolution:     0
% 3.45/1.00  res_backward_subsumption_resolution:    0
% 3.45/1.00  res_clause_to_clause_subsumption:       1648
% 3.45/1.00  res_orphan_elimination:                 0
% 3.45/1.00  res_tautology_del:                      51
% 3.45/1.00  res_num_eq_res_simplified:              0
% 3.45/1.00  res_num_sel_changes:                    0
% 3.45/1.00  res_moves_from_active_to_pass:          0
% 3.45/1.00  
% 3.45/1.00  ------ Superposition
% 3.45/1.00  
% 3.45/1.00  sup_time_total:                         0.
% 3.45/1.00  sup_time_generating:                    0.
% 3.45/1.00  sup_time_sim_full:                      0.
% 3.45/1.00  sup_time_sim_immed:                     0.
% 3.45/1.00  
% 3.45/1.00  sup_num_of_clauses:                     210
% 3.45/1.00  sup_num_in_active:                      92
% 3.45/1.00  sup_num_in_passive:                     118
% 3.45/1.00  sup_num_of_loops:                       93
% 3.45/1.00  sup_fw_superposition:                   202
% 3.45/1.00  sup_bw_superposition:                   145
% 3.45/1.00  sup_immediate_simplified:               90
% 3.45/1.00  sup_given_eliminated:                   0
% 3.45/1.00  comparisons_done:                       0
% 3.45/1.00  comparisons_avoided:                    0
% 3.45/1.00  
% 3.45/1.00  ------ Simplifications
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  sim_fw_subset_subsumed:                 30
% 3.45/1.00  sim_bw_subset_subsumed:                 18
% 3.45/1.00  sim_fw_subsumed:                        27
% 3.45/1.00  sim_bw_subsumed:                        0
% 3.45/1.00  sim_fw_subsumption_res:                 4
% 3.45/1.00  sim_bw_subsumption_res:                 0
% 3.45/1.00  sim_tautology_del:                      3
% 3.45/1.00  sim_eq_tautology_del:                   7
% 3.45/1.00  sim_eq_res_simp:                        0
% 3.45/1.00  sim_fw_demodulated:                     23
% 3.45/1.00  sim_bw_demodulated:                     1
% 3.45/1.00  sim_light_normalised:                   10
% 3.45/1.00  sim_joinable_taut:                      0
% 3.45/1.00  sim_joinable_simp:                      0
% 3.45/1.00  sim_ac_normalised:                      0
% 3.45/1.00  sim_smt_subsumption:                    0
% 3.45/1.00  
%------------------------------------------------------------------------------
