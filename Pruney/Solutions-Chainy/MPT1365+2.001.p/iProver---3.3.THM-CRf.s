%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:57 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 275 expanded)
%              Number of clauses        :   60 (  77 expanded)
%              Number of leaves         :   13 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  385 (1730 expanded)
%              Number of equality atoms :   27 (  35 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28,f27])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
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
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3016,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4354,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_10287,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4354])).

cnf(c_474,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1731,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_2100,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_4594,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_2100])).

cnf(c_6785,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4594])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2858,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5260,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_1266,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1540,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_2242,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_1540])).

cnf(c_4080,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2242])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_134,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_135,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_135])).

cnf(c_2827,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_858,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_863,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1378,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_863])).

cnf(c_1380,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1378])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_859,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1377,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_863])).

cnf(c_1379,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1377])).

cnf(c_1328,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

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

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_267,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_268,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_270,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_18])).

cnf(c_271,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_913,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_1091,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_293,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_294,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_18])).

cnf(c_299,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_919,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,sK2),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_957,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_919])).

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

cnf(c_242,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_243,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_247,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_18,c_17])).

cnf(c_899,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_896,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_11,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10287,c_6785,c_5260,c_4080,c_2827,c_1380,c_1379,c_1328,c_1091,c_957,c_899,c_896,c_11,c_12,c_13,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    ""
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             all
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         305.
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/1.00  --trig_cnt_out                          false
% 3.64/1.00  --trig_cnt_out_tolerance                1.
% 3.64/1.00  --trig_cnt_out_sk_spl                   false
% 3.64/1.00  --abstr_cl_out                          false
% 3.64/1.00  
% 3.64/1.00  ------ Global Options
% 3.64/1.00  
% 3.64/1.00  --schedule                              default
% 3.64/1.00  --add_important_lit                     false
% 3.64/1.00  --prop_solver_per_cl                    1000
% 3.64/1.00  --min_unsat_core                        false
% 3.64/1.00  --soft_assumptions                      false
% 3.64/1.00  --soft_lemma_size                       3
% 3.64/1.00  --prop_impl_unit_size                   0
% 3.64/1.00  --prop_impl_unit                        []
% 3.64/1.00  --share_sel_clauses                     true
% 3.64/1.00  --reset_solvers                         false
% 3.64/1.00  --bc_imp_inh                            [conj_cone]
% 3.64/1.00  --conj_cone_tolerance                   3.
% 3.64/1.00  --extra_neg_conj                        none
% 3.64/1.00  --large_theory_mode                     true
% 3.64/1.00  --prolific_symb_bound                   200
% 3.64/1.00  --lt_threshold                          2000
% 3.64/1.00  --clause_weak_htbl                      true
% 3.64/1.00  --gc_record_bc_elim                     false
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing Options
% 3.64/1.00  
% 3.64/1.00  --preprocessing_flag                    true
% 3.64/1.00  --time_out_prep_mult                    0.1
% 3.64/1.00  --splitting_mode                        input
% 3.64/1.00  --splitting_grd                         true
% 3.64/1.00  --splitting_cvd                         false
% 3.64/1.00  --splitting_cvd_svl                     false
% 3.64/1.00  --splitting_nvd                         32
% 3.64/1.00  --sub_typing                            true
% 3.64/1.00  --prep_gs_sim                           true
% 3.64/1.00  --prep_unflatten                        true
% 3.64/1.00  --prep_res_sim                          true
% 3.64/1.00  --prep_upred                            true
% 3.64/1.00  --prep_sem_filter                       exhaustive
% 3.64/1.00  --prep_sem_filter_out                   false
% 3.64/1.00  --pred_elim                             true
% 3.64/1.00  --res_sim_input                         true
% 3.64/1.00  --eq_ax_congr_red                       true
% 3.64/1.00  --pure_diseq_elim                       true
% 3.64/1.00  --brand_transform                       false
% 3.64/1.00  --non_eq_to_eq                          false
% 3.64/1.00  --prep_def_merge                        true
% 3.64/1.00  --prep_def_merge_prop_impl              false
% 3.64/1.00  --prep_def_merge_mbd                    true
% 3.64/1.00  --prep_def_merge_tr_red                 false
% 3.64/1.00  --prep_def_merge_tr_cl                  false
% 3.64/1.00  --smt_preprocessing                     true
% 3.64/1.00  --smt_ac_axioms                         fast
% 3.64/1.00  --preprocessed_out                      false
% 3.64/1.00  --preprocessed_stats                    false
% 3.64/1.00  
% 3.64/1.00  ------ Abstraction refinement Options
% 3.64/1.00  
% 3.64/1.00  --abstr_ref                             []
% 3.64/1.00  --abstr_ref_prep                        false
% 3.64/1.00  --abstr_ref_until_sat                   false
% 3.64/1.00  --abstr_ref_sig_restrict                funpre
% 3.64/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/1.00  --abstr_ref_under                       []
% 3.64/1.00  
% 3.64/1.00  ------ SAT Options
% 3.64/1.00  
% 3.64/1.00  --sat_mode                              false
% 3.64/1.00  --sat_fm_restart_options                ""
% 3.64/1.00  --sat_gr_def                            false
% 3.64/1.00  --sat_epr_types                         true
% 3.64/1.00  --sat_non_cyclic_types                  false
% 3.64/1.00  --sat_finite_models                     false
% 3.64/1.00  --sat_fm_lemmas                         false
% 3.64/1.00  --sat_fm_prep                           false
% 3.64/1.00  --sat_fm_uc_incr                        true
% 3.64/1.00  --sat_out_model                         small
% 3.64/1.00  --sat_out_clauses                       false
% 3.64/1.00  
% 3.64/1.00  ------ QBF Options
% 3.64/1.00  
% 3.64/1.00  --qbf_mode                              false
% 3.64/1.00  --qbf_elim_univ                         false
% 3.64/1.00  --qbf_dom_inst                          none
% 3.64/1.00  --qbf_dom_pre_inst                      false
% 3.64/1.00  --qbf_sk_in                             false
% 3.64/1.00  --qbf_pred_elim                         true
% 3.64/1.00  --qbf_split                             512
% 3.64/1.00  
% 3.64/1.00  ------ BMC1 Options
% 3.64/1.00  
% 3.64/1.00  --bmc1_incremental                      false
% 3.64/1.00  --bmc1_axioms                           reachable_all
% 3.64/1.00  --bmc1_min_bound                        0
% 3.64/1.00  --bmc1_max_bound                        -1
% 3.64/1.00  --bmc1_max_bound_default                -1
% 3.64/1.00  --bmc1_symbol_reachability              true
% 3.64/1.00  --bmc1_property_lemmas                  false
% 3.64/1.00  --bmc1_k_induction                      false
% 3.64/1.00  --bmc1_non_equiv_states                 false
% 3.64/1.00  --bmc1_deadlock                         false
% 3.64/1.00  --bmc1_ucm                              false
% 3.64/1.00  --bmc1_add_unsat_core                   none
% 3.64/1.00  --bmc1_unsat_core_children              false
% 3.64/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/1.00  --bmc1_out_stat                         full
% 3.64/1.00  --bmc1_ground_init                      false
% 3.64/1.00  --bmc1_pre_inst_next_state              false
% 3.64/1.00  --bmc1_pre_inst_state                   false
% 3.64/1.00  --bmc1_pre_inst_reach_state             false
% 3.64/1.00  --bmc1_out_unsat_core                   false
% 3.64/1.00  --bmc1_aig_witness_out                  false
% 3.64/1.00  --bmc1_verbose                          false
% 3.64/1.00  --bmc1_dump_clauses_tptp                false
% 3.64/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.64/1.00  --bmc1_dump_file                        -
% 3.64/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.64/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.64/1.00  --bmc1_ucm_extend_mode                  1
% 3.64/1.00  --bmc1_ucm_init_mode                    2
% 3.64/1.00  --bmc1_ucm_cone_mode                    none
% 3.64/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.64/1.00  --bmc1_ucm_relax_model                  4
% 3.64/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.64/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/1.00  --bmc1_ucm_layered_model                none
% 3.64/1.00  --bmc1_ucm_max_lemma_size               10
% 3.64/1.00  
% 3.64/1.00  ------ AIG Options
% 3.64/1.00  
% 3.64/1.00  --aig_mode                              false
% 3.64/1.00  
% 3.64/1.00  ------ Instantiation Options
% 3.64/1.00  
% 3.64/1.00  --instantiation_flag                    true
% 3.64/1.00  --inst_sos_flag                         true
% 3.64/1.00  --inst_sos_phase                        true
% 3.64/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel_side                     num_symb
% 3.64/1.00  --inst_solver_per_active                1400
% 3.64/1.00  --inst_solver_calls_frac                1.
% 3.64/1.00  --inst_passive_queue_type               priority_queues
% 3.64/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/1.00  --inst_passive_queues_freq              [25;2]
% 3.64/1.00  --inst_dismatching                      true
% 3.64/1.00  --inst_eager_unprocessed_to_passive     true
% 3.64/1.00  --inst_prop_sim_given                   true
% 3.64/1.00  --inst_prop_sim_new                     false
% 3.64/1.00  --inst_subs_new                         false
% 3.64/1.00  --inst_eq_res_simp                      false
% 3.64/1.00  --inst_subs_given                       false
% 3.64/1.00  --inst_orphan_elimination               true
% 3.64/1.00  --inst_learning_loop_flag               true
% 3.64/1.00  --inst_learning_start                   3000
% 3.64/1.00  --inst_learning_factor                  2
% 3.64/1.00  --inst_start_prop_sim_after_learn       3
% 3.64/1.00  --inst_sel_renew                        solver
% 3.64/1.00  --inst_lit_activity_flag                true
% 3.64/1.00  --inst_restr_to_given                   false
% 3.64/1.00  --inst_activity_threshold               500
% 3.64/1.00  --inst_out_proof                        true
% 3.64/1.00  
% 3.64/1.00  ------ Resolution Options
% 3.64/1.00  
% 3.64/1.00  --resolution_flag                       true
% 3.64/1.00  --res_lit_sel                           adaptive
% 3.64/1.00  --res_lit_sel_side                      none
% 3.64/1.00  --res_ordering                          kbo
% 3.64/1.00  --res_to_prop_solver                    active
% 3.64/1.00  --res_prop_simpl_new                    false
% 3.64/1.00  --res_prop_simpl_given                  true
% 3.64/1.00  --res_passive_queue_type                priority_queues
% 3.64/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/1.00  --res_passive_queues_freq               [15;5]
% 3.64/1.00  --res_forward_subs                      full
% 3.64/1.00  --res_backward_subs                     full
% 3.64/1.00  --res_forward_subs_resolution           true
% 3.64/1.00  --res_backward_subs_resolution          true
% 3.64/1.00  --res_orphan_elimination                true
% 3.64/1.00  --res_time_limit                        2.
% 3.64/1.00  --res_out_proof                         true
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Options
% 3.64/1.00  
% 3.64/1.00  --superposition_flag                    true
% 3.64/1.00  --sup_passive_queue_type                priority_queues
% 3.64/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.64/1.00  --demod_completeness_check              fast
% 3.64/1.00  --demod_use_ground                      true
% 3.64/1.00  --sup_to_prop_solver                    passive
% 3.64/1.00  --sup_prop_simpl_new                    true
% 3.64/1.00  --sup_prop_simpl_given                  true
% 3.64/1.00  --sup_fun_splitting                     true
% 3.64/1.00  --sup_smt_interval                      50000
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Simplification Setup
% 3.64/1.00  
% 3.64/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.64/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_immed_triv                        [TrivRules]
% 3.64/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_bw_main                     []
% 3.64/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_input_bw                          []
% 3.64/1.00  
% 3.64/1.00  ------ Combination Options
% 3.64/1.00  
% 3.64/1.00  --comb_res_mult                         3
% 3.64/1.00  --comb_sup_mult                         2
% 3.64/1.00  --comb_inst_mult                        10
% 3.64/1.00  
% 3.64/1.00  ------ Debug Options
% 3.64/1.00  
% 3.64/1.00  --dbg_backtrace                         false
% 3.64/1.00  --dbg_dump_prop_clauses                 false
% 3.64/1.00  --dbg_dump_prop_clauses_file            -
% 3.64/1.00  --dbg_out_stat                          false
% 3.64/1.00  ------ Parsing...
% 3.64/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  ------ Proving...
% 3.64/1.00  ------ Problem Properties 
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  clauses                                 16
% 3.64/1.00  conjectures                             5
% 3.64/1.00  EPR                                     2
% 3.64/1.00  Horn                                    16
% 3.64/1.00  unary                                   7
% 3.64/1.00  binary                                  6
% 3.64/1.00  lits                                    33
% 3.64/1.00  lits eq                                 4
% 3.64/1.00  fd_pure                                 0
% 3.64/1.00  fd_pseudo                               0
% 3.64/1.00  fd_cond                                 0
% 3.64/1.00  fd_pseudo_cond                          0
% 3.64/1.00  AC symbols                              0
% 3.64/1.00  
% 3.64/1.00  ------ Schedule dynamic 5 is on 
% 3.64/1.00  
% 3.64/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ 
% 3.64/1.00  Current options:
% 3.64/1.00  ------ 
% 3.64/1.00  
% 3.64/1.00  ------ Input Options
% 3.64/1.00  
% 3.64/1.00  --out_options                           all
% 3.64/1.00  --tptp_safe_out                         true
% 3.64/1.00  --problem_path                          ""
% 3.64/1.00  --include_path                          ""
% 3.64/1.00  --clausifier                            res/vclausify_rel
% 3.64/1.00  --clausifier_options                    ""
% 3.64/1.00  --stdin                                 false
% 3.64/1.00  --stats_out                             all
% 3.64/1.00  
% 3.64/1.00  ------ General Options
% 3.64/1.00  
% 3.64/1.00  --fof                                   false
% 3.64/1.00  --time_out_real                         305.
% 3.64/1.00  --time_out_virtual                      -1.
% 3.64/1.00  --symbol_type_check                     false
% 3.64/1.00  --clausify_out                          false
% 3.64/1.00  --sig_cnt_out                           false
% 3.64/1.00  --trig_cnt_out                          false
% 3.64/1.00  --trig_cnt_out_tolerance                1.
% 3.64/1.00  --trig_cnt_out_sk_spl                   false
% 3.64/1.00  --abstr_cl_out                          false
% 3.64/1.00  
% 3.64/1.00  ------ Global Options
% 3.64/1.00  
% 3.64/1.00  --schedule                              default
% 3.64/1.00  --add_important_lit                     false
% 3.64/1.00  --prop_solver_per_cl                    1000
% 3.64/1.00  --min_unsat_core                        false
% 3.64/1.00  --soft_assumptions                      false
% 3.64/1.00  --soft_lemma_size                       3
% 3.64/1.00  --prop_impl_unit_size                   0
% 3.64/1.00  --prop_impl_unit                        []
% 3.64/1.00  --share_sel_clauses                     true
% 3.64/1.00  --reset_solvers                         false
% 3.64/1.00  --bc_imp_inh                            [conj_cone]
% 3.64/1.00  --conj_cone_tolerance                   3.
% 3.64/1.00  --extra_neg_conj                        none
% 3.64/1.00  --large_theory_mode                     true
% 3.64/1.00  --prolific_symb_bound                   200
% 3.64/1.00  --lt_threshold                          2000
% 3.64/1.00  --clause_weak_htbl                      true
% 3.64/1.00  --gc_record_bc_elim                     false
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing Options
% 3.64/1.00  
% 3.64/1.00  --preprocessing_flag                    true
% 3.64/1.00  --time_out_prep_mult                    0.1
% 3.64/1.00  --splitting_mode                        input
% 3.64/1.00  --splitting_grd                         true
% 3.64/1.00  --splitting_cvd                         false
% 3.64/1.00  --splitting_cvd_svl                     false
% 3.64/1.00  --splitting_nvd                         32
% 3.64/1.00  --sub_typing                            true
% 3.64/1.00  --prep_gs_sim                           true
% 3.64/1.00  --prep_unflatten                        true
% 3.64/1.00  --prep_res_sim                          true
% 3.64/1.00  --prep_upred                            true
% 3.64/1.00  --prep_sem_filter                       exhaustive
% 3.64/1.00  --prep_sem_filter_out                   false
% 3.64/1.00  --pred_elim                             true
% 3.64/1.00  --res_sim_input                         true
% 3.64/1.00  --eq_ax_congr_red                       true
% 3.64/1.00  --pure_diseq_elim                       true
% 3.64/1.00  --brand_transform                       false
% 3.64/1.00  --non_eq_to_eq                          false
% 3.64/1.00  --prep_def_merge                        true
% 3.64/1.00  --prep_def_merge_prop_impl              false
% 3.64/1.00  --prep_def_merge_mbd                    true
% 3.64/1.00  --prep_def_merge_tr_red                 false
% 3.64/1.00  --prep_def_merge_tr_cl                  false
% 3.64/1.00  --smt_preprocessing                     true
% 3.64/1.00  --smt_ac_axioms                         fast
% 3.64/1.00  --preprocessed_out                      false
% 3.64/1.00  --preprocessed_stats                    false
% 3.64/1.00  
% 3.64/1.00  ------ Abstraction refinement Options
% 3.64/1.00  
% 3.64/1.00  --abstr_ref                             []
% 3.64/1.00  --abstr_ref_prep                        false
% 3.64/1.00  --abstr_ref_until_sat                   false
% 3.64/1.00  --abstr_ref_sig_restrict                funpre
% 3.64/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/1.00  --abstr_ref_under                       []
% 3.64/1.00  
% 3.64/1.00  ------ SAT Options
% 3.64/1.00  
% 3.64/1.00  --sat_mode                              false
% 3.64/1.00  --sat_fm_restart_options                ""
% 3.64/1.00  --sat_gr_def                            false
% 3.64/1.00  --sat_epr_types                         true
% 3.64/1.00  --sat_non_cyclic_types                  false
% 3.64/1.00  --sat_finite_models                     false
% 3.64/1.00  --sat_fm_lemmas                         false
% 3.64/1.00  --sat_fm_prep                           false
% 3.64/1.00  --sat_fm_uc_incr                        true
% 3.64/1.00  --sat_out_model                         small
% 3.64/1.00  --sat_out_clauses                       false
% 3.64/1.00  
% 3.64/1.00  ------ QBF Options
% 3.64/1.00  
% 3.64/1.00  --qbf_mode                              false
% 3.64/1.00  --qbf_elim_univ                         false
% 3.64/1.00  --qbf_dom_inst                          none
% 3.64/1.00  --qbf_dom_pre_inst                      false
% 3.64/1.00  --qbf_sk_in                             false
% 3.64/1.00  --qbf_pred_elim                         true
% 3.64/1.00  --qbf_split                             512
% 3.64/1.00  
% 3.64/1.00  ------ BMC1 Options
% 3.64/1.00  
% 3.64/1.00  --bmc1_incremental                      false
% 3.64/1.00  --bmc1_axioms                           reachable_all
% 3.64/1.00  --bmc1_min_bound                        0
% 3.64/1.00  --bmc1_max_bound                        -1
% 3.64/1.00  --bmc1_max_bound_default                -1
% 3.64/1.00  --bmc1_symbol_reachability              true
% 3.64/1.00  --bmc1_property_lemmas                  false
% 3.64/1.00  --bmc1_k_induction                      false
% 3.64/1.00  --bmc1_non_equiv_states                 false
% 3.64/1.00  --bmc1_deadlock                         false
% 3.64/1.00  --bmc1_ucm                              false
% 3.64/1.00  --bmc1_add_unsat_core                   none
% 3.64/1.00  --bmc1_unsat_core_children              false
% 3.64/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/1.00  --bmc1_out_stat                         full
% 3.64/1.00  --bmc1_ground_init                      false
% 3.64/1.00  --bmc1_pre_inst_next_state              false
% 3.64/1.00  --bmc1_pre_inst_state                   false
% 3.64/1.00  --bmc1_pre_inst_reach_state             false
% 3.64/1.00  --bmc1_out_unsat_core                   false
% 3.64/1.00  --bmc1_aig_witness_out                  false
% 3.64/1.00  --bmc1_verbose                          false
% 3.64/1.00  --bmc1_dump_clauses_tptp                false
% 3.64/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.64/1.00  --bmc1_dump_file                        -
% 3.64/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.64/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.64/1.00  --bmc1_ucm_extend_mode                  1
% 3.64/1.00  --bmc1_ucm_init_mode                    2
% 3.64/1.00  --bmc1_ucm_cone_mode                    none
% 3.64/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.64/1.00  --bmc1_ucm_relax_model                  4
% 3.64/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.64/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/1.00  --bmc1_ucm_layered_model                none
% 3.64/1.00  --bmc1_ucm_max_lemma_size               10
% 3.64/1.00  
% 3.64/1.00  ------ AIG Options
% 3.64/1.00  
% 3.64/1.00  --aig_mode                              false
% 3.64/1.00  
% 3.64/1.00  ------ Instantiation Options
% 3.64/1.00  
% 3.64/1.00  --instantiation_flag                    true
% 3.64/1.00  --inst_sos_flag                         true
% 3.64/1.00  --inst_sos_phase                        true
% 3.64/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel_side                     none
% 3.64/1.00  --inst_solver_per_active                1400
% 3.64/1.00  --inst_solver_calls_frac                1.
% 3.64/1.00  --inst_passive_queue_type               priority_queues
% 3.64/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/1.00  --inst_passive_queues_freq              [25;2]
% 3.64/1.00  --inst_dismatching                      true
% 3.64/1.00  --inst_eager_unprocessed_to_passive     true
% 3.64/1.00  --inst_prop_sim_given                   true
% 3.64/1.00  --inst_prop_sim_new                     false
% 3.64/1.00  --inst_subs_new                         false
% 3.64/1.00  --inst_eq_res_simp                      false
% 3.64/1.00  --inst_subs_given                       false
% 3.64/1.00  --inst_orphan_elimination               true
% 3.64/1.00  --inst_learning_loop_flag               true
% 3.64/1.00  --inst_learning_start                   3000
% 3.64/1.00  --inst_learning_factor                  2
% 3.64/1.00  --inst_start_prop_sim_after_learn       3
% 3.64/1.00  --inst_sel_renew                        solver
% 3.64/1.00  --inst_lit_activity_flag                true
% 3.64/1.00  --inst_restr_to_given                   false
% 3.64/1.00  --inst_activity_threshold               500
% 3.64/1.00  --inst_out_proof                        true
% 3.64/1.00  
% 3.64/1.00  ------ Resolution Options
% 3.64/1.00  
% 3.64/1.00  --resolution_flag                       false
% 3.64/1.00  --res_lit_sel                           adaptive
% 3.64/1.00  --res_lit_sel_side                      none
% 3.64/1.00  --res_ordering                          kbo
% 3.64/1.00  --res_to_prop_solver                    active
% 3.64/1.00  --res_prop_simpl_new                    false
% 3.64/1.00  --res_prop_simpl_given                  true
% 3.64/1.00  --res_passive_queue_type                priority_queues
% 3.64/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/1.00  --res_passive_queues_freq               [15;5]
% 3.64/1.00  --res_forward_subs                      full
% 3.64/1.00  --res_backward_subs                     full
% 3.64/1.00  --res_forward_subs_resolution           true
% 3.64/1.00  --res_backward_subs_resolution          true
% 3.64/1.00  --res_orphan_elimination                true
% 3.64/1.00  --res_time_limit                        2.
% 3.64/1.00  --res_out_proof                         true
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Options
% 3.64/1.00  
% 3.64/1.00  --superposition_flag                    true
% 3.64/1.00  --sup_passive_queue_type                priority_queues
% 3.64/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.64/1.00  --demod_completeness_check              fast
% 3.64/1.00  --demod_use_ground                      true
% 3.64/1.00  --sup_to_prop_solver                    passive
% 3.64/1.00  --sup_prop_simpl_new                    true
% 3.64/1.00  --sup_prop_simpl_given                  true
% 3.64/1.00  --sup_fun_splitting                     true
% 3.64/1.00  --sup_smt_interval                      50000
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Simplification Setup
% 3.64/1.00  
% 3.64/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.64/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_immed_triv                        [TrivRules]
% 3.64/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_bw_main                     []
% 3.64/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_input_bw                          []
% 3.64/1.00  
% 3.64/1.00  ------ Combination Options
% 3.64/1.00  
% 3.64/1.00  --comb_res_mult                         3
% 3.64/1.00  --comb_sup_mult                         2
% 3.64/1.00  --comb_inst_mult                        10
% 3.64/1.00  
% 3.64/1.00  ------ Debug Options
% 3.64/1.00  
% 3.64/1.00  --dbg_backtrace                         false
% 3.64/1.00  --dbg_dump_prop_clauses                 false
% 3.64/1.00  --dbg_dump_prop_clauses_file            -
% 3.64/1.00  --dbg_out_stat                          false
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS status Theorem for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  fof(f1,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f14,plain,(
% 3.64/1.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f1])).
% 3.64/1.00  
% 3.64/1.00  fof(f31,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f14])).
% 3.64/1.00  
% 3.64/1.00  fof(f7,axiom,(
% 3.64/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f37,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f7])).
% 3.64/1.00  
% 3.64/1.00  fof(f51,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f31,f37])).
% 3.64/1.00  
% 3.64/1.00  fof(f2,axiom,(
% 3.64/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f32,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f2])).
% 3.64/1.00  
% 3.64/1.00  fof(f52,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f32,f37])).
% 3.64/1.00  
% 3.64/1.00  fof(f6,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f17,plain,(
% 3.64/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.64/1.00    inference(ennf_transformation,[],[f6])).
% 3.64/1.00  
% 3.64/1.00  fof(f36,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f17])).
% 3.64/1.00  
% 3.64/1.00  fof(f54,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.64/1.00    inference(definition_unfolding,[],[f36,f37])).
% 3.64/1.00  
% 3.64/1.00  fof(f8,axiom,(
% 3.64/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f26,plain,(
% 3.64/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.64/1.00    inference(nnf_transformation,[],[f8])).
% 3.64/1.00  
% 3.64/1.00  fof(f39,plain,(
% 3.64/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f26])).
% 3.64/1.00  
% 3.64/1.00  fof(f12,conjecture,(
% 3.64/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f13,negated_conjecture,(
% 3.64/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.64/1.00    inference(negated_conjecture,[],[f12])).
% 3.64/1.00  
% 3.64/1.00  fof(f24,plain,(
% 3.64/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.64/1.00    inference(ennf_transformation,[],[f13])).
% 3.64/1.00  
% 3.64/1.00  fof(f25,plain,(
% 3.64/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.64/1.00    inference(flattening,[],[f24])).
% 3.64/1.00  
% 3.64/1.00  fof(f29,plain,(
% 3.64/1.00    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.64/1.00    introduced(choice_axiom,[])).
% 3.64/1.00  
% 3.64/1.00  fof(f28,plain,(
% 3.64/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.64/1.00    introduced(choice_axiom,[])).
% 3.64/1.00  
% 3.64/1.00  fof(f27,plain,(
% 3.64/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.64/1.00    introduced(choice_axiom,[])).
% 3.64/1.00  
% 3.64/1.00  fof(f30,plain,(
% 3.64/1.00    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28,f27])).
% 3.64/1.00  
% 3.64/1.00  fof(f45,plain,(
% 3.64/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f38,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f26])).
% 3.64/1.00  
% 3.64/1.00  fof(f46,plain,(
% 3.64/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f11,axiom,(
% 3.64/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f22,plain,(
% 3.64/1.00    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.64/1.00    inference(ennf_transformation,[],[f11])).
% 3.64/1.00  
% 3.64/1.00  fof(f23,plain,(
% 3.64/1.00    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.64/1.00    inference(flattening,[],[f22])).
% 3.64/1.00  
% 3.64/1.00  fof(f42,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f23])).
% 3.64/1.00  
% 3.64/1.00  fof(f44,plain,(
% 3.64/1.00    l1_pre_topc(sK0)),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f43,plain,(
% 3.64/1.00    v2_pre_topc(sK0)),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f9,axiom,(
% 3.64/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f18,plain,(
% 3.64/1.00    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.64/1.00    inference(ennf_transformation,[],[f9])).
% 3.64/1.00  
% 3.64/1.00  fof(f19,plain,(
% 3.64/1.00    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.64/1.00    inference(flattening,[],[f18])).
% 3.64/1.00  
% 3.64/1.00  fof(f40,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f19])).
% 3.64/1.00  
% 3.64/1.00  fof(f10,axiom,(
% 3.64/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f20,plain,(
% 3.64/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.64/1.00    inference(ennf_transformation,[],[f10])).
% 3.64/1.00  
% 3.64/1.00  fof(f21,plain,(
% 3.64/1.00    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.64/1.00    inference(flattening,[],[f20])).
% 3.64/1.00  
% 3.64/1.00  fof(f41,plain,(
% 3.64/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f21])).
% 3.64/1.00  
% 3.64/1.00  fof(f47,plain,(
% 3.64/1.00    v8_pre_topc(sK0)),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f50,plain,(
% 3.64/1.00    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f49,plain,(
% 3.64/1.00    v2_compts_1(sK2,sK0)),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  fof(f48,plain,(
% 3.64/1.00    v2_compts_1(sK1,sK0)),
% 3.64/1.00    inference(cnf_transformation,[],[f30])).
% 3.64/1.00  
% 3.64/1.00  cnf(c_0,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,X1)
% 3.64/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_3016,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 3.64/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4354,plain,
% 3.64/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
% 3.64/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_3016]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_10287,plain,
% 3.64/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 3.64/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_4354]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_474,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.64/1.00      theory(equality) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1731,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 3.64/1.00      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_474]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2100,plain,
% 3.64/1.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 3.64/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),u1_struct_0(sK0))
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_1731]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4594,plain,
% 3.64/1.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 3.64/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,X0)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_2100]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6785,plain,
% 3.64/1.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 3.64/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_4594]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1,plain,
% 3.64/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2858,plain,
% 3.64/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5260,plain,
% 3.64/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_2858]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1266,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,sK1)
% 3.64/1.00      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_474]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1540,plain,
% 3.64/1.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 3.64/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1)
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_1266]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2242,plain,
% 3.64/1.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 3.64/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),sK1)
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,X0)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_1540]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4080,plain,
% 3.64/1.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 3.64/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_2242]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5,plain,
% 3.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.64/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6,plain,
% 3.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_134,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.64/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_135,plain,
% 3.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.64/1.00      inference(renaming,[status(thm)],[c_134]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_167,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,X1)
% 3.64/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.64/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_135]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2827,plain,
% 3.64/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 3.64/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_167]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_16,negated_conjecture,
% 3.64/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_858,plain,
% 3.64/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7,plain,
% 3.64/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_863,plain,
% 3.64/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.64/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1378,plain,
% 3.64/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_858,c_863]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1380,plain,
% 3.64/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.64/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1378]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_15,negated_conjecture,
% 3.64/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_859,plain,
% 3.64/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1377,plain,
% 3.64/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_859,c_863]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1379,plain,
% 3.64/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.64/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1377]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1328,plain,
% 3.64/1.00      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_10,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,X1)
% 3.64/1.00      | v2_compts_1(X2,X1)
% 3.64/1.00      | ~ v4_pre_topc(X2,X1)
% 3.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ r1_tarski(X2,X0)
% 3.64/1.00      | ~ v2_pre_topc(X1)
% 3.64/1.00      | ~ l1_pre_topc(X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_17,negated_conjecture,
% 3.64/1.00      ( l1_pre_topc(sK0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_267,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,X1)
% 3.64/1.00      | v2_compts_1(X2,X1)
% 3.64/1.00      | ~ v4_pre_topc(X2,X1)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ r1_tarski(X2,X0)
% 3.64/1.00      | ~ v2_pre_topc(X1)
% 3.64/1.00      | sK0 != X1 ),
% 3.64/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_268,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.64/1.00      | v2_compts_1(X1,sK0)
% 3.64/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ r1_tarski(X1,X0)
% 3.64/1.00      | ~ v2_pre_topc(sK0) ),
% 3.64/1.00      inference(unflattening,[status(thm)],[c_267]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_18,negated_conjecture,
% 3.64/1.00      ( v2_pre_topc(sK0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_270,plain,
% 3.64/1.00      ( ~ r1_tarski(X1,X0)
% 3.64/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.64/1.00      | v2_compts_1(X1,sK0)
% 3.64/1.00      | ~ v2_compts_1(X0,sK0) ),
% 3.64/1.00      inference(global_propositional_subsumption,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_268,c_18]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_271,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.64/1.00      | v2_compts_1(X1,sK0)
% 3.64/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ r1_tarski(X1,X0) ),
% 3.64/1.00      inference(renaming,[status(thm)],[c_270]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_913,plain,
% 3.64/1.00      ( v2_compts_1(X0,sK0)
% 3.64/1.00      | ~ v2_compts_1(sK1,sK0)
% 3.64/1.00      | ~ v4_pre_topc(X0,sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ r1_tarski(X0,sK1) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_271]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1091,plain,
% 3.64/1.00      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 3.64/1.00      | ~ v2_compts_1(sK1,sK0)
% 3.64/1.00      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 3.64/1.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_913]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_8,plain,
% 3.64/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.64/1.00      | ~ v4_pre_topc(X2,X1)
% 3.64/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ v2_pre_topc(X1)
% 3.64/1.00      | ~ l1_pre_topc(X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_293,plain,
% 3.64/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.64/1.00      | ~ v4_pre_topc(X2,X1)
% 3.64/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ v2_pre_topc(X1)
% 3.64/1.00      | sK0 != X1 ),
% 3.64/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_294,plain,
% 3.64/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.64/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.64/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ v2_pre_topc(sK0) ),
% 3.64/1.00      inference(unflattening,[status(thm)],[c_293]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_298,plain,
% 3.64/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.64/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.64/1.00      | ~ v4_pre_topc(X0,sK0) ),
% 3.64/1.00      inference(global_propositional_subsumption,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_294,c_18]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_299,plain,
% 3.64/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.64/1.00      | ~ v4_pre_topc(X1,sK0)
% 3.64/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(renaming,[status(thm)],[c_298]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_919,plain,
% 3.64/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.64/1.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,sK2),sK0)
% 3.64/1.00      | ~ v4_pre_topc(sK2,sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_299]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_957,plain,
% 3.64/1.00      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 3.64/1.00      | ~ v4_pre_topc(sK2,sK0)
% 3.64/1.00      | ~ v4_pre_topc(sK1,sK0)
% 3.64/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_919]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,X1)
% 3.64/1.00      | v4_pre_topc(X0,X1)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ v8_pre_topc(X1)
% 3.64/1.00      | ~ v2_pre_topc(X1)
% 3.64/1.00      | ~ l1_pre_topc(X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_14,negated_conjecture,
% 3.64/1.00      ( v8_pre_topc(sK0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_242,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,X1)
% 3.64/1.00      | v4_pre_topc(X0,X1)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.64/1.00      | ~ v2_pre_topc(X1)
% 3.64/1.00      | ~ l1_pre_topc(X1)
% 3.64/1.00      | sK0 != X1 ),
% 3.64/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_243,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.64/1.00      | v4_pre_topc(X0,sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.64/1.00      | ~ v2_pre_topc(sK0)
% 3.64/1.00      | ~ l1_pre_topc(sK0) ),
% 3.64/1.00      inference(unflattening,[status(thm)],[c_242]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_247,plain,
% 3.64/1.00      ( ~ v2_compts_1(X0,sK0)
% 3.64/1.00      | v4_pre_topc(X0,sK0)
% 3.64/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(global_propositional_subsumption,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_243,c_18,c_17]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_899,plain,
% 3.64/1.00      ( ~ v2_compts_1(sK1,sK0)
% 3.64/1.00      | v4_pre_topc(sK1,sK0)
% 3.64/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_247]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_896,plain,
% 3.64/1.00      ( ~ v2_compts_1(sK2,sK0)
% 3.64/1.00      | v4_pre_topc(sK2,sK0)
% 3.64/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_247]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_11,negated_conjecture,
% 3.64/1.00      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_12,negated_conjecture,
% 3.64/1.00      ( v2_compts_1(sK2,sK0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_13,negated_conjecture,
% 3.64/1.00      ( v2_compts_1(sK1,sK0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(contradiction,plain,
% 3.64/1.00      ( $false ),
% 3.64/1.00      inference(minisat,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_10287,c_6785,c_5260,c_4080,c_2827,c_1380,c_1379,
% 3.64/1.00                 c_1328,c_1091,c_957,c_899,c_896,c_11,c_12,c_13,c_15,
% 3.64/1.00                 c_16]) ).
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  ------                               Statistics
% 3.64/1.00  
% 3.64/1.00  ------ General
% 3.64/1.00  
% 3.64/1.00  abstr_ref_over_cycles:                  0
% 3.64/1.00  abstr_ref_under_cycles:                 0
% 3.64/1.00  gc_basic_clause_elim:                   0
% 3.64/1.00  forced_gc_time:                         0
% 3.64/1.00  parsing_time:                           0.007
% 3.64/1.00  unif_index_cands_time:                  0.
% 3.64/1.00  unif_index_add_time:                    0.
% 3.64/1.00  orderings_time:                         0.
% 3.64/1.00  out_proof_time:                         0.011
% 3.64/1.00  total_time:                             0.321
% 3.64/1.00  num_of_symbols:                         46
% 3.64/1.00  num_of_terms:                           6560
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing
% 3.64/1.00  
% 3.64/1.00  num_of_splits:                          0
% 3.64/1.00  num_of_split_atoms:                     0
% 3.64/1.00  num_of_reused_defs:                     0
% 3.64/1.00  num_eq_ax_congr_red:                    10
% 3.64/1.00  num_of_sem_filtered_clauses:            1
% 3.64/1.00  num_of_subtypes:                        0
% 3.64/1.00  monotx_restored_types:                  0
% 3.64/1.00  sat_num_of_epr_types:                   0
% 3.64/1.00  sat_num_of_non_cyclic_types:            0
% 3.64/1.00  sat_guarded_non_collapsed_types:        0
% 3.64/1.00  num_pure_diseq_elim:                    0
% 3.64/1.00  simp_replaced_by:                       0
% 3.64/1.00  res_preprocessed:                       88
% 3.64/1.00  prep_upred:                             0
% 3.64/1.00  prep_unflattend:                        3
% 3.64/1.00  smt_new_axioms:                         0
% 3.64/1.00  pred_elim_cands:                        4
% 3.64/1.00  pred_elim:                              3
% 3.64/1.00  pred_elim_cl:                           3
% 3.64/1.00  pred_elim_cycles:                       5
% 3.64/1.00  merged_defs:                            8
% 3.64/1.00  merged_defs_ncl:                        0
% 3.64/1.00  bin_hyper_res:                          10
% 3.64/1.00  prep_cycles:                            4
% 3.64/1.00  pred_elim_time:                         0.002
% 3.64/1.00  splitting_time:                         0.
% 3.64/1.00  sem_filter_time:                        0.
% 3.64/1.00  monotx_time:                            0.003
% 3.64/1.00  subtype_inf_time:                       0.
% 3.64/1.00  
% 3.64/1.00  ------ Problem properties
% 3.64/1.00  
% 3.64/1.00  clauses:                                16
% 3.64/1.00  conjectures:                            5
% 3.64/1.00  epr:                                    2
% 3.64/1.00  horn:                                   16
% 3.64/1.00  ground:                                 5
% 3.64/1.00  unary:                                  7
% 3.64/1.00  binary:                                 6
% 3.64/1.00  lits:                                   33
% 3.64/1.00  lits_eq:                                4
% 3.64/1.00  fd_pure:                                0
% 3.64/1.00  fd_pseudo:                              0
% 3.64/1.00  fd_cond:                                0
% 3.64/1.00  fd_pseudo_cond:                         0
% 3.64/1.00  ac_symbols:                             0
% 3.64/1.00  
% 3.64/1.00  ------ Propositional Solver
% 3.64/1.00  
% 3.64/1.00  prop_solver_calls:                      33
% 3.64/1.00  prop_fast_solver_calls:                 993
% 3.64/1.00  smt_solver_calls:                       0
% 3.64/1.00  smt_fast_solver_calls:                  0
% 3.64/1.00  prop_num_of_clauses:                    3972
% 3.64/1.00  prop_preprocess_simplified:             8164
% 3.64/1.00  prop_fo_subsumed:                       32
% 3.64/1.00  prop_solver_time:                       0.
% 3.64/1.00  smt_solver_time:                        0.
% 3.64/1.00  smt_fast_solver_time:                   0.
% 3.64/1.00  prop_fast_solver_time:                  0.
% 3.64/1.00  prop_unsat_core_time:                   0.
% 3.64/1.00  
% 3.64/1.00  ------ QBF
% 3.64/1.00  
% 3.64/1.00  qbf_q_res:                              0
% 3.64/1.00  qbf_num_tautologies:                    0
% 3.64/1.00  qbf_prep_cycles:                        0
% 3.64/1.00  
% 3.64/1.00  ------ BMC1
% 3.64/1.00  
% 3.64/1.00  bmc1_current_bound:                     -1
% 3.64/1.00  bmc1_last_solved_bound:                 -1
% 3.64/1.00  bmc1_unsat_core_size:                   -1
% 3.64/1.00  bmc1_unsat_core_parents_size:           -1
% 3.64/1.00  bmc1_merge_next_fun:                    0
% 3.64/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.64/1.00  
% 3.64/1.00  ------ Instantiation
% 3.64/1.00  
% 3.64/1.00  inst_num_of_clauses:                    1242
% 3.64/1.00  inst_num_in_passive:                    66
% 3.64/1.00  inst_num_in_active:                     710
% 3.64/1.00  inst_num_in_unprocessed:                465
% 3.64/1.00  inst_num_of_loops:                      777
% 3.64/1.00  inst_num_of_learning_restarts:          0
% 3.64/1.00  inst_num_moves_active_passive:          60
% 3.64/1.00  inst_lit_activity:                      0
% 3.64/1.00  inst_lit_activity_moves:                0
% 3.64/1.00  inst_num_tautologies:                   0
% 3.64/1.00  inst_num_prop_implied:                  0
% 3.64/1.00  inst_num_existing_simplified:           0
% 3.64/1.00  inst_num_eq_res_simplified:             0
% 3.64/1.00  inst_num_child_elim:                    0
% 3.64/1.00  inst_num_of_dismatching_blockings:      550
% 3.64/1.00  inst_num_of_non_proper_insts:           1562
% 3.64/1.00  inst_num_of_duplicates:                 0
% 3.64/1.00  inst_inst_num_from_inst_to_res:         0
% 3.64/1.00  inst_dismatching_checking_time:         0.
% 3.64/1.00  
% 3.64/1.00  ------ Resolution
% 3.64/1.00  
% 3.64/1.00  res_num_of_clauses:                     0
% 3.64/1.00  res_num_in_passive:                     0
% 3.64/1.00  res_num_in_active:                      0
% 3.64/1.00  res_num_of_loops:                       92
% 3.64/1.00  res_forward_subset_subsumed:            209
% 3.64/1.00  res_backward_subset_subsumed:           14
% 3.64/1.00  res_forward_subsumed:                   0
% 3.64/1.00  res_backward_subsumed:                  0
% 3.64/1.00  res_forward_subsumption_resolution:     0
% 3.64/1.00  res_backward_subsumption_resolution:    0
% 3.64/1.00  res_clause_to_clause_subsumption:       2902
% 3.64/1.00  res_orphan_elimination:                 0
% 3.64/1.00  res_tautology_del:                      187
% 3.64/1.00  res_num_eq_res_simplified:              0
% 3.64/1.00  res_num_sel_changes:                    0
% 3.64/1.00  res_moves_from_active_to_pass:          0
% 3.64/1.00  
% 3.64/1.00  ------ Superposition
% 3.64/1.00  
% 3.64/1.00  sup_time_total:                         0.
% 3.64/1.00  sup_time_generating:                    0.
% 3.64/1.00  sup_time_sim_full:                      0.
% 3.64/1.00  sup_time_sim_immed:                     0.
% 3.64/1.00  
% 3.64/1.00  sup_num_of_clauses:                     201
% 3.64/1.00  sup_num_in_active:                      116
% 3.64/1.00  sup_num_in_passive:                     85
% 3.64/1.00  sup_num_of_loops:                       154
% 3.64/1.00  sup_fw_superposition:                   793
% 3.64/1.00  sup_bw_superposition:                   892
% 3.64/1.00  sup_immediate_simplified:               646
% 3.64/1.00  sup_given_eliminated:                   0
% 3.64/1.00  comparisons_done:                       0
% 3.64/1.00  comparisons_avoided:                    0
% 3.64/1.00  
% 3.64/1.00  ------ Simplifications
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  sim_fw_subset_subsumed:                 151
% 3.64/1.00  sim_bw_subset_subsumed:                 32
% 3.64/1.00  sim_fw_subsumed:                        231
% 3.64/1.00  sim_bw_subsumed:                        0
% 3.64/1.00  sim_fw_subsumption_res:                 0
% 3.64/1.00  sim_bw_subsumption_res:                 0
% 3.64/1.00  sim_tautology_del:                      44
% 3.64/1.00  sim_eq_tautology_del:                   3
% 3.64/1.00  sim_eq_res_simp:                        0
% 3.64/1.00  sim_fw_demodulated:                     179
% 3.64/1.00  sim_bw_demodulated:                     58
% 3.64/1.00  sim_light_normalised:                   234
% 3.64/1.00  sim_joinable_taut:                      0
% 3.64/1.00  sim_joinable_simp:                      0
% 3.64/1.00  sim_ac_normalised:                      0
% 3.64/1.00  sim_smt_subsumption:                    0
% 3.64/1.00  
%------------------------------------------------------------------------------
