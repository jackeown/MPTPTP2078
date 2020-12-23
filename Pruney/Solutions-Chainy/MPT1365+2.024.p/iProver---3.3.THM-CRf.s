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
% DateTime   : Thu Dec  3 12:18:01 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 682 expanded)
%              Number of clauses        :   62 ( 152 expanded)
%              Number of leaves         :   19 ( 200 expanded)
%              Depth                    :   25
%              Number of atoms          :  413 (2436 expanded)
%              Number of equality atoms :  168 ( 528 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f33,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_447,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_447,c_0])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_445,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1438,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_464,c_445])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1670,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_446])).

cnf(c_1890,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1670,c_464])).

cnf(c_1891,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1890])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_444,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1898,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_444])).

cnf(c_2075,plain,
    ( r1_tarski(k9_subset_1(X0,X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_1898])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_443,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v4_pre_topc(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1885,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(X2,X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_443])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1436,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_436,c_445])).

cnf(c_1661,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_1438,c_1436])).

cnf(c_7,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

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

cnf(c_1209,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) = iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_441])).

cnf(c_3903,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,sK2),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1209])).

cnf(c_3947,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3903,c_1661])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2558,plain,
    ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_446])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2925,plain,
    ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2558,c_19])).

cnf(c_2935,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2925,c_441])).

cnf(c_5931,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v2_compts_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3947,c_16,c_17,c_2935])).

cnf(c_5932,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5931])).

cnf(c_7166,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_5932])).

cnf(c_11,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( v8_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

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
    inference(cnf_transformation,[],[f47])).

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

cnf(c_9960,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7166,c_16,c_17,c_19,c_20,c_22,c_620])).

cnf(c_9961,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9960])).

cnf(c_11518,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_9961])).

cnf(c_12592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11518,c_19,c_22])).

cnf(c_12593,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12592])).

cnf(c_8,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_440,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2549,plain,
    ( v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1661,c_440])).

cnf(c_12601,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12593,c_2549])).

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
    inference(cnf_transformation,[],[f54])).

cnf(c_21,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12601,c_623,c_21,c_20,c_18,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:24:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.77/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.98  
% 3.77/0.98  ------  iProver source info
% 3.77/0.98  
% 3.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.98  git: non_committed_changes: false
% 3.77/0.98  git: last_make_outside_of_git: false
% 3.77/0.98  
% 3.77/0.98  ------ 
% 3.77/0.98  ------ Parsing...
% 3.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.98  
% 3.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.98  ------ Proving...
% 3.77/0.98  ------ Problem Properties 
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  clauses                                 16
% 3.77/0.98  conjectures                             8
% 3.77/0.98  EPR                                     5
% 3.77/0.98  Horn                                    16
% 3.77/0.98  unary                                   10
% 3.77/0.98  binary                                  3
% 3.77/0.98  lits                                    37
% 3.77/0.98  lits eq                                 2
% 3.77/0.98  fd_pure                                 0
% 3.77/0.98  fd_pseudo                               0
% 3.77/0.98  fd_cond                                 0
% 3.77/0.98  fd_pseudo_cond                          0
% 3.77/0.98  AC symbols                              0
% 3.77/0.98  
% 3.77/0.98  ------ Input Options Time Limit: Unbounded
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  ------ 
% 3.77/0.98  Current options:
% 3.77/0.98  ------ 
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  ------ Proving...
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  % SZS status Theorem for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  fof(f8,axiom,(
% 3.77/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f41,plain,(
% 3.77/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.77/0.98    inference(cnf_transformation,[],[f8])).
% 3.77/0.98  
% 3.77/0.98  fof(f7,axiom,(
% 3.77/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f40,plain,(
% 3.77/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.77/0.98    inference(cnf_transformation,[],[f7])).
% 3.77/0.98  
% 3.77/0.98  fof(f10,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f20,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f10])).
% 3.77/0.98  
% 3.77/0.98  fof(f43,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.77/0.98    inference(cnf_transformation,[],[f20])).
% 3.77/0.98  
% 3.77/0.98  fof(f11,axiom,(
% 3.77/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f44,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.77/0.98    inference(cnf_transformation,[],[f11])).
% 3.77/0.98  
% 3.77/0.98  fof(f1,axiom,(
% 3.77/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f34,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f1])).
% 3.77/0.98  
% 3.77/0.98  fof(f2,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f35,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f2])).
% 3.77/0.98  
% 3.77/0.98  fof(f3,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f36,plain,(
% 3.77/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f3])).
% 3.77/0.98  
% 3.77/0.98  fof(f4,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f37,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f4])).
% 3.77/0.98  
% 3.77/0.98  fof(f5,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f38,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f5])).
% 3.77/0.98  
% 3.77/0.98  fof(f6,axiom,(
% 3.77/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f39,plain,(
% 3.77/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f6])).
% 3.77/0.98  
% 3.77/0.98  fof(f57,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f38,f39])).
% 3.77/0.98  
% 3.77/0.98  fof(f58,plain,(
% 3.77/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f37,f57])).
% 3.77/0.98  
% 3.77/0.98  fof(f59,plain,(
% 3.77/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f36,f58])).
% 3.77/0.98  
% 3.77/0.98  fof(f60,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f35,f59])).
% 3.77/0.98  
% 3.77/0.98  fof(f61,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f34,f60])).
% 3.77/0.98  
% 3.77/0.98  fof(f62,plain,(
% 3.77/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.77/0.98    inference(definition_unfolding,[],[f44,f61])).
% 3.77/0.98  
% 3.77/0.98  fof(f63,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.77/0.98    inference(definition_unfolding,[],[f43,f62])).
% 3.77/0.98  
% 3.77/0.98  fof(f9,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f19,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f9])).
% 3.77/0.98  
% 3.77/0.98  fof(f42,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.77/0.98    inference(cnf_transformation,[],[f19])).
% 3.77/0.98  
% 3.77/0.98  fof(f12,axiom,(
% 3.77/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f18,plain,(
% 3.77/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.77/0.98    inference(unused_predicate_definition_removal,[],[f12])).
% 3.77/0.98  
% 3.77/0.98  fof(f21,plain,(
% 3.77/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.77/0.98    inference(ennf_transformation,[],[f18])).
% 3.77/0.98  
% 3.77/0.98  fof(f45,plain,(
% 3.77/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/0.98    inference(cnf_transformation,[],[f21])).
% 3.77/0.98  
% 3.77/0.98  fof(f13,axiom,(
% 3.77/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f22,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f13])).
% 3.77/0.98  
% 3.77/0.98  fof(f23,plain,(
% 3.77/0.98    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.98    inference(flattening,[],[f22])).
% 3.77/0.98  
% 3.77/0.98  fof(f46,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f23])).
% 3.77/0.98  
% 3.77/0.98  fof(f64,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (v4_pre_topc(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.98    inference(definition_unfolding,[],[f46,f62])).
% 3.77/0.98  
% 3.77/0.98  fof(f16,conjecture,(
% 3.77/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f17,negated_conjecture,(
% 3.77/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.77/0.98    inference(negated_conjecture,[],[f16])).
% 3.77/0.98  
% 3.77/0.98  fof(f28,plain,(
% 3.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f17])).
% 3.77/0.98  
% 3.77/0.98  fof(f29,plain,(
% 3.77/0.98    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.77/0.98    inference(flattening,[],[f28])).
% 3.77/0.98  
% 3.77/0.98  fof(f32,plain,(
% 3.77/0.98    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f31,plain,(
% 3.77/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f30,plain,(
% 3.77/0.98    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.77/0.98    introduced(choice_axiom,[])).
% 3.77/0.98  
% 3.77/0.98  fof(f33,plain,(
% 3.77/0.98    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 3.77/0.98  
% 3.77/0.98  fof(f52,plain,(
% 3.77/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f15,axiom,(
% 3.77/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f26,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f15])).
% 3.77/0.98  
% 3.77/0.98  fof(f27,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.98    inference(flattening,[],[f26])).
% 3.77/0.98  
% 3.77/0.98  fof(f48,plain,(
% 3.77/0.98    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f27])).
% 3.77/0.98  
% 3.77/0.98  fof(f49,plain,(
% 3.77/0.98    v2_pre_topc(sK0)),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f50,plain,(
% 3.77/0.98    l1_pre_topc(sK0)),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f53,plain,(
% 3.77/0.98    v8_pre_topc(sK0)),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f55,plain,(
% 3.77/0.98    v2_compts_1(sK2,sK0)),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f14,axiom,(
% 3.77/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 3.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.98  
% 3.77/0.98  fof(f24,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.98    inference(ennf_transformation,[],[f14])).
% 3.77/0.98  
% 3.77/0.98  fof(f25,plain,(
% 3.77/0.98    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.98    inference(flattening,[],[f24])).
% 3.77/0.98  
% 3.77/0.98  fof(f47,plain,(
% 3.77/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.98    inference(cnf_transformation,[],[f25])).
% 3.77/0.98  
% 3.77/0.98  fof(f56,plain,(
% 3.77/0.98    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f54,plain,(
% 3.77/0.98    v2_compts_1(sK1,sK0)),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  fof(f51,plain,(
% 3.77/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.77/0.98    inference(cnf_transformation,[],[f33])).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1,plain,
% 3.77/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_447,plain,
% 3.77/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_0,plain,
% 3.77/0.98      ( k2_subset_1(X0) = X0 ),
% 3.77/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_464,plain,
% 3.77/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.77/0.98      inference(light_normalisation,[status(thm)],[c_447,c_0]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3,plain,
% 3.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.98      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_445,plain,
% 3.77/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.77/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1438,plain,
% 3.77/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_464,c_445]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2,plain,
% 3.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_446,plain,
% 3.77/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.77/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1670,plain,
% 3.77/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 3.77/0.98      | m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1438,c_446]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1890,plain,
% 3.77/0.98      ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_1670,c_464]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1891,plain,
% 3.77/0.98      ( m1_subset_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_1890]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_4,plain,
% 3.77/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_444,plain,
% 3.77/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1898,plain,
% 3.77/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1891,c_444]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2075,plain,
% 3.77/0.98      ( r1_tarski(k9_subset_1(X0,X1,X0),X0) = iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1438,c_1898]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5,plain,
% 3.77/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.77/0.98      | ~ v4_pre_topc(X2,X1)
% 3.77/0.98      | v4_pre_topc(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)),X1)
% 3.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.98      | ~ v2_pre_topc(X1)
% 3.77/0.98      | ~ l1_pre_topc(X1) ),
% 3.77/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_443,plain,
% 3.77/0.98      ( v4_pre_topc(X0,X1) != iProver_top
% 3.77/0.98      | v4_pre_topc(X2,X1) != iProver_top
% 3.77/0.98      | v4_pre_topc(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | v2_pre_topc(X1) != iProver_top
% 3.77/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1885,plain,
% 3.77/0.98      ( v4_pre_topc(X0,X1) != iProver_top
% 3.77/0.98      | v4_pre_topc(X2,X1) != iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(X2,X0,X2),X1) = iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | v2_pre_topc(X1) != iProver_top
% 3.77/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1438,c_443]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_12,negated_conjecture,
% 3.77/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_436,plain,
% 3.77/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1436,plain,
% 3.77/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_436,c_445]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1661,plain,
% 3.77/0.98      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_1438,c_1436]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7,plain,
% 3.77/0.98      ( ~ v2_compts_1(X0,X1)
% 3.77/0.98      | v2_compts_1(X2,X1)
% 3.77/0.98      | ~ v4_pre_topc(X2,X1)
% 3.77/0.98      | ~ r1_tarski(X2,X0)
% 3.77/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.98      | ~ v2_pre_topc(X1)
% 3.77/0.98      | ~ l1_pre_topc(X1) ),
% 3.77/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_441,plain,
% 3.77/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.77/0.98      | v2_compts_1(X2,X1) = iProver_top
% 3.77/0.98      | v4_pre_topc(X2,X1) != iProver_top
% 3.77/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | v2_pre_topc(X1) != iProver_top
% 3.77/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_1209,plain,
% 3.77/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) = iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.77/0.98      | v2_pre_topc(X1) != iProver_top
% 3.77/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_446,c_441]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3903,plain,
% 3.77/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,sK2),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1661,c_1209]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_3947,plain,
% 3.77/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_3903,c_1661]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_15,negated_conjecture,
% 3.77/0.98      ( v2_pre_topc(sK0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_16,plain,
% 3.77/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_14,negated_conjecture,
% 3.77/0.98      ( l1_pre_topc(sK0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_17,plain,
% 3.77/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2558,plain,
% 3.77/0.98      ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1661,c_446]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_19,plain,
% 3.77/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2925,plain,
% 3.77/0.98      ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_2558,c_19]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2935,plain,
% 3.77/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_2925,c_441]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5931,plain,
% 3.77/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v2_compts_1(X0,sK0) != iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_3947,c_16,c_17,c_2935]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_5932,plain,
% 3.77/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(k9_subset_1(sK2,X1,sK2),sK0) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_5931]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_7166,plain,
% 3.77/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(X1,sK0) != iProver_top
% 3.77/0.98      | v4_pre_topc(sK2,sK0) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_1885,c_5932]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_11,negated_conjecture,
% 3.77/0.98      ( v8_pre_topc(sK0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_20,plain,
% 3.77/0.98      ( v8_pre_topc(sK0) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_9,negated_conjecture,
% 3.77/0.98      ( v2_compts_1(sK2,sK0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_22,plain,
% 3.77/0.98      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_6,plain,
% 3.77/0.98      ( ~ v2_compts_1(X0,X1)
% 3.77/0.98      | v4_pre_topc(X0,X1)
% 3.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.98      | ~ v8_pre_topc(X1)
% 3.77/0.98      | ~ v2_pre_topc(X1)
% 3.77/0.98      | ~ l1_pre_topc(X1) ),
% 3.77/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_619,plain,
% 3.77/0.98      ( ~ v2_compts_1(sK2,sK0)
% 3.77/0.98      | v4_pre_topc(sK2,sK0)
% 3.77/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.98      | ~ v8_pre_topc(sK0)
% 3.77/0.98      | ~ v2_pre_topc(sK0)
% 3.77/0.98      | ~ l1_pre_topc(sK0) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_620,plain,
% 3.77/0.98      ( v2_compts_1(sK2,sK0) != iProver_top
% 3.77/0.98      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v8_pre_topc(sK0) != iProver_top
% 3.77/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_9960,plain,
% 3.77/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(X1,sK0) != iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_7166,c_16,c_17,c_19,c_20,c_22,c_620]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_9961,plain,
% 3.77/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X1,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(X1,sK0) != iProver_top
% 3.77/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_9960]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_11518,plain,
% 3.77/0.98      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.77/0.98      | v2_compts_1(sK2,sK0) != iProver_top
% 3.77/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_2075,c_9961]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_12592,plain,
% 3.77/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.77/0.98      | v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
% 3.77/0.98      inference(global_propositional_subsumption,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_11518,c_19,c_22]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_12593,plain,
% 3.77/0.98      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.77/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.77/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.98      inference(renaming,[status(thm)],[c_12592]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_8,negated_conjecture,
% 3.77/0.98      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_440,plain,
% 3.77/0.98      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_2549,plain,
% 3.77/0.98      ( v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 3.77/0.98      inference(demodulation,[status(thm)],[c_1661,c_440]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_12601,plain,
% 3.77/0.98      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.77/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.77/0.98      inference(superposition,[status(thm)],[c_12593,c_2549]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_622,plain,
% 3.77/0.98      ( ~ v2_compts_1(sK1,sK0)
% 3.77/0.98      | v4_pre_topc(sK1,sK0)
% 3.77/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.77/0.98      | ~ v8_pre_topc(sK0)
% 3.77/0.98      | ~ v2_pre_topc(sK0)
% 3.77/0.98      | ~ l1_pre_topc(sK0) ),
% 3.77/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_623,plain,
% 3.77/0.98      ( v2_compts_1(sK1,sK0) != iProver_top
% 3.77/0.98      | v4_pre_topc(sK1,sK0) = iProver_top
% 3.77/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.77/0.98      | v8_pre_topc(sK0) != iProver_top
% 3.77/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_10,negated_conjecture,
% 3.77/0.98      ( v2_compts_1(sK1,sK0) ),
% 3.77/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_21,plain,
% 3.77/0.98      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_13,negated_conjecture,
% 3.77/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.77/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(c_18,plain,
% 3.77/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.77/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.77/0.98  
% 3.77/0.98  cnf(contradiction,plain,
% 3.77/0.98      ( $false ),
% 3.77/0.98      inference(minisat,
% 3.77/0.98                [status(thm)],
% 3.77/0.98                [c_12601,c_623,c_21,c_20,c_18,c_17,c_16]) ).
% 3.77/0.98  
% 3.77/0.98  
% 3.77/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.98  
% 3.77/0.98  ------                               Statistics
% 3.77/0.98  
% 3.77/0.98  ------ Selected
% 3.77/0.98  
% 3.77/0.98  total_time:                             0.44
% 3.77/0.98  
%------------------------------------------------------------------------------
