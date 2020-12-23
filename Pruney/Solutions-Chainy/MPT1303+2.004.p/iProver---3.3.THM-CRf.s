%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:23 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 453 expanded)
%              Number of clauses        :   57 ( 110 expanded)
%              Number of leaves         :   21 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  285 (1083 expanded)
%              Number of equality atoms :   93 ( 322 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK3),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK2,X2),X0)
            & v1_tops_2(sK2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,X2),sK1)
              & v1_tops_2(X1,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1)
    & v1_tops_2(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f34,f33,f32])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_922,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_928,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_922,c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_920,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1578,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_928,c_920])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_917,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1576,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK3) ),
    inference(superposition,[status(thm)],[c_917,c_920])).

cnf(c_2224,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK3) = k9_subset_1(sK3,X0,sK3) ),
    inference(demodulation,[status(thm)],[c_1578,c_1576])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_923,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1448,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK3,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK3) ),
    inference(superposition,[status(thm)],[c_917,c_923])).

cnf(c_2392,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK3,X0) = k9_subset_1(sK3,X0,sK3) ),
    inference(demodulation,[status(thm)],[c_2224,c_1448])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_916,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1577,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2) ),
    inference(superposition,[status(thm)],[c_916,c_920])).

cnf(c_2225,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_1578,c_1577])).

cnf(c_2648,plain,
    ( k9_subset_1(sK2,sK3,sK2) = k9_subset_1(sK3,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2392,c_2225])).

cnf(c_12,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_919,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2390,plain,
    ( v1_tops_2(k9_subset_1(sK3,sK2,sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2224,c_919])).

cnf(c_7634,plain,
    ( v1_tops_2(k9_subset_1(sK2,sK3,sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2648,c_2390])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_921,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_469,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_470,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_221,c_470])).

cnf(c_914,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_2991,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_914])).

cnf(c_1449,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2) ),
    inference(superposition,[status(thm)],[c_916,c_923])).

cnf(c_1736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_921])).

cnf(c_18,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1049,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1254,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1255,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_2759,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1736,c_18,c_1255])).

cnf(c_2765,plain,
    ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2759,c_2225])).

cnf(c_11,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_235,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_236,plain,
    ( ~ v1_tops_2(X0,sK1)
    | v1_tops_2(X1,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_915,plain,
    ( v1_tops_2(X0,sK1) != iProver_top
    | v1_tops_2(X1,sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_2775,plain,
    ( v1_tops_2(X0,sK1) != iProver_top
    | v1_tops_2(k9_subset_1(sK2,X1,sK2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2765,c_915])).

cnf(c_3939,plain,
    ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top
    | v1_tops_2(sK2,sK1) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_2775])).

cnf(c_13,negated_conjecture,
    ( v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4792,plain,
    ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top
    | r1_tarski(k9_subset_1(sK2,X0,sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3939,c_20])).

cnf(c_4800,plain,
    ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2991,c_4792])).

cnf(c_5026,plain,
    ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4800,c_928])).

cnf(c_7682,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7634,c_5026])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.98  
% 3.00/0.98  ------  iProver source info
% 3.00/0.98  
% 3.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.98  git: non_committed_changes: false
% 3.00/0.98  git: last_make_outside_of_git: false
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     num_symb
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       true
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  ------ Parsing...
% 3.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.98  ------ Proving...
% 3.00/0.98  ------ Problem Properties 
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  clauses                                 13
% 3.00/0.98  conjectures                             4
% 3.00/0.98  EPR                                     1
% 3.00/0.98  Horn                                    12
% 3.00/0.98  unary                                   6
% 3.00/0.98  binary                                  4
% 3.00/0.98  lits                                    25
% 3.00/0.98  lits eq                                 5
% 3.00/0.98  fd_pure                                 0
% 3.00/0.98  fd_pseudo                               0
% 3.00/0.98  fd_cond                                 0
% 3.00/0.98  fd_pseudo_cond                          0
% 3.00/0.98  AC symbols                              0
% 3.00/0.98  
% 3.00/0.98  ------ Schedule dynamic 5 is on 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  Current options:
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     none
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       false
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ Proving...
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS status Theorem for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98   Resolution empty clause
% 3.00/0.98  
% 3.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  fof(f10,axiom,(
% 3.00/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f48,plain,(
% 3.00/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f10])).
% 3.00/0.98  
% 3.00/0.98  fof(f9,axiom,(
% 3.00/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f47,plain,(
% 3.00/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.00/0.98    inference(cnf_transformation,[],[f9])).
% 3.00/0.98  
% 3.00/0.98  fof(f13,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f21,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f13])).
% 3.00/0.98  
% 3.00/0.98  fof(f51,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f21])).
% 3.00/0.98  
% 3.00/0.98  fof(f14,axiom,(
% 3.00/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f52,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f14])).
% 3.00/0.98  
% 3.00/0.98  fof(f1,axiom,(
% 3.00/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f36,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f1])).
% 3.00/0.98  
% 3.00/0.98  fof(f2,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f37,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f2])).
% 3.00/0.98  
% 3.00/0.98  fof(f3,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f38,plain,(
% 3.00/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f3])).
% 3.00/0.98  
% 3.00/0.98  fof(f4,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f39,plain,(
% 3.00/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f4])).
% 3.00/0.98  
% 3.00/0.98  fof(f5,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f40,plain,(
% 3.00/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f5])).
% 3.00/0.98  
% 3.00/0.98  fof(f6,axiom,(
% 3.00/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f41,plain,(
% 3.00/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f6])).
% 3.00/0.98  
% 3.00/0.98  fof(f60,plain,(
% 3.00/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f40,f41])).
% 3.00/0.98  
% 3.00/0.98  fof(f61,plain,(
% 3.00/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f39,f60])).
% 3.00/0.98  
% 3.00/0.98  fof(f62,plain,(
% 3.00/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f38,f61])).
% 3.00/0.98  
% 3.00/0.98  fof(f63,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f37,f62])).
% 3.00/0.98  
% 3.00/0.98  fof(f64,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.00/0.98    inference(definition_unfolding,[],[f36,f63])).
% 3.00/0.98  
% 3.00/0.98  fof(f65,plain,(
% 3.00/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.00/0.98    inference(definition_unfolding,[],[f52,f64])).
% 3.00/0.98  
% 3.00/0.98  fof(f66,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(definition_unfolding,[],[f51,f65])).
% 3.00/0.98  
% 3.00/0.98  fof(f17,conjecture,(
% 3.00/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f18,negated_conjecture,(
% 3.00/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.00/0.98    inference(negated_conjecture,[],[f17])).
% 3.00/0.98  
% 3.00/0.98  fof(f26,plain,(
% 3.00/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f18])).
% 3.00/0.98  
% 3.00/0.98  fof(f27,plain,(
% 3.00/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.00/0.98    inference(flattening,[],[f26])).
% 3.00/0.98  
% 3.00/0.98  fof(f34,plain,(
% 3.00/0.98    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK3),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f33,plain,(
% 3.00/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK2,X2),X0) & v1_tops_2(sK2,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f32,plain,(
% 3.00/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,X2),sK1) & v1_tops_2(X1,sK1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & l1_pre_topc(sK1))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f35,plain,(
% 3.00/0.98    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) & v1_tops_2(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & l1_pre_topc(sK1)),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f34,f33,f32])).
% 3.00/0.98  
% 3.00/0.98  fof(f57,plain,(
% 3.00/0.98    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f8,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f19,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f8])).
% 3.00/0.98  
% 3.00/0.98  fof(f46,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f19])).
% 3.00/0.98  
% 3.00/0.98  fof(f56,plain,(
% 3.00/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f59,plain,(
% 3.00/0.98    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1)),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f11,axiom,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f20,plain,(
% 3.00/0.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f11])).
% 3.00/0.98  
% 3.00/0.98  fof(f49,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f20])).
% 3.00/0.98  
% 3.00/0.98  fof(f12,axiom,(
% 3.00/0.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f50,plain,(
% 3.00/0.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(cnf_transformation,[],[f12])).
% 3.00/0.98  
% 3.00/0.98  fof(f15,axiom,(
% 3.00/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f22,plain,(
% 3.00/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.00/0.98    inference(ennf_transformation,[],[f15])).
% 3.00/0.98  
% 3.00/0.98  fof(f23,plain,(
% 3.00/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.00/0.98    inference(flattening,[],[f22])).
% 3.00/0.98  
% 3.00/0.98  fof(f53,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f23])).
% 3.00/0.98  
% 3.00/0.98  fof(f7,axiom,(
% 3.00/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f28,plain,(
% 3.00/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/0.98    inference(nnf_transformation,[],[f7])).
% 3.00/0.98  
% 3.00/0.98  fof(f29,plain,(
% 3.00/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/0.98    inference(rectify,[],[f28])).
% 3.00/0.98  
% 3.00/0.98  fof(f30,plain,(
% 3.00/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f31,plain,(
% 3.00/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.00/0.98  
% 3.00/0.98  fof(f42,plain,(
% 3.00/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.00/0.98    inference(cnf_transformation,[],[f31])).
% 3.00/0.98  
% 3.00/0.98  fof(f68,plain,(
% 3.00/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(equality_resolution,[],[f42])).
% 3.00/0.98  
% 3.00/0.98  fof(f16,axiom,(
% 3.00/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 3.00/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f24,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f16])).
% 3.00/0.98  
% 3.00/0.98  fof(f25,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.00/0.98    inference(flattening,[],[f24])).
% 3.00/0.98  
% 3.00/0.98  fof(f54,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f25])).
% 3.00/0.98  
% 3.00/0.98  fof(f55,plain,(
% 3.00/0.98    l1_pre_topc(sK1)),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f58,plain,(
% 3.00/0.98    v1_tops_2(sK2,sK1)),
% 3.00/0.98    inference(cnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  cnf(c_6,plain,
% 3.00/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_922,plain,
% 3.00/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_5,plain,
% 3.00/0.98      ( k2_subset_1(X0) = X0 ),
% 3.00/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_928,plain,
% 3.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_922,c_5]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_9,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.98      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_920,plain,
% 3.00/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1578,plain,
% 3.00/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_928,c_920]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_14,negated_conjecture,
% 3.00/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_917,plain,
% 3.00/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1576,plain,
% 3.00/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK3) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_917,c_920]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2224,plain,
% 3.00/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK3) = k9_subset_1(sK3,X0,sK3) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_1578,c_1576]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.98      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_923,plain,
% 3.00/0.98      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 3.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1448,plain,
% 3.00/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK3,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK3) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_917,c_923]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2392,plain,
% 3.00/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK3,X0) = k9_subset_1(sK3,X0,sK3) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_2224,c_1448]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_15,negated_conjecture,
% 3.00/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.00/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_916,plain,
% 3.00/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1577,plain,
% 3.00/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_916,c_920]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2225,plain,
% 3.00/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_1578,c_1577]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2648,plain,
% 3.00/0.98      ( k9_subset_1(sK2,sK3,sK2) = k9_subset_1(sK3,sK2,sK3) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2392,c_2225]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_12,negated_conjecture,
% 3.00/0.98      ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_919,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2390,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(sK3,sK2,sK3),sK1) != iProver_top ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_2224,c_919]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_7634,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(sK2,sK3,sK2),sK1) != iProver_top ),
% 3.00/0.98      inference(demodulation,[status(thm)],[c_2648,c_2390]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_7,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_921,plain,
% 3.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_8,plain,
% 3.00/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_10,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_220,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_221,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_220]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3,plain,
% 3.00/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_469,plain,
% 3.00/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.00/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_470,plain,
% 3.00/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/0.98      inference(renaming,[status(thm)],[c_469]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_499,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/0.98      inference(bin_hyper_res,[status(thm)],[c_221,c_470]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_914,plain,
% 3.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2991,plain,
% 3.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/0.98      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_921,c_914]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1449,plain,
% 3.00/0.98      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2) ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_916,c_923]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1736,plain,
% 3.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.00/0.98      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_1449,c_921]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_18,plain,
% 3.00/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1049,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.00/0.98      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1254,plain,
% 3.00/0.98      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.00/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_1049]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1255,plain,
% 3.00/0.98      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.00/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2759,plain,
% 3.00/0.98      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_1736,c_18,c_1255]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2765,plain,
% 3.00/0.98      ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 3.00/0.98      inference(light_normalisation,[status(thm)],[c_2759,c_2225]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_11,plain,
% 3.00/0.98      ( ~ v1_tops_2(X0,X1)
% 3.00/0.98      | v1_tops_2(X2,X1)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.00/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.00/0.98      | ~ r1_tarski(X2,X0)
% 3.00/0.98      | ~ l1_pre_topc(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_16,negated_conjecture,
% 3.00/0.98      ( l1_pre_topc(sK1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_235,plain,
% 3.00/0.98      ( ~ v1_tops_2(X0,X1)
% 3.00/0.98      | v1_tops_2(X2,X1)
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.00/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.00/0.98      | ~ r1_tarski(X2,X0)
% 3.00/0.98      | sK1 != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_236,plain,
% 3.00/0.98      ( ~ v1_tops_2(X0,sK1)
% 3.00/0.98      | v1_tops_2(X1,sK1)
% 3.00/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.00/0.98      | ~ r1_tarski(X1,X0) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_235]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_915,plain,
% 3.00/0.98      ( v1_tops_2(X0,sK1) != iProver_top
% 3.00/0.98      | v1_tops_2(X1,sK1) = iProver_top
% 3.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.00/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2775,plain,
% 3.00/0.98      ( v1_tops_2(X0,sK1) != iProver_top
% 3.00/0.98      | v1_tops_2(k9_subset_1(sK2,X1,sK2),sK1) = iProver_top
% 3.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.00/0.98      | r1_tarski(k9_subset_1(sK2,X1,sK2),X0) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2765,c_915]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3939,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top
% 3.00/0.98      | v1_tops_2(sK2,sK1) != iProver_top
% 3.00/0.98      | r1_tarski(k9_subset_1(sK2,X0,sK2),sK2) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_916,c_2775]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_13,negated_conjecture,
% 3.00/0.98      ( v1_tops_2(sK2,sK1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_20,plain,
% 3.00/0.98      ( v1_tops_2(sK2,sK1) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4792,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top
% 3.00/0.98      | r1_tarski(k9_subset_1(sK2,X0,sK2),sK2) != iProver_top ),
% 3.00/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3939,c_20]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4800,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top
% 3.00/0.98      | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2991,c_4792]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_5026,plain,
% 3.00/0.98      ( v1_tops_2(k9_subset_1(sK2,X0,sK2),sK1) = iProver_top ),
% 3.00/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_4800,c_928]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_7682,plain,
% 3.00/0.98      ( $false ),
% 3.00/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_7634,c_5026]) ).
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  ------                               Statistics
% 3.00/0.98  
% 3.00/0.98  ------ General
% 3.00/0.98  
% 3.00/0.98  abstr_ref_over_cycles:                  0
% 3.00/0.98  abstr_ref_under_cycles:                 0
% 3.00/0.98  gc_basic_clause_elim:                   0
% 3.00/0.98  forced_gc_time:                         0
% 3.00/0.98  parsing_time:                           0.006
% 3.00/0.98  unif_index_cands_time:                  0.
% 3.00/0.98  unif_index_add_time:                    0.
% 3.00/0.98  orderings_time:                         0.
% 3.00/0.98  out_proof_time:                         0.008
% 3.00/0.98  total_time:                             0.192
% 3.00/0.98  num_of_symbols:                         47
% 3.00/0.98  num_of_terms:                           7402
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing
% 3.00/0.98  
% 3.00/0.98  num_of_splits:                          0
% 3.00/0.98  num_of_split_atoms:                     0
% 3.00/0.98  num_of_reused_defs:                     0
% 3.00/0.98  num_eq_ax_congr_red:                    46
% 3.00/0.98  num_of_sem_filtered_clauses:            1
% 3.00/0.98  num_of_subtypes:                        0
% 3.00/0.98  monotx_restored_types:                  0
% 3.00/0.98  sat_num_of_epr_types:                   0
% 3.00/0.98  sat_num_of_non_cyclic_types:            0
% 3.00/0.98  sat_guarded_non_collapsed_types:        0
% 3.00/0.98  num_pure_diseq_elim:                    0
% 3.00/0.98  simp_replaced_by:                       0
% 3.00/0.98  res_preprocessed:                       92
% 3.00/0.98  prep_upred:                             0
% 3.00/0.98  prep_unflattend:                        20
% 3.00/0.98  smt_new_axioms:                         0
% 3.00/0.98  pred_elim_cands:                        3
% 3.00/0.98  pred_elim:                              3
% 3.00/0.98  pred_elim_cl:                           4
% 3.00/0.98  pred_elim_cycles:                       7
% 3.00/0.98  merged_defs:                            4
% 3.00/0.98  merged_defs_ncl:                        0
% 3.00/0.98  bin_hyper_res:                          5
% 3.00/0.98  prep_cycles:                            5
% 3.00/0.98  pred_elim_time:                         0.003
% 3.00/0.98  splitting_time:                         0.
% 3.00/0.98  sem_filter_time:                        0.
% 3.00/0.98  monotx_time:                            0.
% 3.00/0.98  subtype_inf_time:                       0.
% 3.00/0.98  
% 3.00/0.98  ------ Problem properties
% 3.00/0.98  
% 3.00/0.98  clauses:                                13
% 3.00/0.98  conjectures:                            4
% 3.00/0.98  epr:                                    1
% 3.00/0.98  horn:                                   12
% 3.00/0.98  ground:                                 4
% 3.00/0.98  unary:                                  6
% 3.00/0.98  binary:                                 4
% 3.00/0.98  lits:                                   25
% 3.00/0.98  lits_eq:                                5
% 3.00/0.98  fd_pure:                                0
% 3.00/0.98  fd_pseudo:                              0
% 3.00/0.98  fd_cond:                                0
% 3.00/0.98  fd_pseudo_cond:                         0
% 3.00/0.98  ac_symbols:                             0
% 3.00/0.98  
% 3.00/0.98  ------ Propositional Solver
% 3.00/0.98  
% 3.00/0.98  prop_solver_calls:                      34
% 3.00/0.98  prop_fast_solver_calls:                 637
% 3.00/0.98  smt_solver_calls:                       0
% 3.00/0.98  smt_fast_solver_calls:                  0
% 3.00/0.98  prop_num_of_clauses:                    2759
% 3.00/0.98  prop_preprocess_simplified:             4831
% 3.00/0.98  prop_fo_subsumed:                       15
% 3.00/0.98  prop_solver_time:                       0.
% 3.00/0.98  smt_solver_time:                        0.
% 3.00/0.98  smt_fast_solver_time:                   0.
% 3.00/0.98  prop_fast_solver_time:                  0.
% 3.00/0.98  prop_unsat_core_time:                   0.
% 3.00/0.98  
% 3.00/0.98  ------ QBF
% 3.00/0.98  
% 3.00/0.98  qbf_q_res:                              0
% 3.00/0.98  qbf_num_tautologies:                    0
% 3.00/0.98  qbf_prep_cycles:                        0
% 3.00/0.98  
% 3.00/0.98  ------ BMC1
% 3.00/0.98  
% 3.00/0.98  bmc1_current_bound:                     -1
% 3.00/0.98  bmc1_last_solved_bound:                 -1
% 3.00/0.98  bmc1_unsat_core_size:                   -1
% 3.00/0.98  bmc1_unsat_core_parents_size:           -1
% 3.00/0.98  bmc1_merge_next_fun:                    0
% 3.00/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation
% 3.00/0.98  
% 3.00/0.98  inst_num_of_clauses:                    651
% 3.00/0.98  inst_num_in_passive:                    78
% 3.00/0.98  inst_num_in_active:                     340
% 3.00/0.98  inst_num_in_unprocessed:                233
% 3.00/0.98  inst_num_of_loops:                      370
% 3.00/0.98  inst_num_of_learning_restarts:          0
% 3.00/0.98  inst_num_moves_active_passive:          26
% 3.00/0.98  inst_lit_activity:                      0
% 3.00/0.98  inst_lit_activity_moves:                0
% 3.00/0.98  inst_num_tautologies:                   0
% 3.00/0.98  inst_num_prop_implied:                  0
% 3.00/0.98  inst_num_existing_simplified:           0
% 3.00/0.98  inst_num_eq_res_simplified:             0
% 3.00/0.98  inst_num_child_elim:                    0
% 3.00/0.98  inst_num_of_dismatching_blockings:      496
% 3.00/0.98  inst_num_of_non_proper_insts:           839
% 3.00/0.98  inst_num_of_duplicates:                 0
% 3.00/0.98  inst_inst_num_from_inst_to_res:         0
% 3.00/0.98  inst_dismatching_checking_time:         0.
% 3.00/0.98  
% 3.00/0.98  ------ Resolution
% 3.00/0.98  
% 3.00/0.98  res_num_of_clauses:                     0
% 3.00/0.98  res_num_in_passive:                     0
% 3.00/0.98  res_num_in_active:                      0
% 3.00/0.98  res_num_of_loops:                       97
% 3.00/0.98  res_forward_subset_subsumed:            98
% 3.00/0.98  res_backward_subset_subsumed:           0
% 3.00/0.98  res_forward_subsumed:                   0
% 3.00/0.98  res_backward_subsumed:                  0
% 3.00/0.98  res_forward_subsumption_resolution:     0
% 3.00/0.98  res_backward_subsumption_resolution:    0
% 3.00/0.98  res_clause_to_clause_subsumption:       1592
% 3.00/0.98  res_orphan_elimination:                 0
% 3.00/0.98  res_tautology_del:                      69
% 3.00/0.98  res_num_eq_res_simplified:              0
% 3.00/0.98  res_num_sel_changes:                    0
% 3.00/0.98  res_moves_from_active_to_pass:          0
% 3.00/0.98  
% 3.00/0.98  ------ Superposition
% 3.00/0.98  
% 3.00/0.98  sup_time_total:                         0.
% 3.00/0.98  sup_time_generating:                    0.
% 3.00/0.98  sup_time_sim_full:                      0.
% 3.00/0.98  sup_time_sim_immed:                     0.
% 3.00/0.98  
% 3.00/0.98  sup_num_of_clauses:                     241
% 3.00/0.98  sup_num_in_active:                      61
% 3.00/0.98  sup_num_in_passive:                     180
% 3.00/0.98  sup_num_of_loops:                       73
% 3.00/0.98  sup_fw_superposition:                   250
% 3.00/0.98  sup_bw_superposition:                   169
% 3.00/0.98  sup_immediate_simplified:               121
% 3.00/0.98  sup_given_eliminated:                   1
% 3.00/0.98  comparisons_done:                       0
% 3.00/0.98  comparisons_avoided:                    0
% 3.00/0.98  
% 3.00/0.98  ------ Simplifications
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  sim_fw_subset_subsumed:                 13
% 3.00/0.98  sim_bw_subset_subsumed:                 12
% 3.00/0.98  sim_fw_subsumed:                        44
% 3.00/0.98  sim_bw_subsumed:                        31
% 3.00/0.98  sim_fw_subsumption_res:                 3
% 3.00/0.98  sim_bw_subsumption_res:                 1
% 3.00/0.98  sim_tautology_del:                      11
% 3.00/0.98  sim_eq_tautology_del:                   1
% 3.00/0.98  sim_eq_res_simp:                        0
% 3.00/0.98  sim_fw_demodulated:                     36
% 3.00/0.98  sim_bw_demodulated:                     13
% 3.00/0.98  sim_light_normalised:                   17
% 3.00/0.98  sim_joinable_taut:                      0
% 3.00/0.98  sim_joinable_simp:                      0
% 3.00/0.98  sim_ac_normalised:                      0
% 3.00/0.98  sim_smt_subsumption:                    0
% 3.00/0.98  
%------------------------------------------------------------------------------
