%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:52 EST 2020

% Result     : Theorem 19.83s
% Output     : CNFRefutation 19.83s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 549 expanded)
%              Number of clauses        :   78 ( 175 expanded)
%              Number of leaves         :   24 ( 148 expanded)
%              Depth                    :   25
%              Number of atoms          :  332 (1414 expanded)
%              Number of equality atoms :  118 ( 288 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f36,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35,f34,f33])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f58,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_916,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1651,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(X1,sK2)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_5887,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(k2_subset_1(sK2),sK2)
    | X0 != k2_subset_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_74973,plain,
    ( ~ r1_tarski(k2_subset_1(sK2),sK2)
    | r1_tarski(sK2,sK2)
    | sK2 != k2_subset_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5887])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_680,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_682,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1103,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_682])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_679,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1104,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_682])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_109,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_110])).

cnf(c_274,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_135,c_275])).

cnf(c_675,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_1810,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_675])).

cnf(c_2252,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1103,c_1810])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_687,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2392,plain,
    ( r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_687])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_1105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_682])).

cnf(c_1817,plain,
    ( k3_tarski(k6_enumset1(k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),X1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_675])).

cnf(c_8928,plain,
    ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_1817])).

cnf(c_9814,plain,
    ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_8928])).

cnf(c_55473,plain,
    ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_680,c_9814])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_685,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_56276,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),X0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_55473,c_685])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_681,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_57968,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_56276,c_681])).

cnf(c_58736,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_57968])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_110])).

cnf(c_298,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_134,c_275])).

cnf(c_812,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_7339,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_16705,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7339])).

cnf(c_16706,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16705])).

cnf(c_74127,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58736,c_17,c_1103,c_1104,c_16706])).

cnf(c_74133,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_74127])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_686,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2394,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_686])).

cnf(c_74248,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_74133,c_16,c_1103,c_1104,c_2394,c_16706])).

cnf(c_74253,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_74248])).

cnf(c_74254,plain,
    ( ~ r1_tarski(sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_74253])).

cnf(c_355,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1655,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_5895,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_58680,plain,
    ( k2_subset_1(sK2) != sK2
    | sK2 = k2_subset_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5895])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15765,plain,
    ( k2_subset_1(sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_354,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1652,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1448,plain,
    ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1447,plain,
    ( ~ m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2))
    | r1_tarski(k2_subset_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74973,c_74254,c_58680,c_15765,c_1652,c_1448,c_1447])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.83/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.83/2.98  
% 19.83/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.83/2.98  
% 19.83/2.98  ------  iProver source info
% 19.83/2.98  
% 19.83/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.83/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.83/2.98  git: non_committed_changes: false
% 19.83/2.98  git: last_make_outside_of_git: false
% 19.83/2.98  
% 19.83/2.98  ------ 
% 19.83/2.98  
% 19.83/2.98  ------ Input Options
% 19.83/2.98  
% 19.83/2.98  --out_options                           all
% 19.83/2.98  --tptp_safe_out                         true
% 19.83/2.98  --problem_path                          ""
% 19.83/2.98  --include_path                          ""
% 19.83/2.98  --clausifier                            res/vclausify_rel
% 19.83/2.98  --clausifier_options                    --mode clausify
% 19.83/2.98  --stdin                                 false
% 19.83/2.98  --stats_out                             all
% 19.83/2.98  
% 19.83/2.98  ------ General Options
% 19.83/2.98  
% 19.83/2.98  --fof                                   false
% 19.83/2.98  --time_out_real                         305.
% 19.83/2.98  --time_out_virtual                      -1.
% 19.83/2.98  --symbol_type_check                     false
% 19.83/2.98  --clausify_out                          false
% 19.83/2.98  --sig_cnt_out                           false
% 19.83/2.98  --trig_cnt_out                          false
% 19.83/2.98  --trig_cnt_out_tolerance                1.
% 19.83/2.98  --trig_cnt_out_sk_spl                   false
% 19.83/2.98  --abstr_cl_out                          false
% 19.83/2.98  
% 19.83/2.98  ------ Global Options
% 19.83/2.98  
% 19.83/2.98  --schedule                              default
% 19.83/2.98  --add_important_lit                     false
% 19.83/2.98  --prop_solver_per_cl                    1000
% 19.83/2.98  --min_unsat_core                        false
% 19.83/2.98  --soft_assumptions                      false
% 19.83/2.98  --soft_lemma_size                       3
% 19.83/2.98  --prop_impl_unit_size                   0
% 19.83/2.98  --prop_impl_unit                        []
% 19.83/2.98  --share_sel_clauses                     true
% 19.83/2.98  --reset_solvers                         false
% 19.83/2.98  --bc_imp_inh                            [conj_cone]
% 19.83/2.98  --conj_cone_tolerance                   3.
% 19.83/2.98  --extra_neg_conj                        none
% 19.83/2.98  --large_theory_mode                     true
% 19.83/2.98  --prolific_symb_bound                   200
% 19.83/2.98  --lt_threshold                          2000
% 19.83/2.98  --clause_weak_htbl                      true
% 19.83/2.98  --gc_record_bc_elim                     false
% 19.83/2.98  
% 19.83/2.98  ------ Preprocessing Options
% 19.83/2.98  
% 19.83/2.98  --preprocessing_flag                    true
% 19.83/2.98  --time_out_prep_mult                    0.1
% 19.83/2.98  --splitting_mode                        input
% 19.83/2.98  --splitting_grd                         true
% 19.83/2.98  --splitting_cvd                         false
% 19.83/2.98  --splitting_cvd_svl                     false
% 19.83/2.98  --splitting_nvd                         32
% 19.83/2.98  --sub_typing                            true
% 19.83/2.98  --prep_gs_sim                           true
% 19.83/2.98  --prep_unflatten                        true
% 19.83/2.98  --prep_res_sim                          true
% 19.83/2.98  --prep_upred                            true
% 19.83/2.98  --prep_sem_filter                       exhaustive
% 19.83/2.98  --prep_sem_filter_out                   false
% 19.83/2.98  --pred_elim                             true
% 19.83/2.98  --res_sim_input                         true
% 19.83/2.98  --eq_ax_congr_red                       true
% 19.83/2.98  --pure_diseq_elim                       true
% 19.83/2.98  --brand_transform                       false
% 19.83/2.98  --non_eq_to_eq                          false
% 19.83/2.98  --prep_def_merge                        true
% 19.83/2.98  --prep_def_merge_prop_impl              false
% 19.83/2.98  --prep_def_merge_mbd                    true
% 19.83/2.98  --prep_def_merge_tr_red                 false
% 19.83/2.98  --prep_def_merge_tr_cl                  false
% 19.83/2.98  --smt_preprocessing                     true
% 19.83/2.98  --smt_ac_axioms                         fast
% 19.83/2.98  --preprocessed_out                      false
% 19.83/2.98  --preprocessed_stats                    false
% 19.83/2.98  
% 19.83/2.98  ------ Abstraction refinement Options
% 19.83/2.98  
% 19.83/2.98  --abstr_ref                             []
% 19.83/2.98  --abstr_ref_prep                        false
% 19.83/2.98  --abstr_ref_until_sat                   false
% 19.83/2.98  --abstr_ref_sig_restrict                funpre
% 19.83/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.83/2.98  --abstr_ref_under                       []
% 19.83/2.98  
% 19.83/2.98  ------ SAT Options
% 19.83/2.98  
% 19.83/2.98  --sat_mode                              false
% 19.83/2.98  --sat_fm_restart_options                ""
% 19.83/2.98  --sat_gr_def                            false
% 19.83/2.98  --sat_epr_types                         true
% 19.83/2.98  --sat_non_cyclic_types                  false
% 19.83/2.98  --sat_finite_models                     false
% 19.83/2.98  --sat_fm_lemmas                         false
% 19.83/2.98  --sat_fm_prep                           false
% 19.83/2.98  --sat_fm_uc_incr                        true
% 19.83/2.98  --sat_out_model                         small
% 19.83/2.98  --sat_out_clauses                       false
% 19.83/2.98  
% 19.83/2.98  ------ QBF Options
% 19.83/2.98  
% 19.83/2.98  --qbf_mode                              false
% 19.83/2.98  --qbf_elim_univ                         false
% 19.83/2.98  --qbf_dom_inst                          none
% 19.83/2.98  --qbf_dom_pre_inst                      false
% 19.83/2.98  --qbf_sk_in                             false
% 19.83/2.98  --qbf_pred_elim                         true
% 19.83/2.98  --qbf_split                             512
% 19.83/2.98  
% 19.83/2.98  ------ BMC1 Options
% 19.83/2.98  
% 19.83/2.98  --bmc1_incremental                      false
% 19.83/2.98  --bmc1_axioms                           reachable_all
% 19.83/2.98  --bmc1_min_bound                        0
% 19.83/2.98  --bmc1_max_bound                        -1
% 19.83/2.98  --bmc1_max_bound_default                -1
% 19.83/2.98  --bmc1_symbol_reachability              true
% 19.83/2.98  --bmc1_property_lemmas                  false
% 19.83/2.98  --bmc1_k_induction                      false
% 19.83/2.98  --bmc1_non_equiv_states                 false
% 19.83/2.98  --bmc1_deadlock                         false
% 19.83/2.98  --bmc1_ucm                              false
% 19.83/2.98  --bmc1_add_unsat_core                   none
% 19.83/2.98  --bmc1_unsat_core_children              false
% 19.83/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.83/2.98  --bmc1_out_stat                         full
% 19.83/2.98  --bmc1_ground_init                      false
% 19.83/2.98  --bmc1_pre_inst_next_state              false
% 19.83/2.98  --bmc1_pre_inst_state                   false
% 19.83/2.98  --bmc1_pre_inst_reach_state             false
% 19.83/2.98  --bmc1_out_unsat_core                   false
% 19.83/2.98  --bmc1_aig_witness_out                  false
% 19.83/2.98  --bmc1_verbose                          false
% 19.83/2.98  --bmc1_dump_clauses_tptp                false
% 19.83/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.83/2.98  --bmc1_dump_file                        -
% 19.83/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.83/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.83/2.98  --bmc1_ucm_extend_mode                  1
% 19.83/2.98  --bmc1_ucm_init_mode                    2
% 19.83/2.98  --bmc1_ucm_cone_mode                    none
% 19.83/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.83/2.98  --bmc1_ucm_relax_model                  4
% 19.83/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.83/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.83/2.98  --bmc1_ucm_layered_model                none
% 19.83/2.98  --bmc1_ucm_max_lemma_size               10
% 19.83/2.98  
% 19.83/2.98  ------ AIG Options
% 19.83/2.98  
% 19.83/2.98  --aig_mode                              false
% 19.83/2.98  
% 19.83/2.98  ------ Instantiation Options
% 19.83/2.98  
% 19.83/2.98  --instantiation_flag                    true
% 19.83/2.98  --inst_sos_flag                         false
% 19.83/2.98  --inst_sos_phase                        true
% 19.83/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.83/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.83/2.98  --inst_lit_sel_side                     num_symb
% 19.83/2.98  --inst_solver_per_active                1400
% 19.83/2.98  --inst_solver_calls_frac                1.
% 19.83/2.98  --inst_passive_queue_type               priority_queues
% 19.83/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.83/2.98  --inst_passive_queues_freq              [25;2]
% 19.83/2.98  --inst_dismatching                      true
% 19.83/2.98  --inst_eager_unprocessed_to_passive     true
% 19.83/2.98  --inst_prop_sim_given                   true
% 19.83/2.98  --inst_prop_sim_new                     false
% 19.83/2.98  --inst_subs_new                         false
% 19.83/2.98  --inst_eq_res_simp                      false
% 19.83/2.98  --inst_subs_given                       false
% 19.83/2.98  --inst_orphan_elimination               true
% 19.83/2.98  --inst_learning_loop_flag               true
% 19.83/2.98  --inst_learning_start                   3000
% 19.83/2.98  --inst_learning_factor                  2
% 19.83/2.98  --inst_start_prop_sim_after_learn       3
% 19.83/2.98  --inst_sel_renew                        solver
% 19.83/2.98  --inst_lit_activity_flag                true
% 19.83/2.98  --inst_restr_to_given                   false
% 19.83/2.98  --inst_activity_threshold               500
% 19.83/2.98  --inst_out_proof                        true
% 19.83/2.98  
% 19.83/2.98  ------ Resolution Options
% 19.83/2.98  
% 19.83/2.98  --resolution_flag                       true
% 19.83/2.98  --res_lit_sel                           adaptive
% 19.83/2.98  --res_lit_sel_side                      none
% 19.83/2.98  --res_ordering                          kbo
% 19.83/2.98  --res_to_prop_solver                    active
% 19.83/2.98  --res_prop_simpl_new                    false
% 19.83/2.98  --res_prop_simpl_given                  true
% 19.83/2.98  --res_passive_queue_type                priority_queues
% 19.83/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.83/2.98  --res_passive_queues_freq               [15;5]
% 19.83/2.98  --res_forward_subs                      full
% 19.83/2.98  --res_backward_subs                     full
% 19.83/2.98  --res_forward_subs_resolution           true
% 19.83/2.98  --res_backward_subs_resolution          true
% 19.83/2.98  --res_orphan_elimination                true
% 19.83/2.98  --res_time_limit                        2.
% 19.83/2.98  --res_out_proof                         true
% 19.83/2.98  
% 19.83/2.98  ------ Superposition Options
% 19.83/2.98  
% 19.83/2.98  --superposition_flag                    true
% 19.83/2.98  --sup_passive_queue_type                priority_queues
% 19.83/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.83/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.83/2.98  --demod_completeness_check              fast
% 19.83/2.98  --demod_use_ground                      true
% 19.83/2.98  --sup_to_prop_solver                    passive
% 19.83/2.98  --sup_prop_simpl_new                    true
% 19.83/2.98  --sup_prop_simpl_given                  true
% 19.83/2.98  --sup_fun_splitting                     false
% 19.83/2.98  --sup_smt_interval                      50000
% 19.83/2.98  
% 19.83/2.98  ------ Superposition Simplification Setup
% 19.83/2.98  
% 19.83/2.98  --sup_indices_passive                   []
% 19.83/2.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.83/2.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.83/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.83/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.83/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.83/2.98  --sup_full_bw                           [BwDemod]
% 19.83/2.98  --sup_immed_triv                        [TrivRules]
% 19.83/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.83/2.98  --sup_immed_bw_main                     []
% 19.83/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.83/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.83/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.83/2.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.83/2.98  
% 19.83/2.98  ------ Combination Options
% 19.83/2.98  
% 19.83/2.98  --comb_res_mult                         3
% 19.83/2.98  --comb_sup_mult                         2
% 19.83/2.98  --comb_inst_mult                        10
% 19.83/2.98  
% 19.83/2.98  ------ Debug Options
% 19.83/2.98  
% 19.83/2.98  --dbg_backtrace                         false
% 19.83/2.98  --dbg_dump_prop_clauses                 false
% 19.83/2.98  --dbg_dump_prop_clauses_file            -
% 19.83/2.98  --dbg_out_stat                          false
% 19.83/2.98  ------ Parsing...
% 19.83/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.83/2.98  
% 19.83/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.83/2.98  
% 19.83/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.83/2.98  
% 19.83/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.98  ------ Proving...
% 19.83/2.98  ------ Problem Properties 
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  clauses                                 14
% 19.83/2.98  conjectures                             3
% 19.83/2.98  EPR                                     0
% 19.83/2.98  Horn                                    14
% 19.83/2.98  unary                                   6
% 19.83/2.98  binary                                  4
% 19.83/2.98  lits                                    27
% 19.83/2.98  lits eq                                 2
% 19.83/2.98  fd_pure                                 0
% 19.83/2.98  fd_pseudo                               0
% 19.83/2.98  fd_cond                                 0
% 19.83/2.98  fd_pseudo_cond                          0
% 19.83/2.98  AC symbols                              0
% 19.83/2.98  
% 19.83/2.98  ------ Schedule dynamic 5 is on 
% 19.83/2.98  
% 19.83/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  ------ 
% 19.83/2.98  Current options:
% 19.83/2.98  ------ 
% 19.83/2.98  
% 19.83/2.98  ------ Input Options
% 19.83/2.98  
% 19.83/2.98  --out_options                           all
% 19.83/2.98  --tptp_safe_out                         true
% 19.83/2.98  --problem_path                          ""
% 19.83/2.98  --include_path                          ""
% 19.83/2.98  --clausifier                            res/vclausify_rel
% 19.83/2.98  --clausifier_options                    --mode clausify
% 19.83/2.98  --stdin                                 false
% 19.83/2.98  --stats_out                             all
% 19.83/2.98  
% 19.83/2.98  ------ General Options
% 19.83/2.98  
% 19.83/2.98  --fof                                   false
% 19.83/2.98  --time_out_real                         305.
% 19.83/2.98  --time_out_virtual                      -1.
% 19.83/2.98  --symbol_type_check                     false
% 19.83/2.98  --clausify_out                          false
% 19.83/2.98  --sig_cnt_out                           false
% 19.83/2.98  --trig_cnt_out                          false
% 19.83/2.98  --trig_cnt_out_tolerance                1.
% 19.83/2.98  --trig_cnt_out_sk_spl                   false
% 19.83/2.98  --abstr_cl_out                          false
% 19.83/2.98  
% 19.83/2.98  ------ Global Options
% 19.83/2.98  
% 19.83/2.98  --schedule                              default
% 19.83/2.98  --add_important_lit                     false
% 19.83/2.98  --prop_solver_per_cl                    1000
% 19.83/2.98  --min_unsat_core                        false
% 19.83/2.98  --soft_assumptions                      false
% 19.83/2.98  --soft_lemma_size                       3
% 19.83/2.98  --prop_impl_unit_size                   0
% 19.83/2.98  --prop_impl_unit                        []
% 19.83/2.98  --share_sel_clauses                     true
% 19.83/2.98  --reset_solvers                         false
% 19.83/2.98  --bc_imp_inh                            [conj_cone]
% 19.83/2.98  --conj_cone_tolerance                   3.
% 19.83/2.98  --extra_neg_conj                        none
% 19.83/2.98  --large_theory_mode                     true
% 19.83/2.98  --prolific_symb_bound                   200
% 19.83/2.98  --lt_threshold                          2000
% 19.83/2.98  --clause_weak_htbl                      true
% 19.83/2.98  --gc_record_bc_elim                     false
% 19.83/2.98  
% 19.83/2.98  ------ Preprocessing Options
% 19.83/2.98  
% 19.83/2.98  --preprocessing_flag                    true
% 19.83/2.98  --time_out_prep_mult                    0.1
% 19.83/2.98  --splitting_mode                        input
% 19.83/2.98  --splitting_grd                         true
% 19.83/2.98  --splitting_cvd                         false
% 19.83/2.98  --splitting_cvd_svl                     false
% 19.83/2.98  --splitting_nvd                         32
% 19.83/2.98  --sub_typing                            true
% 19.83/2.98  --prep_gs_sim                           true
% 19.83/2.98  --prep_unflatten                        true
% 19.83/2.98  --prep_res_sim                          true
% 19.83/2.98  --prep_upred                            true
% 19.83/2.98  --prep_sem_filter                       exhaustive
% 19.83/2.98  --prep_sem_filter_out                   false
% 19.83/2.98  --pred_elim                             true
% 19.83/2.98  --res_sim_input                         true
% 19.83/2.98  --eq_ax_congr_red                       true
% 19.83/2.98  --pure_diseq_elim                       true
% 19.83/2.98  --brand_transform                       false
% 19.83/2.98  --non_eq_to_eq                          false
% 19.83/2.98  --prep_def_merge                        true
% 19.83/2.98  --prep_def_merge_prop_impl              false
% 19.83/2.98  --prep_def_merge_mbd                    true
% 19.83/2.98  --prep_def_merge_tr_red                 false
% 19.83/2.98  --prep_def_merge_tr_cl                  false
% 19.83/2.98  --smt_preprocessing                     true
% 19.83/2.98  --smt_ac_axioms                         fast
% 19.83/2.98  --preprocessed_out                      false
% 19.83/2.98  --preprocessed_stats                    false
% 19.83/2.98  
% 19.83/2.98  ------ Abstraction refinement Options
% 19.83/2.98  
% 19.83/2.98  --abstr_ref                             []
% 19.83/2.98  --abstr_ref_prep                        false
% 19.83/2.98  --abstr_ref_until_sat                   false
% 19.83/2.98  --abstr_ref_sig_restrict                funpre
% 19.83/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.83/2.98  --abstr_ref_under                       []
% 19.83/2.98  
% 19.83/2.98  ------ SAT Options
% 19.83/2.98  
% 19.83/2.98  --sat_mode                              false
% 19.83/2.98  --sat_fm_restart_options                ""
% 19.83/2.98  --sat_gr_def                            false
% 19.83/2.98  --sat_epr_types                         true
% 19.83/2.98  --sat_non_cyclic_types                  false
% 19.83/2.98  --sat_finite_models                     false
% 19.83/2.98  --sat_fm_lemmas                         false
% 19.83/2.98  --sat_fm_prep                           false
% 19.83/2.98  --sat_fm_uc_incr                        true
% 19.83/2.98  --sat_out_model                         small
% 19.83/2.98  --sat_out_clauses                       false
% 19.83/2.98  
% 19.83/2.98  ------ QBF Options
% 19.83/2.98  
% 19.83/2.98  --qbf_mode                              false
% 19.83/2.98  --qbf_elim_univ                         false
% 19.83/2.98  --qbf_dom_inst                          none
% 19.83/2.98  --qbf_dom_pre_inst                      false
% 19.83/2.98  --qbf_sk_in                             false
% 19.83/2.98  --qbf_pred_elim                         true
% 19.83/2.98  --qbf_split                             512
% 19.83/2.98  
% 19.83/2.98  ------ BMC1 Options
% 19.83/2.98  
% 19.83/2.98  --bmc1_incremental                      false
% 19.83/2.98  --bmc1_axioms                           reachable_all
% 19.83/2.98  --bmc1_min_bound                        0
% 19.83/2.98  --bmc1_max_bound                        -1
% 19.83/2.98  --bmc1_max_bound_default                -1
% 19.83/2.98  --bmc1_symbol_reachability              true
% 19.83/2.98  --bmc1_property_lemmas                  false
% 19.83/2.98  --bmc1_k_induction                      false
% 19.83/2.98  --bmc1_non_equiv_states                 false
% 19.83/2.98  --bmc1_deadlock                         false
% 19.83/2.98  --bmc1_ucm                              false
% 19.83/2.98  --bmc1_add_unsat_core                   none
% 19.83/2.98  --bmc1_unsat_core_children              false
% 19.83/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.83/2.98  --bmc1_out_stat                         full
% 19.83/2.98  --bmc1_ground_init                      false
% 19.83/2.98  --bmc1_pre_inst_next_state              false
% 19.83/2.98  --bmc1_pre_inst_state                   false
% 19.83/2.98  --bmc1_pre_inst_reach_state             false
% 19.83/2.98  --bmc1_out_unsat_core                   false
% 19.83/2.98  --bmc1_aig_witness_out                  false
% 19.83/2.98  --bmc1_verbose                          false
% 19.83/2.98  --bmc1_dump_clauses_tptp                false
% 19.83/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.83/2.98  --bmc1_dump_file                        -
% 19.83/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.83/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.83/2.98  --bmc1_ucm_extend_mode                  1
% 19.83/2.98  --bmc1_ucm_init_mode                    2
% 19.83/2.98  --bmc1_ucm_cone_mode                    none
% 19.83/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.83/2.98  --bmc1_ucm_relax_model                  4
% 19.83/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.83/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.83/2.98  --bmc1_ucm_layered_model                none
% 19.83/2.98  --bmc1_ucm_max_lemma_size               10
% 19.83/2.98  
% 19.83/2.98  ------ AIG Options
% 19.83/2.98  
% 19.83/2.98  --aig_mode                              false
% 19.83/2.98  
% 19.83/2.98  ------ Instantiation Options
% 19.83/2.98  
% 19.83/2.98  --instantiation_flag                    true
% 19.83/2.98  --inst_sos_flag                         false
% 19.83/2.98  --inst_sos_phase                        true
% 19.83/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.83/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.83/2.98  --inst_lit_sel_side                     none
% 19.83/2.98  --inst_solver_per_active                1400
% 19.83/2.98  --inst_solver_calls_frac                1.
% 19.83/2.98  --inst_passive_queue_type               priority_queues
% 19.83/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.83/2.98  --inst_passive_queues_freq              [25;2]
% 19.83/2.98  --inst_dismatching                      true
% 19.83/2.98  --inst_eager_unprocessed_to_passive     true
% 19.83/2.98  --inst_prop_sim_given                   true
% 19.83/2.98  --inst_prop_sim_new                     false
% 19.83/2.98  --inst_subs_new                         false
% 19.83/2.98  --inst_eq_res_simp                      false
% 19.83/2.98  --inst_subs_given                       false
% 19.83/2.98  --inst_orphan_elimination               true
% 19.83/2.98  --inst_learning_loop_flag               true
% 19.83/2.98  --inst_learning_start                   3000
% 19.83/2.98  --inst_learning_factor                  2
% 19.83/2.98  --inst_start_prop_sim_after_learn       3
% 19.83/2.98  --inst_sel_renew                        solver
% 19.83/2.98  --inst_lit_activity_flag                true
% 19.83/2.98  --inst_restr_to_given                   false
% 19.83/2.98  --inst_activity_threshold               500
% 19.83/2.98  --inst_out_proof                        true
% 19.83/2.98  
% 19.83/2.98  ------ Resolution Options
% 19.83/2.98  
% 19.83/2.98  --resolution_flag                       false
% 19.83/2.98  --res_lit_sel                           adaptive
% 19.83/2.98  --res_lit_sel_side                      none
% 19.83/2.98  --res_ordering                          kbo
% 19.83/2.98  --res_to_prop_solver                    active
% 19.83/2.98  --res_prop_simpl_new                    false
% 19.83/2.98  --res_prop_simpl_given                  true
% 19.83/2.98  --res_passive_queue_type                priority_queues
% 19.83/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.83/2.98  --res_passive_queues_freq               [15;5]
% 19.83/2.98  --res_forward_subs                      full
% 19.83/2.98  --res_backward_subs                     full
% 19.83/2.98  --res_forward_subs_resolution           true
% 19.83/2.98  --res_backward_subs_resolution          true
% 19.83/2.98  --res_orphan_elimination                true
% 19.83/2.98  --res_time_limit                        2.
% 19.83/2.98  --res_out_proof                         true
% 19.83/2.98  
% 19.83/2.98  ------ Superposition Options
% 19.83/2.98  
% 19.83/2.98  --superposition_flag                    true
% 19.83/2.98  --sup_passive_queue_type                priority_queues
% 19.83/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.83/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.83/2.98  --demod_completeness_check              fast
% 19.83/2.98  --demod_use_ground                      true
% 19.83/2.98  --sup_to_prop_solver                    passive
% 19.83/2.98  --sup_prop_simpl_new                    true
% 19.83/2.98  --sup_prop_simpl_given                  true
% 19.83/2.98  --sup_fun_splitting                     false
% 19.83/2.98  --sup_smt_interval                      50000
% 19.83/2.98  
% 19.83/2.98  ------ Superposition Simplification Setup
% 19.83/2.98  
% 19.83/2.98  --sup_indices_passive                   []
% 19.83/2.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.83/2.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.83/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.83/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.83/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.83/2.98  --sup_full_bw                           [BwDemod]
% 19.83/2.98  --sup_immed_triv                        [TrivRules]
% 19.83/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.83/2.98  --sup_immed_bw_main                     []
% 19.83/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.83/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.83/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.83/2.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.83/2.98  
% 19.83/2.98  ------ Combination Options
% 19.83/2.98  
% 19.83/2.98  --comb_res_mult                         3
% 19.83/2.98  --comb_sup_mult                         2
% 19.83/2.98  --comb_inst_mult                        10
% 19.83/2.98  
% 19.83/2.98  ------ Debug Options
% 19.83/2.98  
% 19.83/2.98  --dbg_backtrace                         false
% 19.83/2.98  --dbg_dump_prop_clauses                 false
% 19.83/2.98  --dbg_dump_prop_clauses_file            -
% 19.83/2.98  --dbg_out_stat                          false
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  ------ Proving...
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  % SZS status Theorem for theBenchmark.p
% 19.83/2.98  
% 19.83/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.83/2.98  
% 19.83/2.98  fof(f18,conjecture,(
% 19.83/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f19,negated_conjecture,(
% 19.83/2.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 19.83/2.98    inference(negated_conjecture,[],[f18])).
% 19.83/2.98  
% 19.83/2.98  fof(f31,plain,(
% 19.83/2.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.83/2.98    inference(ennf_transformation,[],[f19])).
% 19.83/2.98  
% 19.83/2.98  fof(f35,plain,(
% 19.83/2.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.83/2.98    introduced(choice_axiom,[])).
% 19.83/2.98  
% 19.83/2.98  fof(f34,plain,(
% 19.83/2.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.83/2.98    introduced(choice_axiom,[])).
% 19.83/2.98  
% 19.83/2.98  fof(f33,plain,(
% 19.83/2.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 19.83/2.98    introduced(choice_axiom,[])).
% 19.83/2.98  
% 19.83/2.98  fof(f36,plain,(
% 19.83/2.98    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 19.83/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35,f34,f33])).
% 19.83/2.98  
% 19.83/2.98  fof(f57,plain,(
% 19.83/2.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.83/2.98    inference(cnf_transformation,[],[f36])).
% 19.83/2.98  
% 19.83/2.98  fof(f15,axiom,(
% 19.83/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f32,plain,(
% 19.83/2.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.83/2.98    inference(nnf_transformation,[],[f15])).
% 19.83/2.98  
% 19.83/2.98  fof(f51,plain,(
% 19.83/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.83/2.98    inference(cnf_transformation,[],[f32])).
% 19.83/2.98  
% 19.83/2.98  fof(f56,plain,(
% 19.83/2.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.83/2.98    inference(cnf_transformation,[],[f36])).
% 19.83/2.98  
% 19.83/2.98  fof(f14,axiom,(
% 19.83/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f25,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.83/2.98    inference(ennf_transformation,[],[f14])).
% 19.83/2.98  
% 19.83/2.98  fof(f26,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.83/2.98    inference(flattening,[],[f25])).
% 19.83/2.98  
% 19.83/2.98  fof(f50,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.83/2.98    inference(cnf_transformation,[],[f26])).
% 19.83/2.98  
% 19.83/2.98  fof(f10,axiom,(
% 19.83/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f46,plain,(
% 19.83/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.83/2.98    inference(cnf_transformation,[],[f10])).
% 19.83/2.98  
% 19.83/2.98  fof(f4,axiom,(
% 19.83/2.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f40,plain,(
% 19.83/2.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f4])).
% 19.83/2.98  
% 19.83/2.98  fof(f5,axiom,(
% 19.83/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f41,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f5])).
% 19.83/2.98  
% 19.83/2.98  fof(f6,axiom,(
% 19.83/2.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f42,plain,(
% 19.83/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f6])).
% 19.83/2.98  
% 19.83/2.98  fof(f7,axiom,(
% 19.83/2.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f43,plain,(
% 19.83/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f7])).
% 19.83/2.98  
% 19.83/2.98  fof(f8,axiom,(
% 19.83/2.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f44,plain,(
% 19.83/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f8])).
% 19.83/2.98  
% 19.83/2.98  fof(f9,axiom,(
% 19.83/2.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f45,plain,(
% 19.83/2.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f9])).
% 19.83/2.98  
% 19.83/2.98  fof(f59,plain,(
% 19.83/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f44,f45])).
% 19.83/2.98  
% 19.83/2.98  fof(f60,plain,(
% 19.83/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f43,f59])).
% 19.83/2.98  
% 19.83/2.98  fof(f61,plain,(
% 19.83/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f42,f60])).
% 19.83/2.98  
% 19.83/2.98  fof(f62,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f41,f61])).
% 19.83/2.98  
% 19.83/2.98  fof(f63,plain,(
% 19.83/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f40,f62])).
% 19.83/2.98  
% 19.83/2.98  fof(f64,plain,(
% 19.83/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.83/2.98    inference(definition_unfolding,[],[f46,f63])).
% 19.83/2.98  
% 19.83/2.98  fof(f68,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.83/2.98    inference(definition_unfolding,[],[f50,f64])).
% 19.83/2.98  
% 19.83/2.98  fof(f52,plain,(
% 19.83/2.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f32])).
% 19.83/2.98  
% 19.83/2.98  fof(f1,axiom,(
% 19.83/2.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f20,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 19.83/2.98    inference(ennf_transformation,[],[f1])).
% 19.83/2.98  
% 19.83/2.98  fof(f37,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f20])).
% 19.83/2.98  
% 19.83/2.98  fof(f65,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f37,f64])).
% 19.83/2.98  
% 19.83/2.98  fof(f17,axiom,(
% 19.83/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f29,plain,(
% 19.83/2.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.83/2.98    inference(ennf_transformation,[],[f17])).
% 19.83/2.98  
% 19.83/2.98  fof(f30,plain,(
% 19.83/2.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.83/2.98    inference(flattening,[],[f29])).
% 19.83/2.98  
% 19.83/2.98  fof(f54,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f30])).
% 19.83/2.98  
% 19.83/2.98  fof(f55,plain,(
% 19.83/2.98    l1_pre_topc(sK0)),
% 19.83/2.98    inference(cnf_transformation,[],[f36])).
% 19.83/2.98  
% 19.83/2.98  fof(f16,axiom,(
% 19.83/2.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f27,plain,(
% 19.83/2.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.83/2.98    inference(ennf_transformation,[],[f16])).
% 19.83/2.98  
% 19.83/2.98  fof(f28,plain,(
% 19.83/2.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.83/2.98    inference(flattening,[],[f27])).
% 19.83/2.98  
% 19.83/2.98  fof(f53,plain,(
% 19.83/2.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f28])).
% 19.83/2.98  
% 19.83/2.98  fof(f3,axiom,(
% 19.83/2.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f21,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 19.83/2.98    inference(ennf_transformation,[],[f3])).
% 19.83/2.98  
% 19.83/2.98  fof(f22,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 19.83/2.98    inference(flattening,[],[f21])).
% 19.83/2.98  
% 19.83/2.98  fof(f39,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 19.83/2.98    inference(cnf_transformation,[],[f22])).
% 19.83/2.98  
% 19.83/2.98  fof(f67,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 19.83/2.98    inference(definition_unfolding,[],[f39,f64])).
% 19.83/2.98  
% 19.83/2.98  fof(f58,plain,(
% 19.83/2.98    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 19.83/2.98    inference(cnf_transformation,[],[f36])).
% 19.83/2.98  
% 19.83/2.98  fof(f13,axiom,(
% 19.83/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f23,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.83/2.98    inference(ennf_transformation,[],[f13])).
% 19.83/2.98  
% 19.83/2.98  fof(f24,plain,(
% 19.83/2.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.83/2.98    inference(flattening,[],[f23])).
% 19.83/2.98  
% 19.83/2.98  fof(f49,plain,(
% 19.83/2.98    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.83/2.98    inference(cnf_transformation,[],[f24])).
% 19.83/2.98  
% 19.83/2.98  fof(f2,axiom,(
% 19.83/2.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f38,plain,(
% 19.83/2.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.83/2.98    inference(cnf_transformation,[],[f2])).
% 19.83/2.98  
% 19.83/2.98  fof(f66,plain,(
% 19.83/2.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.83/2.98    inference(definition_unfolding,[],[f38,f64])).
% 19.83/2.98  
% 19.83/2.98  fof(f11,axiom,(
% 19.83/2.98    ! [X0] : k2_subset_1(X0) = X0),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f47,plain,(
% 19.83/2.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 19.83/2.98    inference(cnf_transformation,[],[f11])).
% 19.83/2.98  
% 19.83/2.98  fof(f12,axiom,(
% 19.83/2.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 19.83/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.83/2.98  
% 19.83/2.98  fof(f48,plain,(
% 19.83/2.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 19.83/2.98    inference(cnf_transformation,[],[f12])).
% 19.83/2.98  
% 19.83/2.98  cnf(c_357,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.83/2.98      theory(equality) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_916,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK2) | X2 != X0 | sK2 != X1 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_357]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1651,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,sK2) | r1_tarski(X1,sK2) | X1 != X0 | sK2 != sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_916]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_5887,plain,
% 19.83/2.98      ( r1_tarski(X0,sK2)
% 19.83/2.98      | ~ r1_tarski(k2_subset_1(sK2),sK2)
% 19.83/2.98      | X0 != k2_subset_1(sK2)
% 19.83/2.98      | sK2 != sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_1651]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_74973,plain,
% 19.83/2.98      ( ~ r1_tarski(k2_subset_1(sK2),sK2)
% 19.83/2.98      | r1_tarski(sK2,sK2)
% 19.83/2.98      | sK2 != k2_subset_1(sK2)
% 19.83/2.98      | sK2 != sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_5887]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_12,negated_conjecture,
% 19.83/2.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.83/2.98      inference(cnf_transformation,[],[f57]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_680,plain,
% 19.83/2.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_8,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.83/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_682,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.83/2.98      | r1_tarski(X0,X1) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1103,plain,
% 19.83/2.98      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_680,c_682]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_13,negated_conjecture,
% 19.83/2.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.83/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_679,plain,
% 19.83/2.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1104,plain,
% 19.83/2.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_679,c_682]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_6,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.83/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.83/2.98      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 19.83/2.98      inference(cnf_transformation,[],[f68]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_7,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.83/2.98      inference(cnf_transformation,[],[f52]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_109,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.83/2.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_110,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.83/2.98      inference(renaming,[status(thm)],[c_109]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_135,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.83/2.98      | ~ r1_tarski(X2,X1)
% 19.83/2.98      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 19.83/2.98      inference(bin_hyper_res,[status(thm)],[c_6,c_110]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_274,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.83/2.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_275,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.83/2.98      inference(renaming,[status(thm)],[c_274]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_299,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1)
% 19.83/2.98      | ~ r1_tarski(X2,X1)
% 19.83/2.98      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 19.83/2.98      inference(bin_hyper_res,[status(thm)],[c_135,c_275]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_675,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 19.83/2.98      | r1_tarski(X0,X2) != iProver_top
% 19.83/2.98      | r1_tarski(X1,X2) != iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1810,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 19.83/2.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_1104,c_675]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_2252,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_1103,c_1810]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_0,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1)
% 19.83/2.98      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 19.83/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_687,plain,
% 19.83/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.83/2.98      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_2392,plain,
% 19.83/2.98      ( r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top
% 19.83/2.98      | r1_tarski(X0,sK2) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_2252,c_687]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_10,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | ~ r1_tarski(X0,X2)
% 19.83/2.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.83/2.98      | ~ l1_pre_topc(X1) ),
% 19.83/2.98      inference(cnf_transformation,[],[f54]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_14,negated_conjecture,
% 19.83/2.98      ( l1_pre_topc(sK0) ),
% 19.83/2.98      inference(cnf_transformation,[],[f55]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_191,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | ~ r1_tarski(X0,X2)
% 19.83/2.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.83/2.98      | sK0 != X1 ),
% 19.83/2.98      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_192,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.83/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.83/2.98      | ~ r1_tarski(X1,X0)
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 19.83/2.98      inference(unflattening,[status(thm)],[c_191]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_678,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | r1_tarski(X1,X0) != iProver_top
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_9,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | ~ l1_pre_topc(X1) ),
% 19.83/2.98      inference(cnf_transformation,[],[f53]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_209,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.83/2.98      | sK0 != X1 ),
% 19.83/2.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_210,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.83/2.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.83/2.98      inference(unflattening,[status(thm)],[c_209]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_677,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1105,plain,
% 19.83/2.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_677,c_682]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1817,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),k1_tops_1(sK0,X0),X1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),X1)
% 19.83/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_1105,c_675]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_8928,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0)
% 19.83/2.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_679,c_1817]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_9814,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 19.83/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_1105,c_8928]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_55473,plain,
% 19.83/2.98      ( k3_tarski(k6_enumset1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_680,c_9814]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_2,plain,
% 19.83/2.98      ( ~ r1_tarski(X0,X1)
% 19.83/2.98      | ~ r1_tarski(X2,X1)
% 19.83/2.98      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 19.83/2.98      inference(cnf_transformation,[],[f67]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_685,plain,
% 19.83/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.83/2.98      | r1_tarski(X2,X1) != iProver_top
% 19.83/2.98      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_56276,plain,
% 19.83/2.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),X0) = iProver_top
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_55473,c_685]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_11,negated_conjecture,
% 19.83/2.98      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 19.83/2.98      inference(cnf_transformation,[],[f58]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_681,plain,
% 19.83/2.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_57968,plain,
% 19.83/2.98      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_56276,c_681]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_58736,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
% 19.83/2.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_678,c_57968]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_17,plain,
% 19.83/2.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_5,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.83/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.83/2.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 19.83/2.98      inference(cnf_transformation,[],[f49]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_134,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.83/2.98      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 19.83/2.98      | ~ r1_tarski(X2,X1) ),
% 19.83/2.98      inference(bin_hyper_res,[status(thm)],[c_5,c_110]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_298,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 19.83/2.98      | ~ r1_tarski(X1,X0)
% 19.83/2.98      | ~ r1_tarski(X2,X0) ),
% 19.83/2.98      inference(bin_hyper_res,[status(thm)],[c_134,c_275]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_812,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.83/2.98      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 19.83/2.98      | ~ r1_tarski(X1,u1_struct_0(sK0)) ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_298]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_7339,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.83/2.98      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 19.83/2.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_812]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_16705,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.83/2.98      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 19.83/2.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_7339]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_16706,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.83/2.98      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 19.83/2.98      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_16705]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_74127,plain,
% 19.83/2.98      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
% 19.83/2.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
% 19.83/2.98      inference(global_propositional_subsumption,
% 19.83/2.98                [status(thm)],
% 19.83/2.98                [c_58736,c_17,c_1103,c_1104,c_16706]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_74133,plain,
% 19.83/2.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.83/2.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top
% 19.83/2.98      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_678,c_74127]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_16,plain,
% 19.83/2.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1,plain,
% 19.83/2.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 19.83/2.98      inference(cnf_transformation,[],[f66]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_686,plain,
% 19.83/2.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 19.83/2.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_2394,plain,
% 19.83/2.98      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_2252,c_686]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_74248,plain,
% 19.83/2.98      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != iProver_top ),
% 19.83/2.98      inference(global_propositional_subsumption,
% 19.83/2.98                [status(thm)],
% 19.83/2.98                [c_74133,c_16,c_1103,c_1104,c_2394,c_16706]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_74253,plain,
% 19.83/2.98      ( r1_tarski(sK2,sK2) != iProver_top ),
% 19.83/2.98      inference(superposition,[status(thm)],[c_2392,c_74248]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_74254,plain,
% 19.83/2.98      ( ~ r1_tarski(sK2,sK2) ),
% 19.83/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_74253]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_355,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1655,plain,
% 19.83/2.98      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_355]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_5895,plain,
% 19.83/2.98      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_1655]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_58680,plain,
% 19.83/2.98      ( k2_subset_1(sK2) != sK2 | sK2 = k2_subset_1(sK2) | sK2 != sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_5895]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_3,plain,
% 19.83/2.98      ( k2_subset_1(X0) = X0 ),
% 19.83/2.98      inference(cnf_transformation,[],[f47]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_15765,plain,
% 19.83/2.98      ( k2_subset_1(sK2) = sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_3]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_354,plain,( X0 = X0 ),theory(equality) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1652,plain,
% 19.83/2.98      ( sK2 = sK2 ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_354]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_4,plain,
% 19.83/2.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 19.83/2.98      inference(cnf_transformation,[],[f48]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1448,plain,
% 19.83/2.98      ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_4]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_901,plain,
% 19.83/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_8]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(c_1447,plain,
% 19.83/2.98      ( ~ m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2))
% 19.83/2.98      | r1_tarski(k2_subset_1(sK2),sK2) ),
% 19.83/2.98      inference(instantiation,[status(thm)],[c_901]) ).
% 19.83/2.98  
% 19.83/2.98  cnf(contradiction,plain,
% 19.83/2.98      ( $false ),
% 19.83/2.98      inference(minisat,
% 19.83/2.98                [status(thm)],
% 19.83/2.98                [c_74973,c_74254,c_58680,c_15765,c_1652,c_1448,c_1447]) ).
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.83/2.98  
% 19.83/2.98  ------                               Statistics
% 19.83/2.98  
% 19.83/2.98  ------ General
% 19.83/2.98  
% 19.83/2.98  abstr_ref_over_cycles:                  0
% 19.83/2.98  abstr_ref_under_cycles:                 0
% 19.83/2.98  gc_basic_clause_elim:                   0
% 19.83/2.98  forced_gc_time:                         0
% 19.83/2.98  parsing_time:                           0.01
% 19.83/2.98  unif_index_cands_time:                  0.
% 19.83/2.98  unif_index_add_time:                    0.
% 19.83/2.98  orderings_time:                         0.
% 19.83/2.98  out_proof_time:                         0.017
% 19.83/2.98  total_time:                             2.276
% 19.83/2.98  num_of_symbols:                         44
% 19.83/2.98  num_of_terms:                           52667
% 19.83/2.98  
% 19.83/2.98  ------ Preprocessing
% 19.83/2.98  
% 19.83/2.98  num_of_splits:                          0
% 19.83/2.98  num_of_split_atoms:                     0
% 19.83/2.98  num_of_reused_defs:                     0
% 19.83/2.98  num_eq_ax_congr_red:                    27
% 19.83/2.98  num_of_sem_filtered_clauses:            1
% 19.83/2.98  num_of_subtypes:                        0
% 19.83/2.98  monotx_restored_types:                  0
% 19.83/2.98  sat_num_of_epr_types:                   0
% 19.83/2.98  sat_num_of_non_cyclic_types:            0
% 19.83/2.98  sat_guarded_non_collapsed_types:        0
% 19.83/2.98  num_pure_diseq_elim:                    0
% 19.83/2.98  simp_replaced_by:                       0
% 19.83/2.98  res_preprocessed:                       76
% 19.83/2.98  prep_upred:                             0
% 19.83/2.98  prep_unflattend:                        2
% 19.83/2.98  smt_new_axioms:                         0
% 19.83/2.98  pred_elim_cands:                        2
% 19.83/2.98  pred_elim:                              1
% 19.83/2.98  pred_elim_cl:                           1
% 19.83/2.98  pred_elim_cycles:                       3
% 19.83/2.98  merged_defs:                            8
% 19.83/2.98  merged_defs_ncl:                        0
% 19.83/2.98  bin_hyper_res:                          12
% 19.83/2.98  prep_cycles:                            4
% 19.83/2.98  pred_elim_time:                         0.001
% 19.83/2.98  splitting_time:                         0.
% 19.83/2.98  sem_filter_time:                        0.
% 19.83/2.98  monotx_time:                            0.
% 19.83/2.98  subtype_inf_time:                       0.
% 19.83/2.98  
% 19.83/2.98  ------ Problem properties
% 19.83/2.98  
% 19.83/2.98  clauses:                                14
% 19.83/2.98  conjectures:                            3
% 19.83/2.98  epr:                                    0
% 19.83/2.98  horn:                                   14
% 19.83/2.98  ground:                                 3
% 19.83/2.98  unary:                                  6
% 19.83/2.98  binary:                                 4
% 19.83/2.98  lits:                                   27
% 19.83/2.98  lits_eq:                                2
% 19.83/2.98  fd_pure:                                0
% 19.83/2.98  fd_pseudo:                              0
% 19.83/2.98  fd_cond:                                0
% 19.83/2.98  fd_pseudo_cond:                         0
% 19.83/2.98  ac_symbols:                             0
% 19.83/2.98  
% 19.83/2.98  ------ Propositional Solver
% 19.83/2.98  
% 19.83/2.98  prop_solver_calls:                      34
% 19.83/2.98  prop_fast_solver_calls:                 1181
% 19.83/2.98  smt_solver_calls:                       0
% 19.83/2.98  smt_fast_solver_calls:                  0
% 19.83/2.98  prop_num_of_clauses:                    25377
% 19.83/2.98  prop_preprocess_simplified:             19091
% 19.83/2.98  prop_fo_subsumed:                       13
% 19.83/2.98  prop_solver_time:                       0.
% 19.83/2.98  smt_solver_time:                        0.
% 19.83/2.98  smt_fast_solver_time:                   0.
% 19.83/2.98  prop_fast_solver_time:                  0.
% 19.83/2.98  prop_unsat_core_time:                   0.002
% 19.83/2.98  
% 19.83/2.98  ------ QBF
% 19.83/2.98  
% 19.83/2.98  qbf_q_res:                              0
% 19.83/2.98  qbf_num_tautologies:                    0
% 19.83/2.98  qbf_prep_cycles:                        0
% 19.83/2.98  
% 19.83/2.98  ------ BMC1
% 19.83/2.98  
% 19.83/2.98  bmc1_current_bound:                     -1
% 19.83/2.98  bmc1_last_solved_bound:                 -1
% 19.83/2.98  bmc1_unsat_core_size:                   -1
% 19.83/2.98  bmc1_unsat_core_parents_size:           -1
% 19.83/2.98  bmc1_merge_next_fun:                    0
% 19.83/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.83/2.98  
% 19.83/2.98  ------ Instantiation
% 19.83/2.98  
% 19.83/2.98  inst_num_of_clauses:                    3247
% 19.83/2.98  inst_num_in_passive:                    1141
% 19.83/2.98  inst_num_in_active:                     2014
% 19.83/2.98  inst_num_in_unprocessed:                91
% 19.83/2.98  inst_num_of_loops:                      2139
% 19.83/2.98  inst_num_of_learning_restarts:          0
% 19.83/2.98  inst_num_moves_active_passive:          122
% 19.83/2.98  inst_lit_activity:                      0
% 19.83/2.98  inst_lit_activity_moves:                1
% 19.83/2.98  inst_num_tautologies:                   0
% 19.83/2.98  inst_num_prop_implied:                  0
% 19.83/2.98  inst_num_existing_simplified:           0
% 19.83/2.98  inst_num_eq_res_simplified:             0
% 19.83/2.98  inst_num_child_elim:                    0
% 19.83/2.98  inst_num_of_dismatching_blockings:      1838
% 19.83/2.98  inst_num_of_non_proper_insts:           5351
% 19.83/2.98  inst_num_of_duplicates:                 0
% 19.83/2.98  inst_inst_num_from_inst_to_res:         0
% 19.83/2.98  inst_dismatching_checking_time:         0.
% 19.83/2.98  
% 19.83/2.98  ------ Resolution
% 19.83/2.98  
% 19.83/2.98  res_num_of_clauses:                     0
% 19.83/2.98  res_num_in_passive:                     0
% 19.83/2.98  res_num_in_active:                      0
% 19.83/2.98  res_num_of_loops:                       80
% 19.83/2.98  res_forward_subset_subsumed:            181
% 19.83/2.98  res_backward_subset_subsumed:           6
% 19.83/2.98  res_forward_subsumed:                   0
% 19.83/2.98  res_backward_subsumed:                  0
% 19.83/2.98  res_forward_subsumption_resolution:     0
% 19.83/2.98  res_backward_subsumption_resolution:    0
% 19.83/2.98  res_clause_to_clause_subsumption:       42451
% 19.83/2.98  res_orphan_elimination:                 0
% 19.83/2.98  res_tautology_del:                      142
% 19.83/2.98  res_num_eq_res_simplified:              0
% 19.83/2.98  res_num_sel_changes:                    0
% 19.83/2.98  res_moves_from_active_to_pass:          0
% 19.83/2.98  
% 19.83/2.98  ------ Superposition
% 19.83/2.98  
% 19.83/2.98  sup_time_total:                         0.
% 19.83/2.98  sup_time_generating:                    0.
% 19.83/2.98  sup_time_sim_full:                      0.
% 19.83/2.98  sup_time_sim_immed:                     0.
% 19.83/2.98  
% 19.83/2.98  sup_num_of_clauses:                     5332
% 19.83/2.98  sup_num_in_active:                      416
% 19.83/2.98  sup_num_in_passive:                     4916
% 19.83/2.98  sup_num_of_loops:                       426
% 19.83/2.98  sup_fw_superposition:                   2422
% 19.83/2.98  sup_bw_superposition:                   3487
% 19.83/2.98  sup_immediate_simplified:               483
% 19.83/2.98  sup_given_eliminated:                   0
% 19.83/2.98  comparisons_done:                       0
% 19.83/2.98  comparisons_avoided:                    0
% 19.83/2.98  
% 19.83/2.98  ------ Simplifications
% 19.83/2.98  
% 19.83/2.98  
% 19.83/2.98  sim_fw_subset_subsumed:                 2
% 19.83/2.98  sim_bw_subset_subsumed:                 38
% 19.83/2.98  sim_fw_subsumed:                        85
% 19.83/2.98  sim_bw_subsumed:                        191
% 19.83/2.98  sim_fw_subsumption_res:                 4
% 19.83/2.98  sim_bw_subsumption_res:                 0
% 19.83/2.98  sim_tautology_del:                      1
% 19.83/2.98  sim_eq_tautology_del:                   0
% 19.83/2.98  sim_eq_res_simp:                        0
% 19.83/2.98  sim_fw_demodulated:                     0
% 19.83/2.98  sim_bw_demodulated:                     13
% 19.83/2.98  sim_light_normalised:                   180
% 19.83/2.98  sim_joinable_taut:                      0
% 19.83/2.98  sim_joinable_simp:                      0
% 19.83/2.98  sim_ac_normalised:                      0
% 19.83/2.98  sim_smt_subsumption:                    0
% 19.83/2.98  
%------------------------------------------------------------------------------
