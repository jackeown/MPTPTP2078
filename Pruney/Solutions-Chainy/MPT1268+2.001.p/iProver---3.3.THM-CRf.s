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
% DateTime   : Thu Dec  3 12:15:01 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :  174 (1396 expanded)
%              Number of clauses        :  108 ( 422 expanded)
%              Number of leaves         :   22 ( 343 expanded)
%              Depth                    :   28
%              Number of atoms          :  547 (9042 expanded)
%              Number of equality atoms :  210 (1842 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,X0)
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,X0)
              & r1_tarski(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK1,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f62,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f43,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_423,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3448,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_423,c_1])).

cnf(c_22,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3833,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_22,c_11])).

cnf(c_16625,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | X1 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3448,c_3833])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1232,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1252,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_952,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8193,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_961])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1217,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_9095,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8193,c_27,c_28,c_1217])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_965,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9101,plain,
    ( k3_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_9095,c_965])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1527,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7,c_10])).

cnf(c_1918,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1527,c_10])).

cnf(c_9348,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_9101,c_1918])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2070,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1918,c_0])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_963,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2582,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_963])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_156])).

cnf(c_202,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_157])).

cnf(c_948,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_2689,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2582,c_948])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_201,plain,
    ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_157])).

cnf(c_949,plain,
    ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_3012,plain,
    ( m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2689,c_949])).

cnf(c_1307,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

cnf(c_1308,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_4401,plain,
    ( m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3012,c_1308])).

cnf(c_953,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4420,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK0) != iProver_top
    | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4401,c_953])).

cnf(c_4660,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top
    | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_4420])).

cnf(c_4734,plain,
    ( k3_xboole_0(sK1,X0) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top
    | r1_tarski(k3_xboole_0(sK1,X0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4660,c_2070])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1169,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1171,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_5807,plain,
    ( v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top
    | v2_tops_1(sK1,sK0) = iProver_top
    | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4734,c_1171])).

cnf(c_5808,plain,
    ( k3_xboole_0(sK1,X0) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5807])).

cnf(c_16051,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9348,c_5808])).

cnf(c_16075,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16051,c_9348])).

cnf(c_16128,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16075])).

cnf(c_16687,plain,
    ( v2_tops_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16625,c_25,c_24,c_23,c_1232,c_1252,c_16128])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_16926,plain,
    ( k1_xboole_0 != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16687,c_18])).

cnf(c_17300,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(resolution,[status(thm)],[c_16926,c_1])).

cnf(c_4408,plain,
    ( m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4401])).

cnf(c_4895,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4408,c_963])).

cnf(c_13700,plain,
    ( r1_tarski(k3_xboole_0(X0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_4895])).

cnf(c_964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3562,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_953])).

cnf(c_15203,plain,
    ( k3_xboole_0(X0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k3_xboole_0(X0,sK1),sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13700,c_3562])).

cnf(c_1253,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_17,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_958,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3404,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_958])).

cnf(c_3431,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3404])).

cnf(c_17118,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15203,c_25,c_24,c_27,c_23,c_28,c_1232,c_1252,c_1253,c_3431,c_16128])).

cnf(c_3812,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3404,c_27])).

cnf(c_3813,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3812])).

cnf(c_17131,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17118,c_3813])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_954,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_960,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6487,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_960])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_34,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7711,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6487,c_27,c_34])).

cnf(c_7712,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7711])).

cnf(c_7724,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_7712])).

cnf(c_20,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7962,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7724,c_33])).

cnf(c_7963,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7962])).

cnf(c_17208,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17131,c_7963])).

cnf(c_17259,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17208])).

cnf(c_17639,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17300,c_25,c_24,c_23,c_1232,c_1252,c_16128,c_17259])).

cnf(c_426,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_422,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3634,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_426,c_422])).

cnf(c_6944,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_3634,c_3833])).

cnf(c_7555,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,X0)
    | ~ r1_tarski(sK1,sK1)
    | r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_6944,c_1307])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_966,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1838,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_966])).

cnf(c_1844,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1838])).

cnf(c_7558,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7555,c_1844])).

cnf(c_17644,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17639,c_7558])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.45/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/1.49  
% 7.45/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.45/1.49  
% 7.45/1.49  ------  iProver source info
% 7.45/1.49  
% 7.45/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.45/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.45/1.49  git: non_committed_changes: false
% 7.45/1.49  git: last_make_outside_of_git: false
% 7.45/1.49  
% 7.45/1.49  ------ 
% 7.45/1.49  ------ Parsing...
% 7.45/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.45/1.49  
% 7.45/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.45/1.49  ------ Proving...
% 7.45/1.49  ------ Problem Properties 
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  clauses                                 25
% 7.45/1.49  conjectures                             8
% 7.45/1.49  EPR                                     7
% 7.45/1.49  Horn                                    24
% 7.45/1.49  unary                                   9
% 7.45/1.49  binary                                  9
% 7.45/1.49  lits                                    56
% 7.45/1.49  lits eq                                 11
% 7.45/1.49  fd_pure                                 0
% 7.45/1.49  fd_pseudo                               0
% 7.45/1.49  fd_cond                                 1
% 7.45/1.49  fd_pseudo_cond                          1
% 7.45/1.49  AC symbols                              0
% 7.45/1.49  
% 7.45/1.49  ------ Input Options Time Limit: Unbounded
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  ------ 
% 7.45/1.49  Current options:
% 7.45/1.49  ------ 
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  ------ Proving...
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  % SZS status Theorem for theBenchmark.p
% 7.45/1.49  
% 7.45/1.49   Resolution empty clause
% 7.45/1.49  
% 7.45/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.45/1.49  
% 7.45/1.49  fof(f1,axiom,(
% 7.45/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f29,plain,(
% 7.45/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.45/1.49    inference(nnf_transformation,[],[f1])).
% 7.45/1.49  
% 7.45/1.49  fof(f30,plain,(
% 7.45/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.45/1.49    inference(flattening,[],[f29])).
% 7.45/1.49  
% 7.45/1.49  fof(f42,plain,(
% 7.45/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f30])).
% 7.45/1.49  
% 7.45/1.49  fof(f16,conjecture,(
% 7.45/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f17,negated_conjecture,(
% 7.45/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 7.45/1.49    inference(negated_conjecture,[],[f16])).
% 7.45/1.49  
% 7.45/1.49  fof(f27,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f17])).
% 7.45/1.49  
% 7.45/1.49  fof(f28,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f27])).
% 7.45/1.49  
% 7.45/1.49  fof(f33,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(nnf_transformation,[],[f28])).
% 7.45/1.49  
% 7.45/1.49  fof(f34,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f33])).
% 7.45/1.49  
% 7.45/1.49  fof(f35,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.45/1.49    inference(rectify,[],[f34])).
% 7.45/1.49  
% 7.45/1.49  fof(f38,plain,(
% 7.45/1.49    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f37,plain,(
% 7.45/1.49    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f36,plain,(
% 7.45/1.49    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.45/1.49    introduced(choice_axiom,[])).
% 7.45/1.49  
% 7.45/1.49  fof(f39,plain,(
% 7.45/1.49    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.45/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).
% 7.45/1.49  
% 7.45/1.49  fof(f62,plain,(
% 7.45/1.49    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f11,axiom,(
% 7.45/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f31,plain,(
% 7.45/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.45/1.49    inference(nnf_transformation,[],[f11])).
% 7.45/1.49  
% 7.45/1.49  fof(f53,plain,(
% 7.45/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f31])).
% 7.45/1.49  
% 7.45/1.49  fof(f59,plain,(
% 7.45/1.49    v2_pre_topc(sK0)),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f60,plain,(
% 7.45/1.49    l1_pre_topc(sK0)),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f61,plain,(
% 7.45/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f12,axiom,(
% 7.45/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f21,plain,(
% 7.45/1.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f12])).
% 7.45/1.49  
% 7.45/1.49  fof(f22,plain,(
% 7.45/1.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f21])).
% 7.45/1.49  
% 7.45/1.49  fof(f54,plain,(
% 7.45/1.49    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f22])).
% 7.45/1.49  
% 7.45/1.49  fof(f15,axiom,(
% 7.45/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f26,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.49    inference(ennf_transformation,[],[f15])).
% 7.45/1.49  
% 7.45/1.49  fof(f32,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.49    inference(nnf_transformation,[],[f26])).
% 7.45/1.49  
% 7.45/1.49  fof(f58,plain,(
% 7.45/1.49    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f32])).
% 7.45/1.49  
% 7.45/1.49  fof(f13,axiom,(
% 7.45/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f23,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.49    inference(ennf_transformation,[],[f13])).
% 7.45/1.49  
% 7.45/1.49  fof(f55,plain,(
% 7.45/1.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f23])).
% 7.45/1.49  
% 7.45/1.49  fof(f4,axiom,(
% 7.45/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f18,plain,(
% 7.45/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.45/1.49    inference(ennf_transformation,[],[f4])).
% 7.45/1.49  
% 7.45/1.49  fof(f45,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f18])).
% 7.45/1.49  
% 7.45/1.49  fof(f7,axiom,(
% 7.45/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f48,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f7])).
% 7.45/1.49  
% 7.45/1.49  fof(f10,axiom,(
% 7.45/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f51,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f10])).
% 7.45/1.49  
% 7.45/1.49  fof(f6,axiom,(
% 7.45/1.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f47,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f6])).
% 7.45/1.49  
% 7.45/1.49  fof(f2,axiom,(
% 7.45/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f43,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f2])).
% 7.45/1.49  
% 7.45/1.49  fof(f67,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 7.45/1.49    inference(definition_unfolding,[],[f47,f43,f43])).
% 7.45/1.49  
% 7.45/1.49  fof(f52,plain,(
% 7.45/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f31])).
% 7.45/1.49  
% 7.45/1.49  fof(f9,axiom,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f20,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f9])).
% 7.45/1.49  
% 7.45/1.49  fof(f50,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f20])).
% 7.45/1.49  
% 7.45/1.49  fof(f68,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.45/1.49    inference(definition_unfolding,[],[f50,f43])).
% 7.45/1.49  
% 7.45/1.49  fof(f8,axiom,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f19,plain,(
% 7.45/1.49    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.45/1.49    inference(ennf_transformation,[],[f8])).
% 7.45/1.49  
% 7.45/1.49  fof(f49,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.45/1.49    inference(cnf_transformation,[],[f19])).
% 7.45/1.49  
% 7.45/1.49  fof(f3,axiom,(
% 7.45/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f44,plain,(
% 7.45/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f3])).
% 7.45/1.49  
% 7.45/1.49  fof(f66,plain,(
% 7.45/1.49    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f57,plain,(
% 7.45/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f32])).
% 7.45/1.49  
% 7.45/1.49  fof(f63,plain,(
% 7.45/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f14,axiom,(
% 7.45/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f24,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.49    inference(ennf_transformation,[],[f14])).
% 7.45/1.49  
% 7.45/1.49  fof(f25,plain,(
% 7.45/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.45/1.49    inference(flattening,[],[f24])).
% 7.45/1.49  
% 7.45/1.49  fof(f56,plain,(
% 7.45/1.49    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.45/1.49    inference(cnf_transformation,[],[f25])).
% 7.45/1.49  
% 7.45/1.49  fof(f65,plain,(
% 7.45/1.49    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f64,plain,(
% 7.45/1.49    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 7.45/1.49    inference(cnf_transformation,[],[f39])).
% 7.45/1.49  
% 7.45/1.49  fof(f5,axiom,(
% 7.45/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.45/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.45/1.49  
% 7.45/1.49  fof(f46,plain,(
% 7.45/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.45/1.49    inference(cnf_transformation,[],[f5])).
% 7.45/1.49  
% 7.45/1.49  cnf(c_423,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.45/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3448,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_423,c_1]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_22,negated_conjecture,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ v3_pre_topc(X0,sK0)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.45/1.49      | ~ r1_tarski(X0,sK1)
% 7.45/1.49      | k1_xboole_0 = X0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_11,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3833,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ v3_pre_topc(X0,sK0)
% 7.45/1.49      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 7.45/1.49      | ~ r1_tarski(X0,sK1)
% 7.45/1.49      | k1_xboole_0 = X0 ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_22,c_11]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16625,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ v3_pre_topc(X0,sK0)
% 7.45/1.49      | ~ r1_tarski(X1,X0)
% 7.45/1.49      | ~ r1_tarski(X0,X1)
% 7.45/1.49      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 7.45/1.49      | ~ r1_tarski(X0,sK1)
% 7.45/1.49      | X1 = k1_xboole_0 ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_3448,c_3833]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_25,negated_conjecture,
% 7.45/1.49      ( v2_pre_topc(sK0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_24,negated_conjecture,
% 7.45/1.49      ( l1_pre_topc(sK0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_23,negated_conjecture,
% 7.45/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_13,plain,
% 7.45/1.49      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.45/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.45/1.49      | ~ v2_pre_topc(X0)
% 7.45/1.49      | ~ l1_pre_topc(X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1232,plain,
% 7.45/1.49      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 7.45/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.45/1.49      | ~ v2_pre_topc(sK0)
% 7.45/1.49      | ~ l1_pre_topc(sK0) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16,plain,
% 7.45/1.49      ( v2_tops_1(X0,X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1252,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.45/1.49      | ~ l1_pre_topc(sK0)
% 7.45/1.49      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_952,plain,
% 7.45/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_14,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.49      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.45/1.49      | ~ l1_pre_topc(X1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_961,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.45/1.49      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 7.45/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8193,plain,
% 7.45/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.45/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_952,c_961]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_27,plain,
% 7.45/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_28,plain,
% 7.45/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1216,plain,
% 7.45/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.45/1.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 7.45/1.49      | ~ l1_pre_topc(sK0) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1217,plain,
% 7.45/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.45/1.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.45/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9095,plain,
% 7.45/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_8193,c_27,c_28,c_1217]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_965,plain,
% 7.45/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9101,plain,
% 7.45/1.49      ( k3_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9095,c_965]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7,plain,
% 7.45/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_10,plain,
% 7.45/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1527,plain,
% 7.45/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_7,c_10]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1918,plain,
% 7.45/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_1527,c_10]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9348,plain,
% 7.45/1.49      ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9101,c_1918]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_0,plain,
% 7.45/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_2070,plain,
% 7.45/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_1918,c_0]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_12,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_963,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.45/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_2582,plain,
% 7.45/1.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_952,c_963]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_9,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.45/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.45/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_156,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.45/1.49      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_157,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_156]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_202,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1)
% 7.45/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.45/1.49      inference(bin_hyper_res,[status(thm)],[c_9,c_157]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_948,plain,
% 7.45/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 7.45/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_2689,plain,
% 7.45/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_2582,c_948]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_8,plain,
% 7.45/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.45/1.49      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.45/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_201,plain,
% 7.45/1.49      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 7.45/1.49      | ~ r1_tarski(X1,X0) ),
% 7.45/1.49      inference(bin_hyper_res,[status(thm)],[c_8,c_157]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_949,plain,
% 7.45/1.49      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 7.45/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3012,plain,
% 7.45/1.49      ( m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.45/1.49      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_2689,c_949]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1307,plain,
% 7.45/1.49      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_12,c_23]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1308,plain,
% 7.45/1.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4401,plain,
% 7.45/1.49      ( m1_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3012,c_1308]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_953,plain,
% 7.45/1.49      ( k1_xboole_0 = X0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(X0,sK0) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.45/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4420,plain,
% 7.45/1.49      ( k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK0) != iProver_top
% 7.45/1.49      | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_4401,c_953]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4660,plain,
% 7.45/1.49      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top
% 7.45/1.49      | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))),sK1) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_2070,c_4420]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4734,plain,
% 7.45/1.49      ( k3_xboole_0(sK1,X0) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top
% 7.45/1.49      | r1_tarski(k3_xboole_0(sK1,X0),sK1) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_4660,c_2070]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4,plain,
% 7.45/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1169,plain,
% 7.45/1.49      ( r1_tarski(k3_xboole_0(sK1,X0),sK1) ),
% 7.45/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1171,plain,
% 7.45/1.49      ( r1_tarski(k3_xboole_0(sK1,X0),sK1) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_1169]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5807,plain,
% 7.45/1.49      ( v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4734,c_1171]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_5808,plain,
% 7.45/1.49      ( k3_xboole_0(sK1,X0) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_5807]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16051,plain,
% 7.45/1.49      ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_9348,c_5808]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16075,plain,
% 7.45/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_16051,c_9348]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16128,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 7.45/1.49      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.45/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_16075]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16687,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_16625,c_25,c_24,c_23,c_1232,c_1252,c_16128]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_18,negated_conjecture,
% 7.45/1.49      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 7.45/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_16926,plain,
% 7.45/1.49      ( k1_xboole_0 != sK2 ),
% 7.45/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_16687,c_18]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17300,plain,
% 7.45/1.49      ( ~ r1_tarski(sK2,k1_xboole_0) | ~ r1_tarski(k1_xboole_0,sK2) ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_16926,c_1]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4408,plain,
% 7.45/1.49      ( m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_0,c_4401]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_4895,plain,
% 7.45/1.49      ( r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_4408,c_963]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_13700,plain,
% 7.45/1.49      ( r1_tarski(k3_xboole_0(X0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_1918,c_4895]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_964,plain,
% 7.45/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.45/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3562,plain,
% 7.45/1.49      ( k1_xboole_0 = X0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(X0,sK0) != iProver_top
% 7.45/1.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 7.45/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_964,c_953]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15203,plain,
% 7.45/1.49      ( k3_xboole_0(X0,sK1) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | v3_pre_topc(k3_xboole_0(X0,sK1),sK0) != iProver_top
% 7.45/1.49      | r1_tarski(k3_xboole_0(X0,sK1),sK1) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_13700,c_3562]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1253,plain,
% 7.45/1.49      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.45/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17,plain,
% 7.45/1.49      ( ~ v2_tops_1(X0,X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.49      | ~ l1_pre_topc(X1)
% 7.45/1.49      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_958,plain,
% 7.45/1.49      ( k1_tops_1(X0,X1) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(X1,X0) != iProver_top
% 7.45/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.45/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3404,plain,
% 7.45/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.45/1.49      | v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_952,c_958]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3431,plain,
% 7.45/1.49      ( ~ v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ l1_pre_topc(sK0)
% 7.45/1.49      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.45/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3404]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17118,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_15203,c_25,c_24,c_27,c_23,c_28,c_1232,c_1252,c_1253,
% 7.45/1.49                 c_3431,c_16128]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3812,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3404,c_27]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3813,plain,
% 7.45/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_3812]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17131,plain,
% 7.45/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_17118,c_3813]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_21,negated_conjecture,
% 7.45/1.49      ( ~ v2_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.45/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_954,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_15,plain,
% 7.45/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.45/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.45/1.49      | ~ r1_tarski(X0,X2)
% 7.45/1.49      | r1_tarski(X0,k1_tops_1(X1,X2))
% 7.45/1.49      | ~ l1_pre_topc(X1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_960,plain,
% 7.45/1.49      ( v3_pre_topc(X0,X1) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.45/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.45/1.49      | r1_tarski(X0,X2) != iProver_top
% 7.45/1.49      | r1_tarski(X0,k1_tops_1(X1,X2)) = iProver_top
% 7.45/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6487,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | v3_pre_topc(sK2,sK0) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,X0) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top
% 7.45/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_954,c_960]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_19,negated_conjecture,
% 7.45/1.49      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 7.45/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_34,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7711,plain,
% 7.45/1.49      ( r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top
% 7.45/1.49      | r1_tarski(sK2,X0) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.45/1.49      | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_6487,c_27,c_34]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7712,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,X0) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_7711]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7724,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 7.45/1.49      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_952,c_7712]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_20,negated_conjecture,
% 7.45/1.49      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 7.45/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_33,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top | r1_tarski(sK2,sK1) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7962,plain,
% 7.45/1.49      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 7.45/1.49      | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_7724,c_33]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7963,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 7.45/1.49      inference(renaming,[status(thm)],[c_7962]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17208,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.45/1.49      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 7.45/1.49      inference(demodulation,[status(thm)],[c_17131,c_7963]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17259,plain,
% 7.45/1.49      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,k1_xboole_0) ),
% 7.45/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_17208]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17639,plain,
% 7.45/1.49      ( ~ r1_tarski(k1_xboole_0,sK2) ),
% 7.45/1.49      inference(global_propositional_subsumption,
% 7.45/1.49                [status(thm)],
% 7.45/1.49                [c_17300,c_25,c_24,c_23,c_1232,c_1252,c_16128,c_17259]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_426,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.45/1.49      theory(equality) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_422,plain,( X0 = X0 ),theory(equality) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_3634,plain,
% 7.45/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_426,c_422]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6944,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ v3_pre_topc(X0,sK0)
% 7.45/1.49      | ~ r1_tarski(X0,X1)
% 7.45/1.49      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 7.45/1.49      | ~ r1_tarski(X0,sK1)
% 7.45/1.49      | r1_tarski(k1_xboole_0,X1) ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_3634,c_3833]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7555,plain,
% 7.45/1.49      ( v2_tops_1(sK1,sK0)
% 7.45/1.49      | ~ v3_pre_topc(sK1,sK0)
% 7.45/1.49      | ~ r1_tarski(sK1,X0)
% 7.45/1.49      | ~ r1_tarski(sK1,sK1)
% 7.45/1.49      | r1_tarski(k1_xboole_0,X0) ),
% 7.45/1.49      inference(resolution,[status(thm)],[c_6944,c_1307]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_6,plain,
% 7.45/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.45/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_966,plain,
% 7.45/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.45/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1838,plain,
% 7.45/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.45/1.49      inference(superposition,[status(thm)],[c_6,c_966]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_1844,plain,
% 7.45/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.45/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1838]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_7558,plain,
% 7.45/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.45/1.49      inference(global_propositional_subsumption,[status(thm)],[c_7555,c_1844]) ).
% 7.45/1.49  
% 7.45/1.49  cnf(c_17644,plain,
% 7.45/1.49      ( $false ),
% 7.45/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_17639,c_7558]) ).
% 7.45/1.49  
% 7.45/1.49  
% 7.45/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.45/1.49  
% 7.45/1.49  ------                               Statistics
% 7.45/1.49  
% 7.45/1.49  ------ Selected
% 7.45/1.49  
% 7.45/1.49  total_time:                             0.544
% 7.45/1.49  
%------------------------------------------------------------------------------
