%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:06 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  153 (1385 expanded)
%              Number of clauses        :   97 ( 361 expanded)
%              Number of leaves         :   13 ( 331 expanded)
%              Depth                    :   23
%              Number of atoms          :  542 (11519 expanded)
%              Number of equality atoms :  192 (2068 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f56,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1586,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_292,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_293,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_20])).

cnf(c_298,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_1585,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2525,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1585])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1593,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1587,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2748,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1593,c_1587])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1803,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1939,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_1940,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1939])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1829,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2219,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_2220,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2219])).

cnf(c_4182,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | v2_tops_1(sK1,sK0) = iProver_top
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2748,c_24,c_1940,c_2220])).

cnf(c_4183,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK1,sK0) = iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4182])).

cnf(c_4192,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_4183])).

cnf(c_12,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_328,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_329,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_1737,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_1738,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1737])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1740,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_1741,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1740])).

cnf(c_8054,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4192,c_24,c_1738,c_1741])).

cnf(c_13,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_314,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_1584,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_2727,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1584])).

cnf(c_8059,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8054,c_2727])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1588,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_343,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_344,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_1582,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_1995,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1582])).

cnf(c_28,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_393,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_344])).

cnf(c_394,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_395,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_3540,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1995,c_28,c_395])).

cnf(c_3550,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_3540])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3700,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3550,c_29])).

cnf(c_3701,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3700])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1597,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3708,plain,
    ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_1597])).

cnf(c_5225,plain,
    ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3708,c_24,c_1738,c_1741,c_4192])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1596,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5228,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5225,c_1596])).

cnf(c_8424,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8059,c_5228])).

cnf(c_1581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_1895,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1581])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1599,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2938,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1599])).

cnf(c_3549,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_3540])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1598,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3673,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3549,c_1598])).

cnf(c_3676,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3673,c_1599])).

cnf(c_5584,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2938,c_24,c_1738,c_1741,c_1895,c_3676,c_4192])).

cnf(c_1583,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_5605,plain,
    ( sK2 != k1_xboole_0
    | v2_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5584,c_1583])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_329])).

cnf(c_626,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_628,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_19])).

cnf(c_6070,plain,
    ( sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5605,c_19,c_24,c_626,c_1738,c_1741,c_2727,c_4192])).

cnf(c_2149,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1598,c_1597])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1595,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3157,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_1595])).

cnf(c_4141,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_3157])).

cnf(c_4534,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4141,c_24,c_1738,c_1741,c_4192])).

cnf(c_4540,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4534,c_1599])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8424,c_6070,c_4540])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.65/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.99  
% 2.65/0.99  ------  iProver source info
% 2.65/0.99  
% 2.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.99  git: non_committed_changes: false
% 2.65/0.99  git: last_make_outside_of_git: false
% 2.65/0.99  
% 2.65/0.99  ------ 
% 2.65/0.99  
% 2.65/0.99  ------ Input Options
% 2.65/0.99  
% 2.65/0.99  --out_options                           all
% 2.65/0.99  --tptp_safe_out                         true
% 2.65/0.99  --problem_path                          ""
% 2.65/0.99  --include_path                          ""
% 2.65/0.99  --clausifier                            res/vclausify_rel
% 2.65/0.99  --clausifier_options                    --mode clausify
% 2.65/0.99  --stdin                                 false
% 2.65/0.99  --stats_out                             all
% 2.65/0.99  
% 2.65/0.99  ------ General Options
% 2.65/0.99  
% 2.65/0.99  --fof                                   false
% 2.65/0.99  --time_out_real                         305.
% 2.65/0.99  --time_out_virtual                      -1.
% 2.65/0.99  --symbol_type_check                     false
% 2.65/0.99  --clausify_out                          false
% 2.65/0.99  --sig_cnt_out                           false
% 2.65/0.99  --trig_cnt_out                          false
% 2.65/0.99  --trig_cnt_out_tolerance                1.
% 2.65/0.99  --trig_cnt_out_sk_spl                   false
% 2.65/0.99  --abstr_cl_out                          false
% 2.65/0.99  
% 2.65/0.99  ------ Global Options
% 2.65/0.99  
% 2.65/0.99  --schedule                              default
% 2.65/0.99  --add_important_lit                     false
% 2.65/0.99  --prop_solver_per_cl                    1000
% 2.65/0.99  --min_unsat_core                        false
% 2.65/0.99  --soft_assumptions                      false
% 2.65/0.99  --soft_lemma_size                       3
% 2.65/0.99  --prop_impl_unit_size                   0
% 2.65/0.99  --prop_impl_unit                        []
% 2.65/0.99  --share_sel_clauses                     true
% 2.65/0.99  --reset_solvers                         false
% 2.65/0.99  --bc_imp_inh                            [conj_cone]
% 2.65/0.99  --conj_cone_tolerance                   3.
% 2.65/0.99  --extra_neg_conj                        none
% 2.65/0.99  --large_theory_mode                     true
% 2.65/0.99  --prolific_symb_bound                   200
% 2.65/0.99  --lt_threshold                          2000
% 2.65/0.99  --clause_weak_htbl                      true
% 2.65/0.99  --gc_record_bc_elim                     false
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing Options
% 2.65/0.99  
% 2.65/0.99  --preprocessing_flag                    true
% 2.65/0.99  --time_out_prep_mult                    0.1
% 2.65/0.99  --splitting_mode                        input
% 2.65/0.99  --splitting_grd                         true
% 2.65/0.99  --splitting_cvd                         false
% 2.65/0.99  --splitting_cvd_svl                     false
% 2.65/0.99  --splitting_nvd                         32
% 2.65/0.99  --sub_typing                            true
% 2.65/0.99  --prep_gs_sim                           true
% 2.65/0.99  --prep_unflatten                        true
% 2.65/0.99  --prep_res_sim                          true
% 2.65/0.99  --prep_upred                            true
% 2.65/0.99  --prep_sem_filter                       exhaustive
% 2.65/0.99  --prep_sem_filter_out                   false
% 2.65/0.99  --pred_elim                             true
% 2.65/0.99  --res_sim_input                         true
% 2.65/0.99  --eq_ax_congr_red                       true
% 2.65/0.99  --pure_diseq_elim                       true
% 2.65/0.99  --brand_transform                       false
% 2.65/0.99  --non_eq_to_eq                          false
% 2.65/0.99  --prep_def_merge                        true
% 2.65/0.99  --prep_def_merge_prop_impl              false
% 2.65/0.99  --prep_def_merge_mbd                    true
% 2.65/0.99  --prep_def_merge_tr_red                 false
% 2.65/0.99  --prep_def_merge_tr_cl                  false
% 2.65/0.99  --smt_preprocessing                     true
% 2.65/0.99  --smt_ac_axioms                         fast
% 2.65/0.99  --preprocessed_out                      false
% 2.65/0.99  --preprocessed_stats                    false
% 2.65/0.99  
% 2.65/0.99  ------ Abstraction refinement Options
% 2.65/0.99  
% 2.65/0.99  --abstr_ref                             []
% 2.65/0.99  --abstr_ref_prep                        false
% 2.65/0.99  --abstr_ref_until_sat                   false
% 2.65/0.99  --abstr_ref_sig_restrict                funpre
% 2.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.99  --abstr_ref_under                       []
% 2.65/0.99  
% 2.65/0.99  ------ SAT Options
% 2.65/0.99  
% 2.65/0.99  --sat_mode                              false
% 2.65/0.99  --sat_fm_restart_options                ""
% 2.65/0.99  --sat_gr_def                            false
% 2.65/0.99  --sat_epr_types                         true
% 2.65/0.99  --sat_non_cyclic_types                  false
% 2.65/0.99  --sat_finite_models                     false
% 2.65/0.99  --sat_fm_lemmas                         false
% 2.65/0.99  --sat_fm_prep                           false
% 2.65/0.99  --sat_fm_uc_incr                        true
% 2.65/0.99  --sat_out_model                         small
% 2.65/0.99  --sat_out_clauses                       false
% 2.65/0.99  
% 2.65/0.99  ------ QBF Options
% 2.65/0.99  
% 2.65/0.99  --qbf_mode                              false
% 2.65/0.99  --qbf_elim_univ                         false
% 2.65/0.99  --qbf_dom_inst                          none
% 2.65/0.99  --qbf_dom_pre_inst                      false
% 2.65/0.99  --qbf_sk_in                             false
% 2.65/0.99  --qbf_pred_elim                         true
% 2.65/0.99  --qbf_split                             512
% 2.65/0.99  
% 2.65/0.99  ------ BMC1 Options
% 2.65/0.99  
% 2.65/0.99  --bmc1_incremental                      false
% 2.65/0.99  --bmc1_axioms                           reachable_all
% 2.65/0.99  --bmc1_min_bound                        0
% 2.65/0.99  --bmc1_max_bound                        -1
% 2.65/0.99  --bmc1_max_bound_default                -1
% 2.65/0.99  --bmc1_symbol_reachability              true
% 2.65/0.99  --bmc1_property_lemmas                  false
% 2.65/0.99  --bmc1_k_induction                      false
% 2.65/0.99  --bmc1_non_equiv_states                 false
% 2.65/0.99  --bmc1_deadlock                         false
% 2.65/0.99  --bmc1_ucm                              false
% 2.65/0.99  --bmc1_add_unsat_core                   none
% 2.65/0.99  --bmc1_unsat_core_children              false
% 2.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.99  --bmc1_out_stat                         full
% 2.65/0.99  --bmc1_ground_init                      false
% 2.65/0.99  --bmc1_pre_inst_next_state              false
% 2.65/0.99  --bmc1_pre_inst_state                   false
% 2.65/0.99  --bmc1_pre_inst_reach_state             false
% 2.65/0.99  --bmc1_out_unsat_core                   false
% 2.65/0.99  --bmc1_aig_witness_out                  false
% 2.65/0.99  --bmc1_verbose                          false
% 2.65/0.99  --bmc1_dump_clauses_tptp                false
% 2.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.99  --bmc1_dump_file                        -
% 2.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.99  --bmc1_ucm_extend_mode                  1
% 2.65/0.99  --bmc1_ucm_init_mode                    2
% 2.65/0.99  --bmc1_ucm_cone_mode                    none
% 2.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.99  --bmc1_ucm_relax_model                  4
% 2.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.99  --bmc1_ucm_layered_model                none
% 2.65/0.99  --bmc1_ucm_max_lemma_size               10
% 2.65/0.99  
% 2.65/0.99  ------ AIG Options
% 2.65/0.99  
% 2.65/0.99  --aig_mode                              false
% 2.65/0.99  
% 2.65/0.99  ------ Instantiation Options
% 2.65/0.99  
% 2.65/0.99  --instantiation_flag                    true
% 2.65/0.99  --inst_sos_flag                         false
% 2.65/0.99  --inst_sos_phase                        true
% 2.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.99  --inst_lit_sel_side                     num_symb
% 2.65/0.99  --inst_solver_per_active                1400
% 2.65/0.99  --inst_solver_calls_frac                1.
% 2.65/0.99  --inst_passive_queue_type               priority_queues
% 2.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.99  --inst_passive_queues_freq              [25;2]
% 2.65/0.99  --inst_dismatching                      true
% 2.65/0.99  --inst_eager_unprocessed_to_passive     true
% 2.65/0.99  --inst_prop_sim_given                   true
% 2.65/0.99  --inst_prop_sim_new                     false
% 2.65/0.99  --inst_subs_new                         false
% 2.65/0.99  --inst_eq_res_simp                      false
% 2.65/0.99  --inst_subs_given                       false
% 2.65/0.99  --inst_orphan_elimination               true
% 2.65/0.99  --inst_learning_loop_flag               true
% 2.65/0.99  --inst_learning_start                   3000
% 2.65/0.99  --inst_learning_factor                  2
% 2.65/0.99  --inst_start_prop_sim_after_learn       3
% 2.65/0.99  --inst_sel_renew                        solver
% 2.65/0.99  --inst_lit_activity_flag                true
% 2.65/0.99  --inst_restr_to_given                   false
% 2.65/0.99  --inst_activity_threshold               500
% 2.65/0.99  --inst_out_proof                        true
% 2.65/0.99  
% 2.65/0.99  ------ Resolution Options
% 2.65/0.99  
% 2.65/0.99  --resolution_flag                       true
% 2.65/0.99  --res_lit_sel                           adaptive
% 2.65/0.99  --res_lit_sel_side                      none
% 2.65/0.99  --res_ordering                          kbo
% 2.65/0.99  --res_to_prop_solver                    active
% 2.65/0.99  --res_prop_simpl_new                    false
% 2.65/0.99  --res_prop_simpl_given                  true
% 2.65/0.99  --res_passive_queue_type                priority_queues
% 2.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.99  --res_passive_queues_freq               [15;5]
% 2.65/0.99  --res_forward_subs                      full
% 2.65/0.99  --res_backward_subs                     full
% 2.65/0.99  --res_forward_subs_resolution           true
% 2.65/0.99  --res_backward_subs_resolution          true
% 2.65/0.99  --res_orphan_elimination                true
% 2.65/0.99  --res_time_limit                        2.
% 2.65/0.99  --res_out_proof                         true
% 2.65/0.99  
% 2.65/0.99  ------ Superposition Options
% 2.65/0.99  
% 2.65/0.99  --superposition_flag                    true
% 2.65/0.99  --sup_passive_queue_type                priority_queues
% 2.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.99  --demod_completeness_check              fast
% 2.65/0.99  --demod_use_ground                      true
% 2.65/0.99  --sup_to_prop_solver                    passive
% 2.65/0.99  --sup_prop_simpl_new                    true
% 2.65/0.99  --sup_prop_simpl_given                  true
% 2.65/0.99  --sup_fun_splitting                     false
% 2.65/0.99  --sup_smt_interval                      50000
% 2.65/0.99  
% 2.65/0.99  ------ Superposition Simplification Setup
% 2.65/0.99  
% 2.65/0.99  --sup_indices_passive                   []
% 2.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_full_bw                           [BwDemod]
% 2.65/0.99  --sup_immed_triv                        [TrivRules]
% 2.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_immed_bw_main                     []
% 2.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.99  
% 2.65/0.99  ------ Combination Options
% 2.65/0.99  
% 2.65/0.99  --comb_res_mult                         3
% 2.65/0.99  --comb_sup_mult                         2
% 2.65/0.99  --comb_inst_mult                        10
% 2.65/0.99  
% 2.65/0.99  ------ Debug Options
% 2.65/0.99  
% 2.65/0.99  --dbg_backtrace                         false
% 2.65/0.99  --dbg_dump_prop_clauses                 false
% 2.65/0.99  --dbg_dump_prop_clauses_file            -
% 2.65/0.99  --dbg_out_stat                          false
% 2.65/0.99  ------ Parsing...
% 2.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.99  ------ Proving...
% 2.65/0.99  ------ Problem Properties 
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  clauses                                 19
% 2.65/0.99  conjectures                             6
% 2.65/0.99  EPR                                     6
% 2.65/0.99  Horn                                    18
% 2.65/0.99  unary                                   2
% 2.65/0.99  binary                                  11
% 2.65/0.99  lits                                    46
% 2.65/0.99  lits eq                                 7
% 2.65/0.99  fd_pure                                 0
% 2.65/0.99  fd_pseudo                               0
% 2.65/0.99  fd_cond                                 1
% 2.65/0.99  fd_pseudo_cond                          1
% 2.65/0.99  AC symbols                              0
% 2.65/0.99  
% 2.65/0.99  ------ Schedule dynamic 5 is on 
% 2.65/0.99  
% 2.65/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  ------ 
% 2.65/0.99  Current options:
% 2.65/0.99  ------ 
% 2.65/0.99  
% 2.65/0.99  ------ Input Options
% 2.65/0.99  
% 2.65/0.99  --out_options                           all
% 2.65/0.99  --tptp_safe_out                         true
% 2.65/0.99  --problem_path                          ""
% 2.65/0.99  --include_path                          ""
% 2.65/0.99  --clausifier                            res/vclausify_rel
% 2.65/0.99  --clausifier_options                    --mode clausify
% 2.65/0.99  --stdin                                 false
% 2.65/0.99  --stats_out                             all
% 2.65/0.99  
% 2.65/0.99  ------ General Options
% 2.65/0.99  
% 2.65/0.99  --fof                                   false
% 2.65/0.99  --time_out_real                         305.
% 2.65/0.99  --time_out_virtual                      -1.
% 2.65/0.99  --symbol_type_check                     false
% 2.65/0.99  --clausify_out                          false
% 2.65/0.99  --sig_cnt_out                           false
% 2.65/0.99  --trig_cnt_out                          false
% 2.65/0.99  --trig_cnt_out_tolerance                1.
% 2.65/0.99  --trig_cnt_out_sk_spl                   false
% 2.65/0.99  --abstr_cl_out                          false
% 2.65/0.99  
% 2.65/0.99  ------ Global Options
% 2.65/0.99  
% 2.65/0.99  --schedule                              default
% 2.65/0.99  --add_important_lit                     false
% 2.65/0.99  --prop_solver_per_cl                    1000
% 2.65/0.99  --min_unsat_core                        false
% 2.65/0.99  --soft_assumptions                      false
% 2.65/0.99  --soft_lemma_size                       3
% 2.65/0.99  --prop_impl_unit_size                   0
% 2.65/0.99  --prop_impl_unit                        []
% 2.65/0.99  --share_sel_clauses                     true
% 2.65/0.99  --reset_solvers                         false
% 2.65/0.99  --bc_imp_inh                            [conj_cone]
% 2.65/0.99  --conj_cone_tolerance                   3.
% 2.65/0.99  --extra_neg_conj                        none
% 2.65/0.99  --large_theory_mode                     true
% 2.65/0.99  --prolific_symb_bound                   200
% 2.65/0.99  --lt_threshold                          2000
% 2.65/0.99  --clause_weak_htbl                      true
% 2.65/0.99  --gc_record_bc_elim                     false
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing Options
% 2.65/0.99  
% 2.65/0.99  --preprocessing_flag                    true
% 2.65/0.99  --time_out_prep_mult                    0.1
% 2.65/0.99  --splitting_mode                        input
% 2.65/0.99  --splitting_grd                         true
% 2.65/0.99  --splitting_cvd                         false
% 2.65/0.99  --splitting_cvd_svl                     false
% 2.65/0.99  --splitting_nvd                         32
% 2.65/0.99  --sub_typing                            true
% 2.65/0.99  --prep_gs_sim                           true
% 2.65/0.99  --prep_unflatten                        true
% 2.65/0.99  --prep_res_sim                          true
% 2.65/0.99  --prep_upred                            true
% 2.65/0.99  --prep_sem_filter                       exhaustive
% 2.65/0.99  --prep_sem_filter_out                   false
% 2.65/0.99  --pred_elim                             true
% 2.65/0.99  --res_sim_input                         true
% 2.65/0.99  --eq_ax_congr_red                       true
% 2.65/0.99  --pure_diseq_elim                       true
% 2.65/0.99  --brand_transform                       false
% 2.65/0.99  --non_eq_to_eq                          false
% 2.65/0.99  --prep_def_merge                        true
% 2.65/0.99  --prep_def_merge_prop_impl              false
% 2.65/0.99  --prep_def_merge_mbd                    true
% 2.65/0.99  --prep_def_merge_tr_red                 false
% 2.65/0.99  --prep_def_merge_tr_cl                  false
% 2.65/0.99  --smt_preprocessing                     true
% 2.65/0.99  --smt_ac_axioms                         fast
% 2.65/0.99  --preprocessed_out                      false
% 2.65/0.99  --preprocessed_stats                    false
% 2.65/0.99  
% 2.65/0.99  ------ Abstraction refinement Options
% 2.65/0.99  
% 2.65/0.99  --abstr_ref                             []
% 2.65/0.99  --abstr_ref_prep                        false
% 2.65/0.99  --abstr_ref_until_sat                   false
% 2.65/0.99  --abstr_ref_sig_restrict                funpre
% 2.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.99  --abstr_ref_under                       []
% 2.65/0.99  
% 2.65/0.99  ------ SAT Options
% 2.65/0.99  
% 2.65/0.99  --sat_mode                              false
% 2.65/0.99  --sat_fm_restart_options                ""
% 2.65/0.99  --sat_gr_def                            false
% 2.65/0.99  --sat_epr_types                         true
% 2.65/0.99  --sat_non_cyclic_types                  false
% 2.65/0.99  --sat_finite_models                     false
% 2.65/0.99  --sat_fm_lemmas                         false
% 2.65/0.99  --sat_fm_prep                           false
% 2.65/0.99  --sat_fm_uc_incr                        true
% 2.65/0.99  --sat_out_model                         small
% 2.65/0.99  --sat_out_clauses                       false
% 2.65/0.99  
% 2.65/0.99  ------ QBF Options
% 2.65/0.99  
% 2.65/0.99  --qbf_mode                              false
% 2.65/0.99  --qbf_elim_univ                         false
% 2.65/0.99  --qbf_dom_inst                          none
% 2.65/0.99  --qbf_dom_pre_inst                      false
% 2.65/0.99  --qbf_sk_in                             false
% 2.65/0.99  --qbf_pred_elim                         true
% 2.65/0.99  --qbf_split                             512
% 2.65/0.99  
% 2.65/0.99  ------ BMC1 Options
% 2.65/0.99  
% 2.65/0.99  --bmc1_incremental                      false
% 2.65/0.99  --bmc1_axioms                           reachable_all
% 2.65/0.99  --bmc1_min_bound                        0
% 2.65/0.99  --bmc1_max_bound                        -1
% 2.65/0.99  --bmc1_max_bound_default                -1
% 2.65/0.99  --bmc1_symbol_reachability              true
% 2.65/0.99  --bmc1_property_lemmas                  false
% 2.65/0.99  --bmc1_k_induction                      false
% 2.65/0.99  --bmc1_non_equiv_states                 false
% 2.65/0.99  --bmc1_deadlock                         false
% 2.65/0.99  --bmc1_ucm                              false
% 2.65/0.99  --bmc1_add_unsat_core                   none
% 2.65/0.99  --bmc1_unsat_core_children              false
% 2.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.99  --bmc1_out_stat                         full
% 2.65/0.99  --bmc1_ground_init                      false
% 2.65/0.99  --bmc1_pre_inst_next_state              false
% 2.65/0.99  --bmc1_pre_inst_state                   false
% 2.65/0.99  --bmc1_pre_inst_reach_state             false
% 2.65/0.99  --bmc1_out_unsat_core                   false
% 2.65/0.99  --bmc1_aig_witness_out                  false
% 2.65/0.99  --bmc1_verbose                          false
% 2.65/0.99  --bmc1_dump_clauses_tptp                false
% 2.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.99  --bmc1_dump_file                        -
% 2.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.99  --bmc1_ucm_extend_mode                  1
% 2.65/0.99  --bmc1_ucm_init_mode                    2
% 2.65/0.99  --bmc1_ucm_cone_mode                    none
% 2.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.99  --bmc1_ucm_relax_model                  4
% 2.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.99  --bmc1_ucm_layered_model                none
% 2.65/0.99  --bmc1_ucm_max_lemma_size               10
% 2.65/0.99  
% 2.65/0.99  ------ AIG Options
% 2.65/0.99  
% 2.65/0.99  --aig_mode                              false
% 2.65/0.99  
% 2.65/0.99  ------ Instantiation Options
% 2.65/0.99  
% 2.65/0.99  --instantiation_flag                    true
% 2.65/0.99  --inst_sos_flag                         false
% 2.65/0.99  --inst_sos_phase                        true
% 2.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.99  --inst_lit_sel_side                     none
% 2.65/0.99  --inst_solver_per_active                1400
% 2.65/0.99  --inst_solver_calls_frac                1.
% 2.65/0.99  --inst_passive_queue_type               priority_queues
% 2.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.99  --inst_passive_queues_freq              [25;2]
% 2.65/0.99  --inst_dismatching                      true
% 2.65/0.99  --inst_eager_unprocessed_to_passive     true
% 2.65/0.99  --inst_prop_sim_given                   true
% 2.65/0.99  --inst_prop_sim_new                     false
% 2.65/0.99  --inst_subs_new                         false
% 2.65/0.99  --inst_eq_res_simp                      false
% 2.65/0.99  --inst_subs_given                       false
% 2.65/0.99  --inst_orphan_elimination               true
% 2.65/0.99  --inst_learning_loop_flag               true
% 2.65/0.99  --inst_learning_start                   3000
% 2.65/0.99  --inst_learning_factor                  2
% 2.65/0.99  --inst_start_prop_sim_after_learn       3
% 2.65/0.99  --inst_sel_renew                        solver
% 2.65/0.99  --inst_lit_activity_flag                true
% 2.65/0.99  --inst_restr_to_given                   false
% 2.65/0.99  --inst_activity_threshold               500
% 2.65/0.99  --inst_out_proof                        true
% 2.65/0.99  
% 2.65/0.99  ------ Resolution Options
% 2.65/0.99  
% 2.65/0.99  --resolution_flag                       false
% 2.65/0.99  --res_lit_sel                           adaptive
% 2.65/0.99  --res_lit_sel_side                      none
% 2.65/0.99  --res_ordering                          kbo
% 2.65/0.99  --res_to_prop_solver                    active
% 2.65/0.99  --res_prop_simpl_new                    false
% 2.65/0.99  --res_prop_simpl_given                  true
% 2.65/0.99  --res_passive_queue_type                priority_queues
% 2.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.99  --res_passive_queues_freq               [15;5]
% 2.65/0.99  --res_forward_subs                      full
% 2.65/0.99  --res_backward_subs                     full
% 2.65/0.99  --res_forward_subs_resolution           true
% 2.65/0.99  --res_backward_subs_resolution          true
% 2.65/0.99  --res_orphan_elimination                true
% 2.65/0.99  --res_time_limit                        2.
% 2.65/0.99  --res_out_proof                         true
% 2.65/0.99  
% 2.65/0.99  ------ Superposition Options
% 2.65/0.99  
% 2.65/0.99  --superposition_flag                    true
% 2.65/0.99  --sup_passive_queue_type                priority_queues
% 2.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.99  --demod_completeness_check              fast
% 2.65/0.99  --demod_use_ground                      true
% 2.65/0.99  --sup_to_prop_solver                    passive
% 2.65/0.99  --sup_prop_simpl_new                    true
% 2.65/0.99  --sup_prop_simpl_given                  true
% 2.65/0.99  --sup_fun_splitting                     false
% 2.65/0.99  --sup_smt_interval                      50000
% 2.65/0.99  
% 2.65/0.99  ------ Superposition Simplification Setup
% 2.65/0.99  
% 2.65/0.99  --sup_indices_passive                   []
% 2.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_full_bw                           [BwDemod]
% 2.65/0.99  --sup_immed_triv                        [TrivRules]
% 2.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_immed_bw_main                     []
% 2.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.99  
% 2.65/0.99  ------ Combination Options
% 2.65/0.99  
% 2.65/0.99  --comb_res_mult                         3
% 2.65/0.99  --comb_sup_mult                         2
% 2.65/0.99  --comb_inst_mult                        10
% 2.65/0.99  
% 2.65/0.99  ------ Debug Options
% 2.65/0.99  
% 2.65/0.99  --dbg_backtrace                         false
% 2.65/0.99  --dbg_dump_prop_clauses                 false
% 2.65/0.99  --dbg_dump_prop_clauses_file            -
% 2.65/0.99  --dbg_out_stat                          false
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  ------ Proving...
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  % SZS status Theorem for theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  fof(f10,conjecture,(
% 2.65/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f11,negated_conjecture,(
% 2.65/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.65/0.99    inference(negated_conjecture,[],[f10])).
% 2.65/0.99  
% 2.65/0.99  fof(f21,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.65/0.99    inference(ennf_transformation,[],[f11])).
% 2.65/0.99  
% 2.65/0.99  fof(f22,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.65/0.99    inference(flattening,[],[f21])).
% 2.65/0.99  
% 2.65/0.99  fof(f28,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.65/0.99    inference(nnf_transformation,[],[f22])).
% 2.65/0.99  
% 2.65/0.99  fof(f29,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.65/0.99    inference(flattening,[],[f28])).
% 2.65/0.99  
% 2.65/0.99  fof(f30,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.65/0.99    inference(rectify,[],[f29])).
% 2.65/0.99  
% 2.65/0.99  fof(f33,plain,(
% 2.65/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.65/0.99    introduced(choice_axiom,[])).
% 2.65/0.99  
% 2.65/0.99  fof(f32,plain,(
% 2.65/0.99    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.65/0.99    introduced(choice_axiom,[])).
% 2.65/0.99  
% 2.65/0.99  fof(f31,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.65/0.99    introduced(choice_axiom,[])).
% 2.65/0.99  
% 2.65/0.99  fof(f34,plain,(
% 2.65/0.99    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 2.65/0.99  
% 2.65/0.99  fof(f51,plain,(
% 2.65/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f6,axiom,(
% 2.65/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f15,plain,(
% 2.65/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.65/0.99    inference(ennf_transformation,[],[f6])).
% 2.65/0.99  
% 2.65/0.99  fof(f16,plain,(
% 2.65/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.65/0.99    inference(flattening,[],[f15])).
% 2.65/0.99  
% 2.65/0.99  fof(f44,plain,(
% 2.65/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f16])).
% 2.65/0.99  
% 2.65/0.99  fof(f49,plain,(
% 2.65/0.99    v2_pre_topc(sK0)),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f50,plain,(
% 2.65/0.99    l1_pre_topc(sK0)),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f5,axiom,(
% 2.65/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f26,plain,(
% 2.65/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.65/0.99    inference(nnf_transformation,[],[f5])).
% 2.65/0.99  
% 2.65/0.99  fof(f43,plain,(
% 2.65/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f26])).
% 2.65/0.99  
% 2.65/0.99  fof(f52,plain,(
% 2.65/0.99    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f42,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.65/0.99    inference(cnf_transformation,[],[f26])).
% 2.65/0.99  
% 2.65/0.99  fof(f4,axiom,(
% 2.65/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f13,plain,(
% 2.65/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.65/0.99    inference(ennf_transformation,[],[f4])).
% 2.65/0.99  
% 2.65/0.99  fof(f14,plain,(
% 2.65/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.65/0.99    inference(flattening,[],[f13])).
% 2.65/0.99  
% 2.65/0.99  fof(f41,plain,(
% 2.65/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f14])).
% 2.65/0.99  
% 2.65/0.99  fof(f9,axiom,(
% 2.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f20,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f9])).
% 2.65/0.99  
% 2.65/0.99  fof(f27,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/0.99    inference(nnf_transformation,[],[f20])).
% 2.65/0.99  
% 2.65/0.99  fof(f48,plain,(
% 2.65/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f27])).
% 2.65/0.99  
% 2.65/0.99  fof(f7,axiom,(
% 2.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f17,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f7])).
% 2.65/0.99  
% 2.65/0.99  fof(f45,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f17])).
% 2.65/0.99  
% 2.65/0.99  fof(f47,plain,(
% 2.65/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f27])).
% 2.65/0.99  
% 2.65/0.99  fof(f53,plain,(
% 2.65/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f8,axiom,(
% 2.65/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f18,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f8])).
% 2.65/0.99  
% 2.65/0.99  fof(f19,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.65/0.99    inference(flattening,[],[f18])).
% 2.65/0.99  
% 2.65/0.99  fof(f46,plain,(
% 2.65/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f19])).
% 2.65/0.99  
% 2.65/0.99  fof(f55,plain,(
% 2.65/0.99    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f54,plain,(
% 2.65/0.99    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f2,axiom,(
% 2.65/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f25,plain,(
% 2.65/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.65/0.99    inference(nnf_transformation,[],[f2])).
% 2.65/0.99  
% 2.65/0.99  fof(f39,plain,(
% 2.65/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f25])).
% 2.65/0.99  
% 2.65/0.99  fof(f38,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.65/0.99    inference(cnf_transformation,[],[f25])).
% 2.65/0.99  
% 2.65/0.99  fof(f1,axiom,(
% 2.65/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f23,plain,(
% 2.65/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.99    inference(nnf_transformation,[],[f1])).
% 2.65/0.99  
% 2.65/0.99  fof(f24,plain,(
% 2.65/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.99    inference(flattening,[],[f23])).
% 2.65/0.99  
% 2.65/0.99  fof(f37,plain,(
% 2.65/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f24])).
% 2.65/0.99  
% 2.65/0.99  fof(f36,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.65/0.99    inference(cnf_transformation,[],[f24])).
% 2.65/0.99  
% 2.65/0.99  fof(f57,plain,(
% 2.65/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.65/0.99    inference(equality_resolution,[],[f36])).
% 2.65/0.99  
% 2.65/0.99  fof(f56,plain,(
% 2.65/0.99    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.65/0.99    inference(cnf_transformation,[],[f34])).
% 2.65/0.99  
% 2.65/0.99  fof(f3,axiom,(
% 2.65/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 2.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f12,plain,(
% 2.65/0.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.65/0.99    inference(ennf_transformation,[],[f3])).
% 2.65/0.99  
% 2.65/0.99  fof(f40,plain,(
% 2.65/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f12])).
% 2.65/0.99  
% 2.65/0.99  cnf(c_19,negated_conjecture,
% 2.65/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1586,plain,
% 2.65/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_9,plain,
% 2.65/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.65/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.65/0.99      | ~ v2_pre_topc(X0)
% 2.65/0.99      | ~ l1_pre_topc(X0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_21,negated_conjecture,
% 2.65/0.99      ( v2_pre_topc(sK0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_292,plain,
% 2.65/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.65/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.65/0.99      | ~ l1_pre_topc(X0)
% 2.65/0.99      | sK0 != X0 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_293,plain,
% 2.65/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ l1_pre_topc(sK0) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_292]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_20,negated_conjecture,
% 2.65/0.99      ( l1_pre_topc(sK0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_297,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_293,c_20]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_298,plain,
% 2.65/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.99      inference(renaming,[status(thm)],[c_297]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1585,plain,
% 2.65/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2525,plain,
% 2.65/0.99      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1586,c_1585]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_7,plain,
% 2.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1593,plain,
% 2.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.65/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_18,negated_conjecture,
% 2.65/0.99      ( v2_tops_1(sK1,sK0)
% 2.65/0.99      | ~ v3_pre_topc(X0,sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ r1_tarski(X0,sK1)
% 2.65/0.99      | k1_xboole_0 = X0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1587,plain,
% 2.65/0.99      ( k1_xboole_0 = X0
% 2.65/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 2.65/0.99      | v3_pre_topc(X0,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2748,plain,
% 2.65/0.99      ( k1_xboole_0 = X0
% 2.65/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 2.65/0.99      | v3_pre_topc(X0,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 2.65/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1593,c_1587]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_24,plain,
% 2.65/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_8,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1803,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1939,plain,
% 2.65/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1803]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1940,plain,
% 2.65/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_1939]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_6,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.65/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1829,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1)
% 2.65/0.99      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 2.65/0.99      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2219,plain,
% 2.65/0.99      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.65/0.99      | ~ r1_tarski(X0,sK1)
% 2.65/0.99      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1829]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2220,plain,
% 2.65/0.99      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 2.65/0.99      | r1_tarski(X0,sK1) != iProver_top
% 2.65/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_2219]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4182,plain,
% 2.65/0.99      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.65/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 2.65/0.99      | k1_xboole_0 = X0
% 2.65/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_2748,c_24,c_1940,c_2220]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4183,plain,
% 2.65/0.99      ( k1_xboole_0 = X0
% 2.65/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 2.65/0.99      | v3_pre_topc(X0,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 2.65/0.99      inference(renaming,[status(thm)],[c_4182]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4192,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.65/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_2525,c_4183]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_12,plain,
% 2.65/0.99      ( v2_tops_1(X0,X1)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | ~ l1_pre_topc(X1)
% 2.65/0.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_328,plain,
% 2.65/0.99      ( v2_tops_1(X0,X1)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.65/0.99      | sK0 != X1 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_329,plain,
% 2.65/0.99      ( v2_tops_1(X0,sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_328]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1737,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0)
% 2.65/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_329]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1738,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.65/0.99      | v2_tops_1(sK1,sK0) = iProver_top
% 2.65/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_1737]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_10,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.65/0.99      | ~ l1_pre_topc(X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_364,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.65/0.99      | sK0 != X1 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_365,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1740,plain,
% 2.65/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_365]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1741,plain,
% 2.65/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_1740]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_8054,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_4192,c_24,c_1738,c_1741]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_13,plain,
% 2.65/0.99      ( ~ v2_tops_1(X0,X1)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | ~ l1_pre_topc(X1)
% 2.65/0.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_313,plain,
% 2.65/0.99      ( ~ v2_tops_1(X0,X1)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.65/0.99      | sK0 != X1 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_314,plain,
% 2.65/0.99      ( ~ v2_tops_1(X0,sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_313]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1584,plain,
% 2.65/0.99      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.65/0.99      | v2_tops_1(X0,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2727,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.65/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1586,c_1584]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_8059,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_8054,c_2727]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_17,negated_conjecture,
% 2.65/0.99      ( ~ v2_tops_1(sK1,sK0)
% 2.65/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.65/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1588,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_11,plain,
% 2.65/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | ~ r1_tarski(X0,X2)
% 2.65/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.65/0.99      | ~ l1_pre_topc(X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_343,plain,
% 2.65/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.65/0.99      | ~ r1_tarski(X0,X2)
% 2.65/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.65/0.99      | sK0 != X1 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_344,plain,
% 2.65/0.99      ( ~ v3_pre_topc(X0,sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ r1_tarski(X0,X1)
% 2.65/0.99      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1582,plain,
% 2.65/0.99      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.65/0.99      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1995,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,X0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1588,c_1582]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_28,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_15,negated_conjecture,
% 2.65/0.99      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_393,plain,
% 2.65/0.99      ( ~ v2_tops_1(sK1,sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ r1_tarski(X0,X1)
% 2.65/0.99      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.65/0.99      | sK0 != sK0
% 2.65/0.99      | sK2 != X0 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_344]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_394,plain,
% 2.65/0.99      ( ~ v2_tops_1(sK1,sK0)
% 2.65/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | ~ r1_tarski(sK2,X0)
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_395,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,X0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3540,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,X0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_1995,c_28,c_395]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3550,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.65/0.99      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1586,c_3540]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_16,negated_conjecture,
% 2.65/0.99      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_29,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3700,plain,
% 2.65/0.99      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.65/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_3550,c_29]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3701,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.65/0.99      inference(renaming,[status(thm)],[c_3700]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1597,plain,
% 2.65/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.65/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3708,plain,
% 2.65/0.99      ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0
% 2.65/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_3701,c_1597]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_5225,plain,
% 2.65/0.99      ( k4_xboole_0(sK2,k1_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_3708,c_24,c_1738,c_1741,c_4192]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4,plain,
% 2.65/0.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1596,plain,
% 2.65/0.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.65/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_5228,plain,
% 2.65/0.99      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_5225,c_1596]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_8424,plain,
% 2.65/0.99      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.65/0.99      inference(demodulation,[status(thm)],[c_8059,c_5228]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1581,plain,
% 2.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1895,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1588,c_1581]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_0,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.65/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1599,plain,
% 2.65/0.99      ( X0 = X1
% 2.65/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.65/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2938,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK2) = sK2
% 2.65/0.99      | v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1895,c_1599]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3549,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top
% 2.65/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1588,c_3540]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1,plain,
% 2.65/0.99      ( r1_tarski(X0,X0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1598,plain,
% 2.65/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3673,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) = iProver_top ),
% 2.65/0.99      inference(forward_subsumption_resolution,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_3549,c_1598]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3676,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK2) = sK2
% 2.65/0.99      | v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_3673,c_1599]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_5584,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_2938,c_24,c_1738,c_1741,c_1895,c_3676,c_4192]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1583,plain,
% 2.65/0.99      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 2.65/0.99      | v2_tops_1(X0,sK0) = iProver_top
% 2.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_5605,plain,
% 2.65/0.99      ( sK2 != k1_xboole_0
% 2.65/0.99      | v2_tops_1(sK2,sK0) = iProver_top
% 2.65/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_5584,c_1583]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_14,negated_conjecture,
% 2.65/0.99      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.65/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_625,plain,
% 2.65/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.65/0.99      | sK0 != sK0
% 2.65/0.99      | sK1 != X0
% 2.65/0.99      | sK2 != k1_xboole_0 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_329]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_626,plain,
% 2.65/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.65/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.65/0.99      | sK2 != k1_xboole_0 ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_625]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_628,plain,
% 2.65/0.99      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_626,c_19]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_6070,plain,
% 2.65/0.99      ( sK2 != k1_xboole_0 ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_5605,c_19,c_24,c_626,c_1738,c_1741,c_2727,c_4192]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2149,plain,
% 2.65/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1598,c_1597]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_5,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1595,plain,
% 2.65/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.65/0.99      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3157,plain,
% 2.65/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.65/0.99      | r1_tarski(k1_xboole_0,X1) = iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_2149,c_1595]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4141,plain,
% 2.65/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.65/0.99      | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_1895,c_3157]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4534,plain,
% 2.65/0.99      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_4141,c_24,c_1738,c_1741,c_4192]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4540,plain,
% 2.65/0.99      ( sK2 = k1_xboole_0 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.65/0.99      inference(superposition,[status(thm)],[c_4534,c_1599]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(contradiction,plain,
% 2.65/0.99      ( $false ),
% 2.65/0.99      inference(minisat,[status(thm)],[c_8424,c_6070,c_4540]) ).
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  ------                               Statistics
% 2.65/0.99  
% 2.65/0.99  ------ General
% 2.65/0.99  
% 2.65/0.99  abstr_ref_over_cycles:                  0
% 2.65/0.99  abstr_ref_under_cycles:                 0
% 2.65/0.99  gc_basic_clause_elim:                   0
% 2.65/0.99  forced_gc_time:                         0
% 2.65/0.99  parsing_time:                           0.017
% 2.65/0.99  unif_index_cands_time:                  0.
% 2.65/0.99  unif_index_add_time:                    0.
% 2.65/0.99  orderings_time:                         0.
% 2.65/0.99  out_proof_time:                         0.01
% 2.65/0.99  total_time:                             0.246
% 2.65/0.99  num_of_symbols:                         45
% 2.65/0.99  num_of_terms:                           6519
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing
% 2.65/0.99  
% 2.65/0.99  num_of_splits:                          0
% 2.65/0.99  num_of_split_atoms:                     0
% 2.65/0.99  num_of_reused_defs:                     0
% 2.65/0.99  num_eq_ax_congr_red:                    10
% 2.65/0.99  num_of_sem_filtered_clauses:            1
% 2.65/0.99  num_of_subtypes:                        0
% 2.65/0.99  monotx_restored_types:                  0
% 2.65/0.99  sat_num_of_epr_types:                   0
% 2.65/0.99  sat_num_of_non_cyclic_types:            0
% 2.65/0.99  sat_guarded_non_collapsed_types:        0
% 2.65/0.99  num_pure_diseq_elim:                    0
% 2.65/0.99  simp_replaced_by:                       0
% 2.65/0.99  res_preprocessed:                       97
% 2.65/0.99  prep_upred:                             0
% 2.65/0.99  prep_unflattend:                        23
% 2.65/0.99  smt_new_axioms:                         0
% 2.65/0.99  pred_elim_cands:                        4
% 2.65/0.99  pred_elim:                              2
% 2.65/0.99  pred_elim_cl:                           2
% 2.65/0.99  pred_elim_cycles:                       6
% 2.65/0.99  merged_defs:                            16
% 2.65/0.99  merged_defs_ncl:                        0
% 2.65/0.99  bin_hyper_res:                          16
% 2.65/0.99  prep_cycles:                            4
% 2.65/0.99  pred_elim_time:                         0.011
% 2.65/0.99  splitting_time:                         0.
% 2.65/0.99  sem_filter_time:                        0.
% 2.65/0.99  monotx_time:                            0.001
% 2.65/0.99  subtype_inf_time:                       0.
% 2.65/0.99  
% 2.65/0.99  ------ Problem properties
% 2.65/0.99  
% 2.65/0.99  clauses:                                19
% 2.65/0.99  conjectures:                            6
% 2.65/0.99  epr:                                    6
% 2.65/0.99  horn:                                   18
% 2.65/0.99  ground:                                 5
% 2.65/0.99  unary:                                  2
% 2.65/0.99  binary:                                 11
% 2.65/0.99  lits:                                   46
% 2.65/0.99  lits_eq:                                7
% 2.65/0.99  fd_pure:                                0
% 2.65/0.99  fd_pseudo:                              0
% 2.65/0.99  fd_cond:                                1
% 2.65/0.99  fd_pseudo_cond:                         1
% 2.65/0.99  ac_symbols:                             0
% 2.65/0.99  
% 2.65/0.99  ------ Propositional Solver
% 2.65/0.99  
% 2.65/0.99  prop_solver_calls:                      27
% 2.65/0.99  prop_fast_solver_calls:                 932
% 2.65/0.99  smt_solver_calls:                       0
% 2.65/0.99  smt_fast_solver_calls:                  0
% 2.65/0.99  prop_num_of_clauses:                    3248
% 2.65/0.99  prop_preprocess_simplified:             6679
% 2.65/0.99  prop_fo_subsumed:                       42
% 2.65/0.99  prop_solver_time:                       0.
% 2.65/0.99  smt_solver_time:                        0.
% 2.65/0.99  smt_fast_solver_time:                   0.
% 2.65/0.99  prop_fast_solver_time:                  0.
% 2.65/0.99  prop_unsat_core_time:                   0.
% 2.65/0.99  
% 2.65/0.99  ------ QBF
% 2.65/0.99  
% 2.65/0.99  qbf_q_res:                              0
% 2.65/0.99  qbf_num_tautologies:                    0
% 2.65/0.99  qbf_prep_cycles:                        0
% 2.65/0.99  
% 2.65/0.99  ------ BMC1
% 2.65/0.99  
% 2.65/0.99  bmc1_current_bound:                     -1
% 2.65/0.99  bmc1_last_solved_bound:                 -1
% 2.65/0.99  bmc1_unsat_core_size:                   -1
% 2.65/0.99  bmc1_unsat_core_parents_size:           -1
% 2.65/0.99  bmc1_merge_next_fun:                    0
% 2.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.99  
% 2.65/0.99  ------ Instantiation
% 2.65/0.99  
% 2.65/0.99  inst_num_of_clauses:                    895
% 2.65/0.99  inst_num_in_passive:                    111
% 2.65/0.99  inst_num_in_active:                     413
% 2.65/0.99  inst_num_in_unprocessed:                372
% 2.65/0.99  inst_num_of_loops:                      440
% 2.65/0.99  inst_num_of_learning_restarts:          0
% 2.65/0.99  inst_num_moves_active_passive:          22
% 2.65/0.99  inst_lit_activity:                      0
% 2.65/0.99  inst_lit_activity_moves:                0
% 2.65/0.99  inst_num_tautologies:                   0
% 2.65/0.99  inst_num_prop_implied:                  0
% 2.65/0.99  inst_num_existing_simplified:           0
% 2.65/0.99  inst_num_eq_res_simplified:             0
% 2.65/0.99  inst_num_child_elim:                    0
% 2.65/0.99  inst_num_of_dismatching_blockings:      334
% 2.65/0.99  inst_num_of_non_proper_insts:           1298
% 2.65/0.99  inst_num_of_duplicates:                 0
% 2.65/0.99  inst_inst_num_from_inst_to_res:         0
% 2.65/0.99  inst_dismatching_checking_time:         0.
% 2.65/0.99  
% 2.65/0.99  ------ Resolution
% 2.65/0.99  
% 2.65/0.99  res_num_of_clauses:                     0
% 2.65/0.99  res_num_in_passive:                     0
% 2.65/0.99  res_num_in_active:                      0
% 2.65/0.99  res_num_of_loops:                       101
% 2.65/0.99  res_forward_subset_subsumed:            73
% 2.65/0.99  res_backward_subset_subsumed:           4
% 2.65/0.99  res_forward_subsumed:                   0
% 2.65/0.99  res_backward_subsumed:                  0
% 2.65/0.99  res_forward_subsumption_resolution:     0
% 2.65/0.99  res_backward_subsumption_resolution:    0
% 2.65/0.99  res_clause_to_clause_subsumption:       1036
% 2.65/0.99  res_orphan_elimination:                 0
% 2.65/0.99  res_tautology_del:                      178
% 2.65/0.99  res_num_eq_res_simplified:              0
% 2.65/0.99  res_num_sel_changes:                    0
% 2.65/0.99  res_moves_from_active_to_pass:          0
% 2.65/0.99  
% 2.65/0.99  ------ Superposition
% 2.65/0.99  
% 2.65/0.99  sup_time_total:                         0.
% 2.65/0.99  sup_time_generating:                    0.
% 2.65/0.99  sup_time_sim_full:                      0.
% 2.65/0.99  sup_time_sim_immed:                     0.
% 2.65/0.99  
% 2.65/0.99  sup_num_of_clauses:                     139
% 2.65/0.99  sup_num_in_active:                      61
% 2.65/0.99  sup_num_in_passive:                     78
% 2.65/0.99  sup_num_of_loops:                       86
% 2.65/0.99  sup_fw_superposition:                   137
% 2.65/0.99  sup_bw_superposition:                   126
% 2.65/0.99  sup_immediate_simplified:               57
% 2.65/0.99  sup_given_eliminated:                   1
% 2.65/0.99  comparisons_done:                       0
% 2.65/0.99  comparisons_avoided:                    0
% 2.65/0.99  
% 2.65/0.99  ------ Simplifications
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  sim_fw_subset_subsumed:                 17
% 2.65/0.99  sim_bw_subset_subsumed:                 7
% 2.65/0.99  sim_fw_subsumed:                        27
% 2.65/0.99  sim_bw_subsumed:                        10
% 2.65/0.99  sim_fw_subsumption_res:                 2
% 2.65/0.99  sim_bw_subsumption_res:                 0
% 2.65/0.99  sim_tautology_del:                      14
% 2.65/0.99  sim_eq_tautology_del:                   10
% 2.65/0.99  sim_eq_res_simp:                        0
% 2.65/0.99  sim_fw_demodulated:                     14
% 2.65/0.99  sim_bw_demodulated:                     23
% 2.65/0.99  sim_light_normalised:                   11
% 2.65/0.99  sim_joinable_taut:                      0
% 2.65/0.99  sim_joinable_simp:                      0
% 2.65/0.99  sim_ac_normalised:                      0
% 2.65/0.99  sim_smt_subsumption:                    0
% 2.65/0.99  
%------------------------------------------------------------------------------
