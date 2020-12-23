%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:12 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 928 expanded)
%              Number of clauses        :   75 ( 231 expanded)
%              Number of leaves         :   14 ( 234 expanded)
%              Depth                    :   22
%              Number of atoms          :  467 (7823 expanded)
%              Number of equality atoms :  129 (1323 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,
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

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1480,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1482,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_304,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_305,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_1476,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_1818,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1476])).

cnf(c_9,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_289,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_290,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_290])).

cnf(c_545,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_547,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_16])).

cnf(c_549,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_572,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_290])).

cnf(c_573,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_575,plain,
    ( v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_16])).

cnf(c_577,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_10,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_274,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_275,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_1478,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_2324,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1478])).

cnf(c_6,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_253,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_254,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_17])).

cnf(c_259,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_1609,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_1615,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1649,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1679,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1770,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_1044,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1803,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1938,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1045,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1656,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_2162,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1656])).

cnf(c_2336,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2324])).

cnf(c_2338,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2324,c_16,c_1609,c_1615,c_1627,c_1649,c_1770,c_1803,c_1938,c_2162,c_2336])).

cnf(c_2832,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_2836,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2832])).

cnf(c_2997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1818,c_16,c_549,c_577,c_1609,c_1615,c_1627,c_1649,c_1770,c_1803,c_1938,c_2162,c_2336,c_2836])).

cnf(c_3008,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_2997])).

cnf(c_3011,plain,
    ( r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3008,c_2338])).

cnf(c_13,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_290])).

cnf(c_559,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_561,plain,
    ( r1_tarski(sK2,sK1)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_16])).

cnf(c_563,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_3724,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3011,c_16,c_563,c_1609,c_1615,c_1627,c_1649,c_1770,c_1803,c_1938,c_2162,c_2336])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1490,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3730,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3724,c_1490])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4283,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3730,c_3])).

cnf(c_11,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_290])).

cnf(c_587,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_589,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4283,c_2338,c_589])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:21:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.63/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/0.95  
% 2.63/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/0.95  
% 2.63/0.95  ------  iProver source info
% 2.63/0.95  
% 2.63/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.63/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/0.95  git: non_committed_changes: false
% 2.63/0.95  git: last_make_outside_of_git: false
% 2.63/0.95  
% 2.63/0.95  ------ 
% 2.63/0.95  
% 2.63/0.95  ------ Input Options
% 2.63/0.95  
% 2.63/0.95  --out_options                           all
% 2.63/0.95  --tptp_safe_out                         true
% 2.63/0.95  --problem_path                          ""
% 2.63/0.95  --include_path                          ""
% 2.63/0.95  --clausifier                            res/vclausify_rel
% 2.63/0.95  --clausifier_options                    --mode clausify
% 2.63/0.95  --stdin                                 false
% 2.63/0.95  --stats_out                             all
% 2.63/0.95  
% 2.63/0.95  ------ General Options
% 2.63/0.95  
% 2.63/0.95  --fof                                   false
% 2.63/0.95  --time_out_real                         305.
% 2.63/0.95  --time_out_virtual                      -1.
% 2.63/0.95  --symbol_type_check                     false
% 2.63/0.95  --clausify_out                          false
% 2.63/0.95  --sig_cnt_out                           false
% 2.63/0.95  --trig_cnt_out                          false
% 2.63/0.95  --trig_cnt_out_tolerance                1.
% 2.63/0.95  --trig_cnt_out_sk_spl                   false
% 2.63/0.95  --abstr_cl_out                          false
% 2.63/0.95  
% 2.63/0.95  ------ Global Options
% 2.63/0.95  
% 2.63/0.95  --schedule                              default
% 2.63/0.95  --add_important_lit                     false
% 2.63/0.95  --prop_solver_per_cl                    1000
% 2.63/0.95  --min_unsat_core                        false
% 2.63/0.95  --soft_assumptions                      false
% 2.63/0.95  --soft_lemma_size                       3
% 2.63/0.95  --prop_impl_unit_size                   0
% 2.63/0.95  --prop_impl_unit                        []
% 2.63/0.95  --share_sel_clauses                     true
% 2.63/0.95  --reset_solvers                         false
% 2.63/0.95  --bc_imp_inh                            [conj_cone]
% 2.63/0.95  --conj_cone_tolerance                   3.
% 2.63/0.95  --extra_neg_conj                        none
% 2.63/0.95  --large_theory_mode                     true
% 2.63/0.95  --prolific_symb_bound                   200
% 2.63/0.95  --lt_threshold                          2000
% 2.63/0.95  --clause_weak_htbl                      true
% 2.63/0.95  --gc_record_bc_elim                     false
% 2.63/0.95  
% 2.63/0.95  ------ Preprocessing Options
% 2.63/0.95  
% 2.63/0.95  --preprocessing_flag                    true
% 2.63/0.95  --time_out_prep_mult                    0.1
% 2.63/0.95  --splitting_mode                        input
% 2.63/0.95  --splitting_grd                         true
% 2.63/0.95  --splitting_cvd                         false
% 2.63/0.95  --splitting_cvd_svl                     false
% 2.63/0.95  --splitting_nvd                         32
% 2.63/0.95  --sub_typing                            true
% 2.63/0.95  --prep_gs_sim                           true
% 2.63/0.95  --prep_unflatten                        true
% 2.63/0.95  --prep_res_sim                          true
% 2.63/0.95  --prep_upred                            true
% 2.63/0.95  --prep_sem_filter                       exhaustive
% 2.63/0.95  --prep_sem_filter_out                   false
% 2.63/0.95  --pred_elim                             true
% 2.63/0.95  --res_sim_input                         true
% 2.63/0.95  --eq_ax_congr_red                       true
% 2.63/0.95  --pure_diseq_elim                       true
% 2.63/0.95  --brand_transform                       false
% 2.63/0.95  --non_eq_to_eq                          false
% 2.63/0.95  --prep_def_merge                        true
% 2.63/0.95  --prep_def_merge_prop_impl              false
% 2.63/0.95  --prep_def_merge_mbd                    true
% 2.63/0.95  --prep_def_merge_tr_red                 false
% 2.63/0.95  --prep_def_merge_tr_cl                  false
% 2.63/0.95  --smt_preprocessing                     true
% 2.63/0.95  --smt_ac_axioms                         fast
% 2.63/0.95  --preprocessed_out                      false
% 2.63/0.95  --preprocessed_stats                    false
% 2.63/0.95  
% 2.63/0.95  ------ Abstraction refinement Options
% 2.63/0.95  
% 2.63/0.95  --abstr_ref                             []
% 2.63/0.95  --abstr_ref_prep                        false
% 2.63/0.95  --abstr_ref_until_sat                   false
% 2.63/0.95  --abstr_ref_sig_restrict                funpre
% 2.63/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.95  --abstr_ref_under                       []
% 2.63/0.95  
% 2.63/0.95  ------ SAT Options
% 2.63/0.95  
% 2.63/0.95  --sat_mode                              false
% 2.63/0.95  --sat_fm_restart_options                ""
% 2.63/0.95  --sat_gr_def                            false
% 2.63/0.95  --sat_epr_types                         true
% 2.63/0.95  --sat_non_cyclic_types                  false
% 2.63/0.95  --sat_finite_models                     false
% 2.63/0.95  --sat_fm_lemmas                         false
% 2.63/0.95  --sat_fm_prep                           false
% 2.63/0.95  --sat_fm_uc_incr                        true
% 2.63/0.95  --sat_out_model                         small
% 2.63/0.95  --sat_out_clauses                       false
% 2.63/0.95  
% 2.63/0.95  ------ QBF Options
% 2.63/0.95  
% 2.63/0.95  --qbf_mode                              false
% 2.63/0.95  --qbf_elim_univ                         false
% 2.63/0.95  --qbf_dom_inst                          none
% 2.63/0.95  --qbf_dom_pre_inst                      false
% 2.63/0.95  --qbf_sk_in                             false
% 2.63/0.95  --qbf_pred_elim                         true
% 2.63/0.95  --qbf_split                             512
% 2.63/0.95  
% 2.63/0.95  ------ BMC1 Options
% 2.63/0.95  
% 2.63/0.95  --bmc1_incremental                      false
% 2.63/0.95  --bmc1_axioms                           reachable_all
% 2.63/0.95  --bmc1_min_bound                        0
% 2.63/0.95  --bmc1_max_bound                        -1
% 2.63/0.95  --bmc1_max_bound_default                -1
% 2.63/0.95  --bmc1_symbol_reachability              true
% 2.63/0.95  --bmc1_property_lemmas                  false
% 2.63/0.95  --bmc1_k_induction                      false
% 2.63/0.95  --bmc1_non_equiv_states                 false
% 2.63/0.95  --bmc1_deadlock                         false
% 2.63/0.95  --bmc1_ucm                              false
% 2.63/0.95  --bmc1_add_unsat_core                   none
% 2.63/0.95  --bmc1_unsat_core_children              false
% 2.63/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.95  --bmc1_out_stat                         full
% 2.63/0.95  --bmc1_ground_init                      false
% 2.63/0.95  --bmc1_pre_inst_next_state              false
% 2.63/0.95  --bmc1_pre_inst_state                   false
% 2.63/0.95  --bmc1_pre_inst_reach_state             false
% 2.63/0.95  --bmc1_out_unsat_core                   false
% 2.63/0.95  --bmc1_aig_witness_out                  false
% 2.63/0.95  --bmc1_verbose                          false
% 2.63/0.95  --bmc1_dump_clauses_tptp                false
% 2.63/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.95  --bmc1_dump_file                        -
% 2.63/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.95  --bmc1_ucm_extend_mode                  1
% 2.63/0.95  --bmc1_ucm_init_mode                    2
% 2.63/0.95  --bmc1_ucm_cone_mode                    none
% 2.63/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.95  --bmc1_ucm_relax_model                  4
% 2.63/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.95  --bmc1_ucm_layered_model                none
% 2.63/0.95  --bmc1_ucm_max_lemma_size               10
% 2.63/0.95  
% 2.63/0.95  ------ AIG Options
% 2.63/0.95  
% 2.63/0.95  --aig_mode                              false
% 2.63/0.95  
% 2.63/0.95  ------ Instantiation Options
% 2.63/0.95  
% 2.63/0.95  --instantiation_flag                    true
% 2.63/0.95  --inst_sos_flag                         false
% 2.63/0.95  --inst_sos_phase                        true
% 2.63/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.95  --inst_lit_sel_side                     num_symb
% 2.63/0.95  --inst_solver_per_active                1400
% 2.63/0.95  --inst_solver_calls_frac                1.
% 2.63/0.95  --inst_passive_queue_type               priority_queues
% 2.63/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.95  --inst_passive_queues_freq              [25;2]
% 2.63/0.95  --inst_dismatching                      true
% 2.63/0.95  --inst_eager_unprocessed_to_passive     true
% 2.63/0.95  --inst_prop_sim_given                   true
% 2.63/0.95  --inst_prop_sim_new                     false
% 2.63/0.95  --inst_subs_new                         false
% 2.63/0.95  --inst_eq_res_simp                      false
% 2.63/0.95  --inst_subs_given                       false
% 2.63/0.95  --inst_orphan_elimination               true
% 2.63/0.95  --inst_learning_loop_flag               true
% 2.63/0.95  --inst_learning_start                   3000
% 2.63/0.95  --inst_learning_factor                  2
% 2.63/0.95  --inst_start_prop_sim_after_learn       3
% 2.63/0.95  --inst_sel_renew                        solver
% 2.63/0.95  --inst_lit_activity_flag                true
% 2.63/0.95  --inst_restr_to_given                   false
% 2.63/0.95  --inst_activity_threshold               500
% 2.63/0.95  --inst_out_proof                        true
% 2.63/0.95  
% 2.63/0.95  ------ Resolution Options
% 2.63/0.95  
% 2.63/0.95  --resolution_flag                       true
% 2.63/0.95  --res_lit_sel                           adaptive
% 2.63/0.95  --res_lit_sel_side                      none
% 2.63/0.95  --res_ordering                          kbo
% 2.63/0.95  --res_to_prop_solver                    active
% 2.63/0.95  --res_prop_simpl_new                    false
% 2.63/0.95  --res_prop_simpl_given                  true
% 2.63/0.95  --res_passive_queue_type                priority_queues
% 2.63/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.95  --res_passive_queues_freq               [15;5]
% 2.63/0.95  --res_forward_subs                      full
% 2.63/0.95  --res_backward_subs                     full
% 2.63/0.95  --res_forward_subs_resolution           true
% 2.63/0.95  --res_backward_subs_resolution          true
% 2.63/0.95  --res_orphan_elimination                true
% 2.63/0.95  --res_time_limit                        2.
% 2.63/0.95  --res_out_proof                         true
% 2.63/0.95  
% 2.63/0.95  ------ Superposition Options
% 2.63/0.95  
% 2.63/0.95  --superposition_flag                    true
% 2.63/0.95  --sup_passive_queue_type                priority_queues
% 2.63/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.95  --demod_completeness_check              fast
% 2.63/0.95  --demod_use_ground                      true
% 2.63/0.95  --sup_to_prop_solver                    passive
% 2.63/0.95  --sup_prop_simpl_new                    true
% 2.63/0.95  --sup_prop_simpl_given                  true
% 2.63/0.95  --sup_fun_splitting                     false
% 2.63/0.95  --sup_smt_interval                      50000
% 2.63/0.95  
% 2.63/0.95  ------ Superposition Simplification Setup
% 2.63/0.95  
% 2.63/0.95  --sup_indices_passive                   []
% 2.63/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.95  --sup_full_bw                           [BwDemod]
% 2.63/0.95  --sup_immed_triv                        [TrivRules]
% 2.63/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.95  --sup_immed_bw_main                     []
% 2.63/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.95  
% 2.63/0.95  ------ Combination Options
% 2.63/0.95  
% 2.63/0.95  --comb_res_mult                         3
% 2.63/0.95  --comb_sup_mult                         2
% 2.63/0.95  --comb_inst_mult                        10
% 2.63/0.95  
% 2.63/0.95  ------ Debug Options
% 2.63/0.95  
% 2.63/0.95  --dbg_backtrace                         false
% 2.63/0.95  --dbg_dump_prop_clauses                 false
% 2.63/0.95  --dbg_dump_prop_clauses_file            -
% 2.63/0.95  --dbg_out_stat                          false
% 2.63/0.95  ------ Parsing...
% 2.63/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/0.95  
% 2.63/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.63/0.95  
% 2.63/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/0.95  
% 2.63/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/0.95  ------ Proving...
% 2.63/0.95  ------ Problem Properties 
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  clauses                                 17
% 2.63/0.95  conjectures                             6
% 2.63/0.95  EPR                                     4
% 2.63/0.95  Horn                                    16
% 2.63/0.95  unary                                   2
% 2.63/0.95  binary                                  10
% 2.63/0.95  lits                                    41
% 2.63/0.95  lits eq                                 7
% 2.63/0.95  fd_pure                                 0
% 2.63/0.95  fd_pseudo                               0
% 2.63/0.95  fd_cond                                 1
% 2.63/0.95  fd_pseudo_cond                          0
% 2.63/0.95  AC symbols                              0
% 2.63/0.95  
% 2.63/0.95  ------ Schedule dynamic 5 is on 
% 2.63/0.95  
% 2.63/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  ------ 
% 2.63/0.95  Current options:
% 2.63/0.95  ------ 
% 2.63/0.95  
% 2.63/0.95  ------ Input Options
% 2.63/0.95  
% 2.63/0.95  --out_options                           all
% 2.63/0.95  --tptp_safe_out                         true
% 2.63/0.95  --problem_path                          ""
% 2.63/0.95  --include_path                          ""
% 2.63/0.95  --clausifier                            res/vclausify_rel
% 2.63/0.95  --clausifier_options                    --mode clausify
% 2.63/0.95  --stdin                                 false
% 2.63/0.95  --stats_out                             all
% 2.63/0.95  
% 2.63/0.95  ------ General Options
% 2.63/0.95  
% 2.63/0.95  --fof                                   false
% 2.63/0.95  --time_out_real                         305.
% 2.63/0.95  --time_out_virtual                      -1.
% 2.63/0.95  --symbol_type_check                     false
% 2.63/0.95  --clausify_out                          false
% 2.63/0.95  --sig_cnt_out                           false
% 2.63/0.95  --trig_cnt_out                          false
% 2.63/0.95  --trig_cnt_out_tolerance                1.
% 2.63/0.95  --trig_cnt_out_sk_spl                   false
% 2.63/0.95  --abstr_cl_out                          false
% 2.63/0.95  
% 2.63/0.95  ------ Global Options
% 2.63/0.95  
% 2.63/0.95  --schedule                              default
% 2.63/0.95  --add_important_lit                     false
% 2.63/0.95  --prop_solver_per_cl                    1000
% 2.63/0.95  --min_unsat_core                        false
% 2.63/0.95  --soft_assumptions                      false
% 2.63/0.95  --soft_lemma_size                       3
% 2.63/0.95  --prop_impl_unit_size                   0
% 2.63/0.95  --prop_impl_unit                        []
% 2.63/0.95  --share_sel_clauses                     true
% 2.63/0.95  --reset_solvers                         false
% 2.63/0.95  --bc_imp_inh                            [conj_cone]
% 2.63/0.95  --conj_cone_tolerance                   3.
% 2.63/0.95  --extra_neg_conj                        none
% 2.63/0.95  --large_theory_mode                     true
% 2.63/0.95  --prolific_symb_bound                   200
% 2.63/0.95  --lt_threshold                          2000
% 2.63/0.95  --clause_weak_htbl                      true
% 2.63/0.95  --gc_record_bc_elim                     false
% 2.63/0.95  
% 2.63/0.95  ------ Preprocessing Options
% 2.63/0.95  
% 2.63/0.95  --preprocessing_flag                    true
% 2.63/0.95  --time_out_prep_mult                    0.1
% 2.63/0.95  --splitting_mode                        input
% 2.63/0.95  --splitting_grd                         true
% 2.63/0.95  --splitting_cvd                         false
% 2.63/0.95  --splitting_cvd_svl                     false
% 2.63/0.95  --splitting_nvd                         32
% 2.63/0.95  --sub_typing                            true
% 2.63/0.95  --prep_gs_sim                           true
% 2.63/0.95  --prep_unflatten                        true
% 2.63/0.95  --prep_res_sim                          true
% 2.63/0.95  --prep_upred                            true
% 2.63/0.95  --prep_sem_filter                       exhaustive
% 2.63/0.95  --prep_sem_filter_out                   false
% 2.63/0.95  --pred_elim                             true
% 2.63/0.95  --res_sim_input                         true
% 2.63/0.95  --eq_ax_congr_red                       true
% 2.63/0.95  --pure_diseq_elim                       true
% 2.63/0.95  --brand_transform                       false
% 2.63/0.95  --non_eq_to_eq                          false
% 2.63/0.95  --prep_def_merge                        true
% 2.63/0.95  --prep_def_merge_prop_impl              false
% 2.63/0.95  --prep_def_merge_mbd                    true
% 2.63/0.95  --prep_def_merge_tr_red                 false
% 2.63/0.95  --prep_def_merge_tr_cl                  false
% 2.63/0.95  --smt_preprocessing                     true
% 2.63/0.95  --smt_ac_axioms                         fast
% 2.63/0.95  --preprocessed_out                      false
% 2.63/0.95  --preprocessed_stats                    false
% 2.63/0.95  
% 2.63/0.95  ------ Abstraction refinement Options
% 2.63/0.95  
% 2.63/0.95  --abstr_ref                             []
% 2.63/0.95  --abstr_ref_prep                        false
% 2.63/0.95  --abstr_ref_until_sat                   false
% 2.63/0.95  --abstr_ref_sig_restrict                funpre
% 2.63/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.95  --abstr_ref_under                       []
% 2.63/0.95  
% 2.63/0.95  ------ SAT Options
% 2.63/0.95  
% 2.63/0.95  --sat_mode                              false
% 2.63/0.95  --sat_fm_restart_options                ""
% 2.63/0.95  --sat_gr_def                            false
% 2.63/0.95  --sat_epr_types                         true
% 2.63/0.95  --sat_non_cyclic_types                  false
% 2.63/0.95  --sat_finite_models                     false
% 2.63/0.95  --sat_fm_lemmas                         false
% 2.63/0.95  --sat_fm_prep                           false
% 2.63/0.95  --sat_fm_uc_incr                        true
% 2.63/0.95  --sat_out_model                         small
% 2.63/0.95  --sat_out_clauses                       false
% 2.63/0.95  
% 2.63/0.95  ------ QBF Options
% 2.63/0.95  
% 2.63/0.95  --qbf_mode                              false
% 2.63/0.95  --qbf_elim_univ                         false
% 2.63/0.95  --qbf_dom_inst                          none
% 2.63/0.95  --qbf_dom_pre_inst                      false
% 2.63/0.95  --qbf_sk_in                             false
% 2.63/0.95  --qbf_pred_elim                         true
% 2.63/0.95  --qbf_split                             512
% 2.63/0.95  
% 2.63/0.95  ------ BMC1 Options
% 2.63/0.95  
% 2.63/0.95  --bmc1_incremental                      false
% 2.63/0.95  --bmc1_axioms                           reachable_all
% 2.63/0.95  --bmc1_min_bound                        0
% 2.63/0.95  --bmc1_max_bound                        -1
% 2.63/0.95  --bmc1_max_bound_default                -1
% 2.63/0.95  --bmc1_symbol_reachability              true
% 2.63/0.95  --bmc1_property_lemmas                  false
% 2.63/0.95  --bmc1_k_induction                      false
% 2.63/0.95  --bmc1_non_equiv_states                 false
% 2.63/0.95  --bmc1_deadlock                         false
% 2.63/0.95  --bmc1_ucm                              false
% 2.63/0.95  --bmc1_add_unsat_core                   none
% 2.63/0.95  --bmc1_unsat_core_children              false
% 2.63/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.95  --bmc1_out_stat                         full
% 2.63/0.95  --bmc1_ground_init                      false
% 2.63/0.95  --bmc1_pre_inst_next_state              false
% 2.63/0.95  --bmc1_pre_inst_state                   false
% 2.63/0.95  --bmc1_pre_inst_reach_state             false
% 2.63/0.95  --bmc1_out_unsat_core                   false
% 2.63/0.95  --bmc1_aig_witness_out                  false
% 2.63/0.95  --bmc1_verbose                          false
% 2.63/0.95  --bmc1_dump_clauses_tptp                false
% 2.63/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.95  --bmc1_dump_file                        -
% 2.63/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.95  --bmc1_ucm_extend_mode                  1
% 2.63/0.95  --bmc1_ucm_init_mode                    2
% 2.63/0.95  --bmc1_ucm_cone_mode                    none
% 2.63/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.95  --bmc1_ucm_relax_model                  4
% 2.63/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.95  --bmc1_ucm_layered_model                none
% 2.63/0.95  --bmc1_ucm_max_lemma_size               10
% 2.63/0.95  
% 2.63/0.95  ------ AIG Options
% 2.63/0.95  
% 2.63/0.95  --aig_mode                              false
% 2.63/0.95  
% 2.63/0.95  ------ Instantiation Options
% 2.63/0.95  
% 2.63/0.95  --instantiation_flag                    true
% 2.63/0.95  --inst_sos_flag                         false
% 2.63/0.95  --inst_sos_phase                        true
% 2.63/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.95  --inst_lit_sel_side                     none
% 2.63/0.95  --inst_solver_per_active                1400
% 2.63/0.95  --inst_solver_calls_frac                1.
% 2.63/0.95  --inst_passive_queue_type               priority_queues
% 2.63/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.95  --inst_passive_queues_freq              [25;2]
% 2.63/0.95  --inst_dismatching                      true
% 2.63/0.95  --inst_eager_unprocessed_to_passive     true
% 2.63/0.95  --inst_prop_sim_given                   true
% 2.63/0.95  --inst_prop_sim_new                     false
% 2.63/0.95  --inst_subs_new                         false
% 2.63/0.95  --inst_eq_res_simp                      false
% 2.63/0.95  --inst_subs_given                       false
% 2.63/0.95  --inst_orphan_elimination               true
% 2.63/0.95  --inst_learning_loop_flag               true
% 2.63/0.95  --inst_learning_start                   3000
% 2.63/0.95  --inst_learning_factor                  2
% 2.63/0.95  --inst_start_prop_sim_after_learn       3
% 2.63/0.95  --inst_sel_renew                        solver
% 2.63/0.95  --inst_lit_activity_flag                true
% 2.63/0.95  --inst_restr_to_given                   false
% 2.63/0.95  --inst_activity_threshold               500
% 2.63/0.95  --inst_out_proof                        true
% 2.63/0.95  
% 2.63/0.95  ------ Resolution Options
% 2.63/0.95  
% 2.63/0.95  --resolution_flag                       false
% 2.63/0.95  --res_lit_sel                           adaptive
% 2.63/0.95  --res_lit_sel_side                      none
% 2.63/0.95  --res_ordering                          kbo
% 2.63/0.95  --res_to_prop_solver                    active
% 2.63/0.95  --res_prop_simpl_new                    false
% 2.63/0.95  --res_prop_simpl_given                  true
% 2.63/0.95  --res_passive_queue_type                priority_queues
% 2.63/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.95  --res_passive_queues_freq               [15;5]
% 2.63/0.95  --res_forward_subs                      full
% 2.63/0.95  --res_backward_subs                     full
% 2.63/0.95  --res_forward_subs_resolution           true
% 2.63/0.95  --res_backward_subs_resolution          true
% 2.63/0.95  --res_orphan_elimination                true
% 2.63/0.95  --res_time_limit                        2.
% 2.63/0.95  --res_out_proof                         true
% 2.63/0.95  
% 2.63/0.95  ------ Superposition Options
% 2.63/0.95  
% 2.63/0.95  --superposition_flag                    true
% 2.63/0.95  --sup_passive_queue_type                priority_queues
% 2.63/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.95  --demod_completeness_check              fast
% 2.63/0.95  --demod_use_ground                      true
% 2.63/0.95  --sup_to_prop_solver                    passive
% 2.63/0.95  --sup_prop_simpl_new                    true
% 2.63/0.95  --sup_prop_simpl_given                  true
% 2.63/0.95  --sup_fun_splitting                     false
% 2.63/0.95  --sup_smt_interval                      50000
% 2.63/0.95  
% 2.63/0.95  ------ Superposition Simplification Setup
% 2.63/0.95  
% 2.63/0.95  --sup_indices_passive                   []
% 2.63/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.95  --sup_full_bw                           [BwDemod]
% 2.63/0.95  --sup_immed_triv                        [TrivRules]
% 2.63/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.95  --sup_immed_bw_main                     []
% 2.63/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.95  
% 2.63/0.95  ------ Combination Options
% 2.63/0.95  
% 2.63/0.95  --comb_res_mult                         3
% 2.63/0.95  --comb_sup_mult                         2
% 2.63/0.95  --comb_inst_mult                        10
% 2.63/0.95  
% 2.63/0.95  ------ Debug Options
% 2.63/0.95  
% 2.63/0.95  --dbg_backtrace                         false
% 2.63/0.95  --dbg_dump_prop_clauses                 false
% 2.63/0.95  --dbg_dump_prop_clauses_file            -
% 2.63/0.95  --dbg_out_stat                          false
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  ------ Proving...
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  % SZS status Theorem for theBenchmark.p
% 2.63/0.95  
% 2.63/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/0.95  
% 2.63/0.95  fof(f9,conjecture,(
% 2.63/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f10,negated_conjecture,(
% 2.63/0.95    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.63/0.95    inference(negated_conjecture,[],[f9])).
% 2.63/0.95  
% 2.63/0.95  fof(f19,plain,(
% 2.63/0.95    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.63/0.95    inference(ennf_transformation,[],[f10])).
% 2.63/0.95  
% 2.63/0.95  fof(f20,plain,(
% 2.63/0.95    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.95    inference(flattening,[],[f19])).
% 2.63/0.95  
% 2.63/0.95  fof(f24,plain,(
% 2.63/0.95    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.95    inference(nnf_transformation,[],[f20])).
% 2.63/0.95  
% 2.63/0.95  fof(f25,plain,(
% 2.63/0.95    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.95    inference(flattening,[],[f24])).
% 2.63/0.95  
% 2.63/0.95  fof(f26,plain,(
% 2.63/0.95    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.95    inference(rectify,[],[f25])).
% 2.63/0.95  
% 2.63/0.95  fof(f29,plain,(
% 2.63/0.95    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.63/0.95    introduced(choice_axiom,[])).
% 2.63/0.95  
% 2.63/0.95  fof(f28,plain,(
% 2.63/0.95    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.63/0.95    introduced(choice_axiom,[])).
% 2.63/0.95  
% 2.63/0.95  fof(f27,plain,(
% 2.63/0.95    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.63/0.95    introduced(choice_axiom,[])).
% 2.63/0.95  
% 2.63/0.95  fof(f30,plain,(
% 2.63/0.95    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.63/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 2.63/0.95  
% 2.63/0.95  fof(f44,plain,(
% 2.63/0.95    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f46,plain,(
% 2.63/0.95    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f7,axiom,(
% 2.63/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f16,plain,(
% 2.63/0.95    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.95    inference(ennf_transformation,[],[f7])).
% 2.63/0.95  
% 2.63/0.95  fof(f17,plain,(
% 2.63/0.95    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.95    inference(flattening,[],[f16])).
% 2.63/0.95  
% 2.63/0.95  fof(f39,plain,(
% 2.63/0.95    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f17])).
% 2.63/0.95  
% 2.63/0.95  fof(f43,plain,(
% 2.63/0.95    l1_pre_topc(sK0)),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f8,axiom,(
% 2.63/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f18,plain,(
% 2.63/0.95    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.95    inference(ennf_transformation,[],[f8])).
% 2.63/0.95  
% 2.63/0.95  fof(f23,plain,(
% 2.63/0.95    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.95    inference(nnf_transformation,[],[f18])).
% 2.63/0.95  
% 2.63/0.95  fof(f41,plain,(
% 2.63/0.95    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f23])).
% 2.63/0.95  
% 2.63/0.95  fof(f48,plain,(
% 2.63/0.95    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f40,plain,(
% 2.63/0.95    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f23])).
% 2.63/0.95  
% 2.63/0.95  fof(f5,axiom,(
% 2.63/0.95    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f13,plain,(
% 2.63/0.95    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.63/0.95    inference(ennf_transformation,[],[f5])).
% 2.63/0.95  
% 2.63/0.95  fof(f14,plain,(
% 2.63/0.95    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.63/0.95    inference(flattening,[],[f13])).
% 2.63/0.95  
% 2.63/0.95  fof(f37,plain,(
% 2.63/0.95    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f14])).
% 2.63/0.95  
% 2.63/0.95  fof(f42,plain,(
% 2.63/0.95    v2_pre_topc(sK0)),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f6,axiom,(
% 2.63/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f15,plain,(
% 2.63/0.95    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.95    inference(ennf_transformation,[],[f6])).
% 2.63/0.95  
% 2.63/0.95  fof(f38,plain,(
% 2.63/0.95    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f15])).
% 2.63/0.95  
% 2.63/0.95  fof(f4,axiom,(
% 2.63/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f22,plain,(
% 2.63/0.95    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.63/0.95    inference(nnf_transformation,[],[f4])).
% 2.63/0.95  
% 2.63/0.95  fof(f35,plain,(
% 2.63/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.63/0.95    inference(cnf_transformation,[],[f22])).
% 2.63/0.95  
% 2.63/0.95  fof(f45,plain,(
% 2.63/0.95    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f2,axiom,(
% 2.63/0.95    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f11,plain,(
% 2.63/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.63/0.95    inference(ennf_transformation,[],[f2])).
% 2.63/0.95  
% 2.63/0.95  fof(f12,plain,(
% 2.63/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.63/0.95    inference(flattening,[],[f11])).
% 2.63/0.95  
% 2.63/0.95  fof(f33,plain,(
% 2.63/0.95    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f12])).
% 2.63/0.95  
% 2.63/0.95  fof(f36,plain,(
% 2.63/0.95    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f22])).
% 2.63/0.95  
% 2.63/0.95  fof(f47,plain,(
% 2.63/0.95    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  fof(f1,axiom,(
% 2.63/0.95    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f21,plain,(
% 2.63/0.95    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.63/0.95    inference(nnf_transformation,[],[f1])).
% 2.63/0.95  
% 2.63/0.95  fof(f32,plain,(
% 2.63/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.63/0.95    inference(cnf_transformation,[],[f21])).
% 2.63/0.95  
% 2.63/0.95  fof(f3,axiom,(
% 2.63/0.95    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.63/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.95  
% 2.63/0.95  fof(f34,plain,(
% 2.63/0.95    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.63/0.95    inference(cnf_transformation,[],[f3])).
% 2.63/0.95  
% 2.63/0.95  fof(f49,plain,(
% 2.63/0.95    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.63/0.95    inference(cnf_transformation,[],[f30])).
% 2.63/0.95  
% 2.63/0.95  cnf(c_16,negated_conjecture,
% 2.63/0.95      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.63/0.95      inference(cnf_transformation,[],[f44]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1480,plain,
% 2.63/0.95      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_14,negated_conjecture,
% 2.63/0.95      ( ~ v2_tops_1(sK1,sK0)
% 2.63/0.95      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.63/0.95      inference(cnf_transformation,[],[f46]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1482,plain,
% 2.63/0.95      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.63/0.95      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_8,plain,
% 2.63/0.95      ( ~ v3_pre_topc(X0,X1)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | ~ r1_tarski(X0,X2)
% 2.63/0.95      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.63/0.95      | ~ l1_pre_topc(X1) ),
% 2.63/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_17,negated_conjecture,
% 2.63/0.95      ( l1_pre_topc(sK0) ),
% 2.63/0.95      inference(cnf_transformation,[],[f43]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_304,plain,
% 2.63/0.95      ( ~ v3_pre_topc(X0,X1)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | ~ r1_tarski(X0,X2)
% 2.63/0.95      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.63/0.95      | sK0 != X1 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_305,plain,
% 2.63/0.95      ( ~ v3_pre_topc(X0,sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ r1_tarski(X0,X1)
% 2.63/0.95      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_304]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1476,plain,
% 2.63/0.95      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.63/0.95      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.63/0.95      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.63/0.95      | r1_tarski(X0,X1) != iProver_top
% 2.63/0.95      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1818,plain,
% 2.63/0.95      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.63/0.95      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.63/0.95      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,X0) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.63/0.95      inference(superposition,[status(thm)],[c_1482,c_1476]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_9,plain,
% 2.63/0.95      ( v2_tops_1(X0,X1)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | ~ l1_pre_topc(X1)
% 2.63/0.95      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.63/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_289,plain,
% 2.63/0.95      ( v2_tops_1(X0,X1)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.63/0.95      | sK0 != X1 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_290,plain,
% 2.63/0.95      ( v2_tops_1(X0,sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_289]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_544,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.63/0.95      | sK0 != sK0
% 2.63/0.95      | sK1 != X0 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_14,c_290]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_545,plain,
% 2.63/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_544]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_547,plain,
% 2.63/0.95      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_545,c_16]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_549,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.63/0.95      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_12,negated_conjecture,
% 2.63/0.95      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.63/0.95      inference(cnf_transformation,[],[f48]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_572,plain,
% 2.63/0.95      ( v3_pre_topc(sK2,sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.63/0.95      | sK0 != sK0
% 2.63/0.95      | sK1 != X0 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_12,c_290]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_573,plain,
% 2.63/0.95      ( v3_pre_topc(sK2,sK0)
% 2.63/0.95      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_572]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_575,plain,
% 2.63/0.95      ( v3_pre_topc(sK2,sK0) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_573,c_16]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_577,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.63/0.95      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_10,plain,
% 2.63/0.95      ( ~ v2_tops_1(X0,X1)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | ~ l1_pre_topc(X1)
% 2.63/0.95      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.63/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_274,plain,
% 2.63/0.95      ( ~ v2_tops_1(X0,X1)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.63/0.95      | sK0 != X1 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_275,plain,
% 2.63/0.95      ( ~ v2_tops_1(X0,sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_274]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1478,plain,
% 2.63/0.95      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.63/0.95      | v2_tops_1(X0,sK0) != iProver_top
% 2.63/0.95      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2324,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.63/0.95      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.63/0.95      inference(superposition,[status(thm)],[c_1480,c_1478]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_6,plain,
% 2.63/0.95      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.63/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.95      | ~ v2_pre_topc(X0)
% 2.63/0.95      | ~ l1_pre_topc(X0) ),
% 2.63/0.95      inference(cnf_transformation,[],[f37]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_18,negated_conjecture,
% 2.63/0.95      ( v2_pre_topc(sK0) ),
% 2.63/0.95      inference(cnf_transformation,[],[f42]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_253,plain,
% 2.63/0.95      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.63/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.95      | ~ l1_pre_topc(X0)
% 2.63/0.95      | sK0 != X0 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_254,plain,
% 2.63/0.95      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ l1_pre_topc(sK0) ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_253]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_258,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_254,c_17]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_259,plain,
% 2.63/0.95      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.63/0.95      inference(renaming,[status(thm)],[c_258]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1609,plain,
% 2.63/0.95      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.63/0.95      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_259]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_7,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.63/0.95      | ~ l1_pre_topc(X1) ),
% 2.63/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_325,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.95      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.63/0.95      | sK0 != X1 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_326,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_325]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1615,plain,
% 2.63/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_326]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_5,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.63/0.95      inference(cnf_transformation,[],[f35]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1627,plain,
% 2.63/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_5]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_15,negated_conjecture,
% 2.63/0.95      ( v2_tops_1(sK1,sK0)
% 2.63/0.95      | ~ v3_pre_topc(X0,sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ r1_tarski(X0,sK1)
% 2.63/0.95      | k1_xboole_0 = X0 ),
% 2.63/0.95      inference(cnf_transformation,[],[f45]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1649,plain,
% 2.63/0.95      ( v2_tops_1(sK1,sK0)
% 2.63/0.95      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.63/0.95      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.63/0.95      | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_15]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2,plain,
% 2.63/0.95      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.63/0.95      inference(cnf_transformation,[],[f33]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1679,plain,
% 2.63/0.95      ( r1_tarski(k1_tops_1(sK0,sK1),X0)
% 2.63/0.95      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.63/0.95      | ~ r1_tarski(sK1,X0) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1770,plain,
% 2.63/0.95      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 2.63/0.95      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.63/0.95      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_1679]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1044,plain,( X0 = X0 ),theory(equality) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1803,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_1044]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_4,plain,
% 2.63/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.63/0.95      inference(cnf_transformation,[],[f36]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1938,plain,
% 2.63/0.95      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_4]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1045,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1656,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) != X0
% 2.63/0.95      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.63/0.95      | k1_xboole_0 != X0 ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_1045]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2162,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 2.63/0.95      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.63/0.95      | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_1656]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2336,plain,
% 2.63/0.95      ( ~ v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.63/0.95      inference(predicate_to_equality_rev,[status(thm)],[c_2324]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2338,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_2324,c_16,c_1609,c_1615,c_1627,c_1649,c_1770,c_1803,
% 2.63/0.95                 c_1938,c_2162,c_2336]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2832,plain,
% 2.63/0.95      ( ~ v3_pre_topc(sK2,sK0)
% 2.63/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | ~ r1_tarski(sK2,X0)
% 2.63/0.95      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.63/0.95      inference(instantiation,[status(thm)],[c_305]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2836,plain,
% 2.63/0.95      ( v3_pre_topc(sK2,sK0) != iProver_top
% 2.63/0.95      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.63/0.95      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,X0) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_2832]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_2997,plain,
% 2.63/0.95      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,X0) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_1818,c_16,c_549,c_577,c_1609,c_1615,c_1627,c_1649,
% 2.63/0.95                 c_1770,c_1803,c_1938,c_2162,c_2336,c_2836]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_3008,plain,
% 2.63/0.95      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.63/0.95      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.63/0.95      inference(superposition,[status(thm)],[c_1480,c_2997]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_3011,plain,
% 2.63/0.95      ( r1_tarski(sK2,sK1) != iProver_top
% 2.63/0.95      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.63/0.95      inference(light_normalisation,[status(thm)],[c_3008,c_2338]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_13,negated_conjecture,
% 2.63/0.95      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.63/0.95      inference(cnf_transformation,[],[f47]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_558,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | r1_tarski(sK2,sK1)
% 2.63/0.95      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.63/0.95      | sK0 != sK0
% 2.63/0.95      | sK1 != X0 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_290]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_559,plain,
% 2.63/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | r1_tarski(sK2,sK1)
% 2.63/0.95      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_558]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_561,plain,
% 2.63/0.95      ( r1_tarski(sK2,sK1) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_559,c_16]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_563,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.63/0.95      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_3724,plain,
% 2.63/0.95      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_3011,c_16,c_563,c_1609,c_1615,c_1627,c_1649,c_1770,
% 2.63/0.95                 c_1803,c_1938,c_2162,c_2336]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_0,plain,
% 2.63/0.95      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.63/0.95      inference(cnf_transformation,[],[f32]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_1490,plain,
% 2.63/0.95      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.63/0.95      | r1_tarski(X0,X1) != iProver_top ),
% 2.63/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_3730,plain,
% 2.63/0.95      ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.63/0.95      inference(superposition,[status(thm)],[c_3724,c_1490]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_3,plain,
% 2.63/0.95      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.63/0.95      inference(cnf_transformation,[],[f34]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_4283,plain,
% 2.63/0.95      ( sK2 = k1_xboole_0 ),
% 2.63/0.95      inference(superposition,[status(thm)],[c_3730,c_3]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_11,negated_conjecture,
% 2.63/0.95      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.63/0.95      inference(cnf_transformation,[],[f49]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_586,plain,
% 2.63/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.63/0.95      | sK0 != sK0
% 2.63/0.95      | sK1 != X0
% 2.63/0.95      | sK2 != k1_xboole_0 ),
% 2.63/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_290]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_587,plain,
% 2.63/0.95      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.63/0.95      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.63/0.95      | sK2 != k1_xboole_0 ),
% 2.63/0.95      inference(unflattening,[status(thm)],[c_586]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(c_589,plain,
% 2.63/0.95      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.63/0.95      inference(global_propositional_subsumption,
% 2.63/0.95                [status(thm)],
% 2.63/0.95                [c_587,c_16]) ).
% 2.63/0.95  
% 2.63/0.95  cnf(contradiction,plain,
% 2.63/0.95      ( $false ),
% 2.63/0.95      inference(minisat,[status(thm)],[c_4283,c_2338,c_589]) ).
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/0.95  
% 2.63/0.95  ------                               Statistics
% 2.63/0.95  
% 2.63/0.95  ------ General
% 2.63/0.95  
% 2.63/0.95  abstr_ref_over_cycles:                  0
% 2.63/0.95  abstr_ref_under_cycles:                 0
% 2.63/0.95  gc_basic_clause_elim:                   0
% 2.63/0.95  forced_gc_time:                         0
% 2.63/0.95  parsing_time:                           0.009
% 2.63/0.95  unif_index_cands_time:                  0.
% 2.63/0.95  unif_index_add_time:                    0.
% 2.63/0.95  orderings_time:                         0.
% 2.63/0.95  out_proof_time:                         0.008
% 2.63/0.95  total_time:                             0.139
% 2.63/0.95  num_of_symbols:                         45
% 2.63/0.95  num_of_terms:                           2257
% 2.63/0.95  
% 2.63/0.95  ------ Preprocessing
% 2.63/0.95  
% 2.63/0.95  num_of_splits:                          0
% 2.63/0.95  num_of_split_atoms:                     0
% 2.63/0.95  num_of_reused_defs:                     0
% 2.63/0.95  num_eq_ax_congr_red:                    7
% 2.63/0.95  num_of_sem_filtered_clauses:            1
% 2.63/0.95  num_of_subtypes:                        0
% 2.63/0.95  monotx_restored_types:                  0
% 2.63/0.95  sat_num_of_epr_types:                   0
% 2.63/0.95  sat_num_of_non_cyclic_types:            0
% 2.63/0.95  sat_guarded_non_collapsed_types:        0
% 2.63/0.95  num_pure_diseq_elim:                    0
% 2.63/0.95  simp_replaced_by:                       0
% 2.63/0.95  res_preprocessed:                       91
% 2.63/0.95  prep_upred:                             0
% 2.63/0.95  prep_unflattend:                        23
% 2.63/0.95  smt_new_axioms:                         0
% 2.63/0.95  pred_elim_cands:                        4
% 2.63/0.95  pred_elim:                              2
% 2.63/0.95  pred_elim_cl:                           2
% 2.63/0.95  pred_elim_cycles:                       6
% 2.63/0.95  merged_defs:                            16
% 2.63/0.95  merged_defs_ncl:                        0
% 2.63/0.95  bin_hyper_res:                          16
% 2.63/0.95  prep_cycles:                            4
% 2.63/0.95  pred_elim_time:                         0.01
% 2.63/0.95  splitting_time:                         0.
% 2.63/0.95  sem_filter_time:                        0.
% 2.63/0.95  monotx_time:                            0.
% 2.63/0.95  subtype_inf_time:                       0.
% 2.63/0.95  
% 2.63/0.95  ------ Problem properties
% 2.63/0.95  
% 2.63/0.95  clauses:                                17
% 2.63/0.95  conjectures:                            6
% 2.63/0.95  epr:                                    4
% 2.63/0.95  horn:                                   16
% 2.63/0.95  ground:                                 5
% 2.63/0.95  unary:                                  2
% 2.63/0.95  binary:                                 10
% 2.63/0.95  lits:                                   41
% 2.63/0.95  lits_eq:                                7
% 2.63/0.95  fd_pure:                                0
% 2.63/0.95  fd_pseudo:                              0
% 2.63/0.95  fd_cond:                                1
% 2.63/0.95  fd_pseudo_cond:                         0
% 2.63/0.95  ac_symbols:                             0
% 2.63/0.95  
% 2.63/0.95  ------ Propositional Solver
% 2.63/0.95  
% 2.63/0.95  prop_solver_calls:                      27
% 2.63/0.95  prop_fast_solver_calls:                 739
% 2.63/0.95  smt_solver_calls:                       0
% 2.63/0.95  smt_fast_solver_calls:                  0
% 2.63/0.95  prop_num_of_clauses:                    1430
% 2.63/0.95  prop_preprocess_simplified:             4755
% 2.63/0.95  prop_fo_subsumed:                       30
% 2.63/0.95  prop_solver_time:                       0.
% 2.63/0.95  smt_solver_time:                        0.
% 2.63/0.95  smt_fast_solver_time:                   0.
% 2.63/0.95  prop_fast_solver_time:                  0.
% 2.63/0.95  prop_unsat_core_time:                   0.
% 2.63/0.95  
% 2.63/0.95  ------ QBF
% 2.63/0.95  
% 2.63/0.95  qbf_q_res:                              0
% 2.63/0.95  qbf_num_tautologies:                    0
% 2.63/0.95  qbf_prep_cycles:                        0
% 2.63/0.95  
% 2.63/0.95  ------ BMC1
% 2.63/0.95  
% 2.63/0.95  bmc1_current_bound:                     -1
% 2.63/0.95  bmc1_last_solved_bound:                 -1
% 2.63/0.95  bmc1_unsat_core_size:                   -1
% 2.63/0.95  bmc1_unsat_core_parents_size:           -1
% 2.63/0.95  bmc1_merge_next_fun:                    0
% 2.63/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.63/0.95  
% 2.63/0.95  ------ Instantiation
% 2.63/0.95  
% 2.63/0.95  inst_num_of_clauses:                    492
% 2.63/0.95  inst_num_in_passive:                    270
% 2.63/0.95  inst_num_in_active:                     222
% 2.63/0.95  inst_num_in_unprocessed:                0
% 2.63/0.95  inst_num_of_loops:                      240
% 2.63/0.95  inst_num_of_learning_restarts:          0
% 2.63/0.95  inst_num_moves_active_passive:          14
% 2.63/0.95  inst_lit_activity:                      0
% 2.63/0.95  inst_lit_activity_moves:                0
% 2.63/0.95  inst_num_tautologies:                   0
% 2.63/0.95  inst_num_prop_implied:                  0
% 2.63/0.95  inst_num_existing_simplified:           0
% 2.63/0.95  inst_num_eq_res_simplified:             0
% 2.63/0.95  inst_num_child_elim:                    0
% 2.63/0.95  inst_num_of_dismatching_blockings:      47
% 2.63/0.95  inst_num_of_non_proper_insts:           382
% 2.63/0.95  inst_num_of_duplicates:                 0
% 2.63/0.95  inst_inst_num_from_inst_to_res:         0
% 2.63/0.95  inst_dismatching_checking_time:         0.
% 2.63/0.95  
% 2.63/0.95  ------ Resolution
% 2.63/0.95  
% 2.63/0.95  res_num_of_clauses:                     0
% 2.63/0.95  res_num_in_passive:                     0
% 2.63/0.95  res_num_in_active:                      0
% 2.63/0.95  res_num_of_loops:                       95
% 2.63/0.95  res_forward_subset_subsumed:            27
% 2.63/0.95  res_backward_subset_subsumed:           0
% 2.63/0.95  res_forward_subsumed:                   0
% 2.63/0.95  res_backward_subsumed:                  0
% 2.63/0.95  res_forward_subsumption_resolution:     0
% 2.63/0.95  res_backward_subsumption_resolution:    0
% 2.63/0.95  res_clause_to_clause_subsumption:       260
% 2.63/0.95  res_orphan_elimination:                 0
% 2.63/0.95  res_tautology_del:                      76
% 2.63/0.95  res_num_eq_res_simplified:              0
% 2.63/0.95  res_num_sel_changes:                    0
% 2.63/0.95  res_moves_from_active_to_pass:          0
% 2.63/0.95  
% 2.63/0.95  ------ Superposition
% 2.63/0.95  
% 2.63/0.95  sup_time_total:                         0.
% 2.63/0.95  sup_time_generating:                    0.
% 2.63/0.95  sup_time_sim_full:                      0.
% 2.63/0.95  sup_time_sim_immed:                     0.
% 2.63/0.95  
% 2.63/0.95  sup_num_of_clauses:                     61
% 2.63/0.95  sup_num_in_active:                      45
% 2.63/0.95  sup_num_in_passive:                     16
% 2.63/0.95  sup_num_of_loops:                       46
% 2.63/0.95  sup_fw_superposition:                   26
% 2.63/0.95  sup_bw_superposition:                   33
% 2.63/0.95  sup_immediate_simplified:               3
% 2.63/0.95  sup_given_eliminated:                   1
% 2.63/0.95  comparisons_done:                       0
% 2.63/0.95  comparisons_avoided:                    0
% 2.63/0.95  
% 2.63/0.95  ------ Simplifications
% 2.63/0.95  
% 2.63/0.95  
% 2.63/0.95  sim_fw_subset_subsumed:                 0
% 2.63/0.95  sim_bw_subset_subsumed:                 1
% 2.63/0.95  sim_fw_subsumed:                        1
% 2.63/0.95  sim_bw_subsumed:                        0
% 2.63/0.95  sim_fw_subsumption_res:                 0
% 2.63/0.95  sim_bw_subsumption_res:                 0
% 2.63/0.95  sim_tautology_del:                      3
% 2.63/0.95  sim_eq_tautology_del:                   0
% 2.63/0.96  sim_eq_res_simp:                        0
% 2.63/0.96  sim_fw_demodulated:                     0
% 2.63/0.96  sim_bw_demodulated:                     3
% 2.63/0.96  sim_light_normalised:                   3
% 2.63/0.96  sim_joinable_taut:                      0
% 2.63/0.96  sim_joinable_simp:                      0
% 2.63/0.96  sim_ac_normalised:                      0
% 2.63/0.96  sim_smt_subsumption:                    0
% 2.63/0.96  
%------------------------------------------------------------------------------
