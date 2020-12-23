%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:13 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 940 expanded)
%              Number of clauses        :   79 ( 239 expanded)
%              Number of leaves         :   14 ( 235 expanded)
%              Depth                    :   22
%              Number of atoms          :  476 (7856 expanded)
%              Number of equality atoms :  134 (1337 expanded)
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1440,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1442,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_293,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_294,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_1436,plain,
    ( v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1809,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_1436])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_343,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_294])).

cnf(c_344,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_345,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_8,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_278,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_279,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_279])).

cnf(c_534,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_536,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_15])).

cnf(c_538,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1568,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1569,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_9,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_263,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_264,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_1438,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_2398,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1438])).

cnf(c_5,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_242,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_243,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_16])).

cnf(c_248,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_1565,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_1571,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1594,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1646,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1689,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1760,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_1024,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1774,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1861,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1025,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1653,plain,
    ( k1_tops_1(sK0,sK1) != X0
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_2073,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(X0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_2074,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2419,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2398])).

cnf(c_2572,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_15,c_1565,c_1571,c_1594,c_1646,c_1760,c_1774,c_1861,c_2074,c_2419])).

cnf(c_2913,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1809,c_15,c_20,c_345,c_538,c_1565,c_1569,c_1571,c_1594,c_1646,c_1760,c_1774,c_1861,c_2074,c_2419])).

cnf(c_2924,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_2913])).

cnf(c_2927,plain,
    ( r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2924,c_2572])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_279])).

cnf(c_548,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_550,plain,
    ( r1_tarski(sK2,sK1)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_15])).

cnf(c_552,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_3609,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2927,c_15,c_552,c_1565,c_1571,c_1594,c_1646,c_1760,c_1774,c_1861,c_2074,c_2419])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1449,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1450,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2424,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1450])).

cnf(c_3615,plain,
    ( r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_2424])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1448,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5012,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3615,c_1448])).

cnf(c_10,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_279])).

cnf(c_576,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_578,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5012,c_2572,c_578])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.19/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.03  
% 2.19/1.03  ------  iProver source info
% 2.19/1.03  
% 2.19/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.03  git: non_committed_changes: false
% 2.19/1.03  git: last_make_outside_of_git: false
% 2.19/1.03  
% 2.19/1.03  ------ 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options
% 2.19/1.03  
% 2.19/1.03  --out_options                           all
% 2.19/1.03  --tptp_safe_out                         true
% 2.19/1.03  --problem_path                          ""
% 2.19/1.03  --include_path                          ""
% 2.19/1.03  --clausifier                            res/vclausify_rel
% 2.19/1.03  --clausifier_options                    --mode clausify
% 2.19/1.03  --stdin                                 false
% 2.19/1.03  --stats_out                             all
% 2.19/1.03  
% 2.19/1.03  ------ General Options
% 2.19/1.03  
% 2.19/1.03  --fof                                   false
% 2.19/1.03  --time_out_real                         305.
% 2.19/1.03  --time_out_virtual                      -1.
% 2.19/1.03  --symbol_type_check                     false
% 2.19/1.03  --clausify_out                          false
% 2.19/1.03  --sig_cnt_out                           false
% 2.19/1.03  --trig_cnt_out                          false
% 2.19/1.03  --trig_cnt_out_tolerance                1.
% 2.19/1.03  --trig_cnt_out_sk_spl                   false
% 2.19/1.03  --abstr_cl_out                          false
% 2.19/1.03  
% 2.19/1.03  ------ Global Options
% 2.19/1.03  
% 2.19/1.03  --schedule                              default
% 2.19/1.03  --add_important_lit                     false
% 2.19/1.03  --prop_solver_per_cl                    1000
% 2.19/1.03  --min_unsat_core                        false
% 2.19/1.03  --soft_assumptions                      false
% 2.19/1.03  --soft_lemma_size                       3
% 2.19/1.03  --prop_impl_unit_size                   0
% 2.19/1.03  --prop_impl_unit                        []
% 2.19/1.03  --share_sel_clauses                     true
% 2.19/1.03  --reset_solvers                         false
% 2.19/1.03  --bc_imp_inh                            [conj_cone]
% 2.19/1.03  --conj_cone_tolerance                   3.
% 2.19/1.03  --extra_neg_conj                        none
% 2.19/1.03  --large_theory_mode                     true
% 2.19/1.03  --prolific_symb_bound                   200
% 2.19/1.03  --lt_threshold                          2000
% 2.19/1.03  --clause_weak_htbl                      true
% 2.19/1.03  --gc_record_bc_elim                     false
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing Options
% 2.19/1.03  
% 2.19/1.03  --preprocessing_flag                    true
% 2.19/1.03  --time_out_prep_mult                    0.1
% 2.19/1.03  --splitting_mode                        input
% 2.19/1.03  --splitting_grd                         true
% 2.19/1.03  --splitting_cvd                         false
% 2.19/1.03  --splitting_cvd_svl                     false
% 2.19/1.03  --splitting_nvd                         32
% 2.19/1.03  --sub_typing                            true
% 2.19/1.03  --prep_gs_sim                           true
% 2.19/1.03  --prep_unflatten                        true
% 2.19/1.03  --prep_res_sim                          true
% 2.19/1.03  --prep_upred                            true
% 2.19/1.03  --prep_sem_filter                       exhaustive
% 2.19/1.03  --prep_sem_filter_out                   false
% 2.19/1.03  --pred_elim                             true
% 2.19/1.03  --res_sim_input                         true
% 2.19/1.03  --eq_ax_congr_red                       true
% 2.19/1.03  --pure_diseq_elim                       true
% 2.19/1.03  --brand_transform                       false
% 2.19/1.03  --non_eq_to_eq                          false
% 2.19/1.03  --prep_def_merge                        true
% 2.19/1.03  --prep_def_merge_prop_impl              false
% 2.19/1.03  --prep_def_merge_mbd                    true
% 2.19/1.03  --prep_def_merge_tr_red                 false
% 2.19/1.03  --prep_def_merge_tr_cl                  false
% 2.19/1.03  --smt_preprocessing                     true
% 2.19/1.03  --smt_ac_axioms                         fast
% 2.19/1.03  --preprocessed_out                      false
% 2.19/1.03  --preprocessed_stats                    false
% 2.19/1.03  
% 2.19/1.03  ------ Abstraction refinement Options
% 2.19/1.03  
% 2.19/1.03  --abstr_ref                             []
% 2.19/1.03  --abstr_ref_prep                        false
% 2.19/1.03  --abstr_ref_until_sat                   false
% 2.19/1.03  --abstr_ref_sig_restrict                funpre
% 2.19/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.03  --abstr_ref_under                       []
% 2.19/1.03  
% 2.19/1.03  ------ SAT Options
% 2.19/1.03  
% 2.19/1.03  --sat_mode                              false
% 2.19/1.03  --sat_fm_restart_options                ""
% 2.19/1.03  --sat_gr_def                            false
% 2.19/1.03  --sat_epr_types                         true
% 2.19/1.03  --sat_non_cyclic_types                  false
% 2.19/1.03  --sat_finite_models                     false
% 2.19/1.03  --sat_fm_lemmas                         false
% 2.19/1.03  --sat_fm_prep                           false
% 2.19/1.03  --sat_fm_uc_incr                        true
% 2.19/1.03  --sat_out_model                         small
% 2.19/1.03  --sat_out_clauses                       false
% 2.19/1.03  
% 2.19/1.03  ------ QBF Options
% 2.19/1.03  
% 2.19/1.03  --qbf_mode                              false
% 2.19/1.03  --qbf_elim_univ                         false
% 2.19/1.03  --qbf_dom_inst                          none
% 2.19/1.03  --qbf_dom_pre_inst                      false
% 2.19/1.03  --qbf_sk_in                             false
% 2.19/1.03  --qbf_pred_elim                         true
% 2.19/1.03  --qbf_split                             512
% 2.19/1.03  
% 2.19/1.03  ------ BMC1 Options
% 2.19/1.03  
% 2.19/1.03  --bmc1_incremental                      false
% 2.19/1.03  --bmc1_axioms                           reachable_all
% 2.19/1.03  --bmc1_min_bound                        0
% 2.19/1.03  --bmc1_max_bound                        -1
% 2.19/1.03  --bmc1_max_bound_default                -1
% 2.19/1.03  --bmc1_symbol_reachability              true
% 2.19/1.03  --bmc1_property_lemmas                  false
% 2.19/1.03  --bmc1_k_induction                      false
% 2.19/1.03  --bmc1_non_equiv_states                 false
% 2.19/1.03  --bmc1_deadlock                         false
% 2.19/1.03  --bmc1_ucm                              false
% 2.19/1.03  --bmc1_add_unsat_core                   none
% 2.19/1.03  --bmc1_unsat_core_children              false
% 2.19/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.03  --bmc1_out_stat                         full
% 2.19/1.03  --bmc1_ground_init                      false
% 2.19/1.03  --bmc1_pre_inst_next_state              false
% 2.19/1.03  --bmc1_pre_inst_state                   false
% 2.19/1.03  --bmc1_pre_inst_reach_state             false
% 2.19/1.03  --bmc1_out_unsat_core                   false
% 2.19/1.03  --bmc1_aig_witness_out                  false
% 2.19/1.03  --bmc1_verbose                          false
% 2.19/1.03  --bmc1_dump_clauses_tptp                false
% 2.19/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.03  --bmc1_dump_file                        -
% 2.19/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.03  --bmc1_ucm_extend_mode                  1
% 2.19/1.03  --bmc1_ucm_init_mode                    2
% 2.19/1.03  --bmc1_ucm_cone_mode                    none
% 2.19/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.03  --bmc1_ucm_relax_model                  4
% 2.19/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.03  --bmc1_ucm_layered_model                none
% 2.19/1.03  --bmc1_ucm_max_lemma_size               10
% 2.19/1.03  
% 2.19/1.03  ------ AIG Options
% 2.19/1.03  
% 2.19/1.03  --aig_mode                              false
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation Options
% 2.19/1.03  
% 2.19/1.03  --instantiation_flag                    true
% 2.19/1.03  --inst_sos_flag                         false
% 2.19/1.03  --inst_sos_phase                        true
% 2.19/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel_side                     num_symb
% 2.19/1.03  --inst_solver_per_active                1400
% 2.19/1.03  --inst_solver_calls_frac                1.
% 2.19/1.03  --inst_passive_queue_type               priority_queues
% 2.19/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.03  --inst_passive_queues_freq              [25;2]
% 2.19/1.03  --inst_dismatching                      true
% 2.19/1.03  --inst_eager_unprocessed_to_passive     true
% 2.19/1.03  --inst_prop_sim_given                   true
% 2.19/1.03  --inst_prop_sim_new                     false
% 2.19/1.03  --inst_subs_new                         false
% 2.19/1.03  --inst_eq_res_simp                      false
% 2.19/1.03  --inst_subs_given                       false
% 2.19/1.03  --inst_orphan_elimination               true
% 2.19/1.03  --inst_learning_loop_flag               true
% 2.19/1.03  --inst_learning_start                   3000
% 2.19/1.03  --inst_learning_factor                  2
% 2.19/1.03  --inst_start_prop_sim_after_learn       3
% 2.19/1.03  --inst_sel_renew                        solver
% 2.19/1.03  --inst_lit_activity_flag                true
% 2.19/1.03  --inst_restr_to_given                   false
% 2.19/1.03  --inst_activity_threshold               500
% 2.19/1.03  --inst_out_proof                        true
% 2.19/1.03  
% 2.19/1.03  ------ Resolution Options
% 2.19/1.03  
% 2.19/1.03  --resolution_flag                       true
% 2.19/1.03  --res_lit_sel                           adaptive
% 2.19/1.03  --res_lit_sel_side                      none
% 2.19/1.03  --res_ordering                          kbo
% 2.19/1.03  --res_to_prop_solver                    active
% 2.19/1.03  --res_prop_simpl_new                    false
% 2.19/1.03  --res_prop_simpl_given                  true
% 2.19/1.03  --res_passive_queue_type                priority_queues
% 2.19/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.03  --res_passive_queues_freq               [15;5]
% 2.19/1.03  --res_forward_subs                      full
% 2.19/1.03  --res_backward_subs                     full
% 2.19/1.03  --res_forward_subs_resolution           true
% 2.19/1.03  --res_backward_subs_resolution          true
% 2.19/1.03  --res_orphan_elimination                true
% 2.19/1.03  --res_time_limit                        2.
% 2.19/1.03  --res_out_proof                         true
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Options
% 2.19/1.03  
% 2.19/1.03  --superposition_flag                    true
% 2.19/1.03  --sup_passive_queue_type                priority_queues
% 2.19/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.03  --demod_completeness_check              fast
% 2.19/1.03  --demod_use_ground                      true
% 2.19/1.03  --sup_to_prop_solver                    passive
% 2.19/1.03  --sup_prop_simpl_new                    true
% 2.19/1.03  --sup_prop_simpl_given                  true
% 2.19/1.03  --sup_fun_splitting                     false
% 2.19/1.03  --sup_smt_interval                      50000
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Simplification Setup
% 2.19/1.03  
% 2.19/1.03  --sup_indices_passive                   []
% 2.19/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_full_bw                           [BwDemod]
% 2.19/1.03  --sup_immed_triv                        [TrivRules]
% 2.19/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_immed_bw_main                     []
% 2.19/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  
% 2.19/1.03  ------ Combination Options
% 2.19/1.03  
% 2.19/1.03  --comb_res_mult                         3
% 2.19/1.03  --comb_sup_mult                         2
% 2.19/1.03  --comb_inst_mult                        10
% 2.19/1.03  
% 2.19/1.03  ------ Debug Options
% 2.19/1.03  
% 2.19/1.03  --dbg_backtrace                         false
% 2.19/1.03  --dbg_dump_prop_clauses                 false
% 2.19/1.03  --dbg_dump_prop_clauses_file            -
% 2.19/1.03  --dbg_out_stat                          false
% 2.19/1.03  ------ Parsing...
% 2.19/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.03  ------ Proving...
% 2.19/1.03  ------ Problem Properties 
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  clauses                                 16
% 2.19/1.03  conjectures                             6
% 2.19/1.03  EPR                                     5
% 2.19/1.03  Horn                                    15
% 2.19/1.03  unary                                   2
% 2.19/1.03  binary                                  9
% 2.19/1.03  lits                                    39
% 2.19/1.03  lits eq                                 5
% 2.19/1.03  fd_pure                                 0
% 2.19/1.03  fd_pseudo                               0
% 2.19/1.03  fd_cond                                 2
% 2.19/1.03  fd_pseudo_cond                          0
% 2.19/1.03  AC symbols                              0
% 2.19/1.03  
% 2.19/1.03  ------ Schedule dynamic 5 is on 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  ------ 
% 2.19/1.03  Current options:
% 2.19/1.03  ------ 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options
% 2.19/1.03  
% 2.19/1.03  --out_options                           all
% 2.19/1.03  --tptp_safe_out                         true
% 2.19/1.03  --problem_path                          ""
% 2.19/1.03  --include_path                          ""
% 2.19/1.03  --clausifier                            res/vclausify_rel
% 2.19/1.03  --clausifier_options                    --mode clausify
% 2.19/1.03  --stdin                                 false
% 2.19/1.03  --stats_out                             all
% 2.19/1.03  
% 2.19/1.03  ------ General Options
% 2.19/1.03  
% 2.19/1.03  --fof                                   false
% 2.19/1.03  --time_out_real                         305.
% 2.19/1.03  --time_out_virtual                      -1.
% 2.19/1.03  --symbol_type_check                     false
% 2.19/1.03  --clausify_out                          false
% 2.19/1.03  --sig_cnt_out                           false
% 2.19/1.03  --trig_cnt_out                          false
% 2.19/1.03  --trig_cnt_out_tolerance                1.
% 2.19/1.03  --trig_cnt_out_sk_spl                   false
% 2.19/1.03  --abstr_cl_out                          false
% 2.19/1.03  
% 2.19/1.03  ------ Global Options
% 2.19/1.03  
% 2.19/1.03  --schedule                              default
% 2.19/1.03  --add_important_lit                     false
% 2.19/1.03  --prop_solver_per_cl                    1000
% 2.19/1.03  --min_unsat_core                        false
% 2.19/1.03  --soft_assumptions                      false
% 2.19/1.03  --soft_lemma_size                       3
% 2.19/1.03  --prop_impl_unit_size                   0
% 2.19/1.03  --prop_impl_unit                        []
% 2.19/1.03  --share_sel_clauses                     true
% 2.19/1.03  --reset_solvers                         false
% 2.19/1.03  --bc_imp_inh                            [conj_cone]
% 2.19/1.03  --conj_cone_tolerance                   3.
% 2.19/1.03  --extra_neg_conj                        none
% 2.19/1.03  --large_theory_mode                     true
% 2.19/1.03  --prolific_symb_bound                   200
% 2.19/1.03  --lt_threshold                          2000
% 2.19/1.03  --clause_weak_htbl                      true
% 2.19/1.03  --gc_record_bc_elim                     false
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing Options
% 2.19/1.03  
% 2.19/1.03  --preprocessing_flag                    true
% 2.19/1.03  --time_out_prep_mult                    0.1
% 2.19/1.03  --splitting_mode                        input
% 2.19/1.03  --splitting_grd                         true
% 2.19/1.03  --splitting_cvd                         false
% 2.19/1.03  --splitting_cvd_svl                     false
% 2.19/1.03  --splitting_nvd                         32
% 2.19/1.03  --sub_typing                            true
% 2.19/1.03  --prep_gs_sim                           true
% 2.19/1.03  --prep_unflatten                        true
% 2.19/1.03  --prep_res_sim                          true
% 2.19/1.03  --prep_upred                            true
% 2.19/1.03  --prep_sem_filter                       exhaustive
% 2.19/1.03  --prep_sem_filter_out                   false
% 2.19/1.03  --pred_elim                             true
% 2.19/1.03  --res_sim_input                         true
% 2.19/1.03  --eq_ax_congr_red                       true
% 2.19/1.03  --pure_diseq_elim                       true
% 2.19/1.03  --brand_transform                       false
% 2.19/1.03  --non_eq_to_eq                          false
% 2.19/1.03  --prep_def_merge                        true
% 2.19/1.03  --prep_def_merge_prop_impl              false
% 2.19/1.03  --prep_def_merge_mbd                    true
% 2.19/1.03  --prep_def_merge_tr_red                 false
% 2.19/1.03  --prep_def_merge_tr_cl                  false
% 2.19/1.03  --smt_preprocessing                     true
% 2.19/1.03  --smt_ac_axioms                         fast
% 2.19/1.03  --preprocessed_out                      false
% 2.19/1.03  --preprocessed_stats                    false
% 2.19/1.03  
% 2.19/1.03  ------ Abstraction refinement Options
% 2.19/1.03  
% 2.19/1.03  --abstr_ref                             []
% 2.19/1.03  --abstr_ref_prep                        false
% 2.19/1.03  --abstr_ref_until_sat                   false
% 2.19/1.03  --abstr_ref_sig_restrict                funpre
% 2.19/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.03  --abstr_ref_under                       []
% 2.19/1.03  
% 2.19/1.03  ------ SAT Options
% 2.19/1.03  
% 2.19/1.03  --sat_mode                              false
% 2.19/1.03  --sat_fm_restart_options                ""
% 2.19/1.03  --sat_gr_def                            false
% 2.19/1.03  --sat_epr_types                         true
% 2.19/1.03  --sat_non_cyclic_types                  false
% 2.19/1.03  --sat_finite_models                     false
% 2.19/1.03  --sat_fm_lemmas                         false
% 2.19/1.03  --sat_fm_prep                           false
% 2.19/1.03  --sat_fm_uc_incr                        true
% 2.19/1.03  --sat_out_model                         small
% 2.19/1.03  --sat_out_clauses                       false
% 2.19/1.03  
% 2.19/1.03  ------ QBF Options
% 2.19/1.03  
% 2.19/1.03  --qbf_mode                              false
% 2.19/1.03  --qbf_elim_univ                         false
% 2.19/1.03  --qbf_dom_inst                          none
% 2.19/1.03  --qbf_dom_pre_inst                      false
% 2.19/1.03  --qbf_sk_in                             false
% 2.19/1.03  --qbf_pred_elim                         true
% 2.19/1.03  --qbf_split                             512
% 2.19/1.03  
% 2.19/1.03  ------ BMC1 Options
% 2.19/1.03  
% 2.19/1.03  --bmc1_incremental                      false
% 2.19/1.03  --bmc1_axioms                           reachable_all
% 2.19/1.03  --bmc1_min_bound                        0
% 2.19/1.03  --bmc1_max_bound                        -1
% 2.19/1.03  --bmc1_max_bound_default                -1
% 2.19/1.03  --bmc1_symbol_reachability              true
% 2.19/1.03  --bmc1_property_lemmas                  false
% 2.19/1.03  --bmc1_k_induction                      false
% 2.19/1.03  --bmc1_non_equiv_states                 false
% 2.19/1.03  --bmc1_deadlock                         false
% 2.19/1.03  --bmc1_ucm                              false
% 2.19/1.03  --bmc1_add_unsat_core                   none
% 2.19/1.03  --bmc1_unsat_core_children              false
% 2.19/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.03  --bmc1_out_stat                         full
% 2.19/1.03  --bmc1_ground_init                      false
% 2.19/1.03  --bmc1_pre_inst_next_state              false
% 2.19/1.03  --bmc1_pre_inst_state                   false
% 2.19/1.03  --bmc1_pre_inst_reach_state             false
% 2.19/1.03  --bmc1_out_unsat_core                   false
% 2.19/1.03  --bmc1_aig_witness_out                  false
% 2.19/1.03  --bmc1_verbose                          false
% 2.19/1.03  --bmc1_dump_clauses_tptp                false
% 2.19/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.03  --bmc1_dump_file                        -
% 2.19/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.03  --bmc1_ucm_extend_mode                  1
% 2.19/1.03  --bmc1_ucm_init_mode                    2
% 2.19/1.03  --bmc1_ucm_cone_mode                    none
% 2.19/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.03  --bmc1_ucm_relax_model                  4
% 2.19/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.03  --bmc1_ucm_layered_model                none
% 2.19/1.03  --bmc1_ucm_max_lemma_size               10
% 2.19/1.03  
% 2.19/1.03  ------ AIG Options
% 2.19/1.03  
% 2.19/1.03  --aig_mode                              false
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation Options
% 2.19/1.03  
% 2.19/1.03  --instantiation_flag                    true
% 2.19/1.03  --inst_sos_flag                         false
% 2.19/1.03  --inst_sos_phase                        true
% 2.19/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel_side                     none
% 2.19/1.03  --inst_solver_per_active                1400
% 2.19/1.03  --inst_solver_calls_frac                1.
% 2.19/1.03  --inst_passive_queue_type               priority_queues
% 2.19/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.03  --inst_passive_queues_freq              [25;2]
% 2.19/1.03  --inst_dismatching                      true
% 2.19/1.03  --inst_eager_unprocessed_to_passive     true
% 2.19/1.03  --inst_prop_sim_given                   true
% 2.19/1.03  --inst_prop_sim_new                     false
% 2.19/1.03  --inst_subs_new                         false
% 2.19/1.03  --inst_eq_res_simp                      false
% 2.19/1.03  --inst_subs_given                       false
% 2.19/1.03  --inst_orphan_elimination               true
% 2.19/1.03  --inst_learning_loop_flag               true
% 2.19/1.03  --inst_learning_start                   3000
% 2.19/1.03  --inst_learning_factor                  2
% 2.19/1.03  --inst_start_prop_sim_after_learn       3
% 2.19/1.03  --inst_sel_renew                        solver
% 2.19/1.03  --inst_lit_activity_flag                true
% 2.19/1.03  --inst_restr_to_given                   false
% 2.19/1.03  --inst_activity_threshold               500
% 2.19/1.03  --inst_out_proof                        true
% 2.19/1.03  
% 2.19/1.03  ------ Resolution Options
% 2.19/1.03  
% 2.19/1.03  --resolution_flag                       false
% 2.19/1.03  --res_lit_sel                           adaptive
% 2.19/1.03  --res_lit_sel_side                      none
% 2.19/1.03  --res_ordering                          kbo
% 2.19/1.03  --res_to_prop_solver                    active
% 2.19/1.03  --res_prop_simpl_new                    false
% 2.19/1.03  --res_prop_simpl_given                  true
% 2.19/1.03  --res_passive_queue_type                priority_queues
% 2.19/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.03  --res_passive_queues_freq               [15;5]
% 2.19/1.03  --res_forward_subs                      full
% 2.19/1.03  --res_backward_subs                     full
% 2.19/1.03  --res_forward_subs_resolution           true
% 2.19/1.03  --res_backward_subs_resolution          true
% 2.19/1.03  --res_orphan_elimination                true
% 2.19/1.03  --res_time_limit                        2.
% 2.19/1.03  --res_out_proof                         true
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Options
% 2.19/1.03  
% 2.19/1.03  --superposition_flag                    true
% 2.19/1.03  --sup_passive_queue_type                priority_queues
% 2.19/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.03  --demod_completeness_check              fast
% 2.19/1.03  --demod_use_ground                      true
% 2.19/1.03  --sup_to_prop_solver                    passive
% 2.19/1.03  --sup_prop_simpl_new                    true
% 2.19/1.03  --sup_prop_simpl_given                  true
% 2.19/1.03  --sup_fun_splitting                     false
% 2.19/1.03  --sup_smt_interval                      50000
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Simplification Setup
% 2.19/1.03  
% 2.19/1.03  --sup_indices_passive                   []
% 2.19/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_full_bw                           [BwDemod]
% 2.19/1.03  --sup_immed_triv                        [TrivRules]
% 2.19/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_immed_bw_main                     []
% 2.19/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  
% 2.19/1.03  ------ Combination Options
% 2.19/1.03  
% 2.19/1.03  --comb_res_mult                         3
% 2.19/1.03  --comb_sup_mult                         2
% 2.19/1.03  --comb_inst_mult                        10
% 2.19/1.03  
% 2.19/1.03  ------ Debug Options
% 2.19/1.03  
% 2.19/1.03  --dbg_backtrace                         false
% 2.19/1.03  --dbg_dump_prop_clauses                 false
% 2.19/1.03  --dbg_dump_prop_clauses_file            -
% 2.19/1.03  --dbg_out_stat                          false
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  ------ Proving...
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  % SZS status Theorem for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  fof(f9,conjecture,(
% 2.19/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f10,negated_conjecture,(
% 2.19/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.19/1.03    inference(negated_conjecture,[],[f9])).
% 2.19/1.03  
% 2.19/1.03  fof(f20,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f10])).
% 2.19/1.03  
% 2.19/1.03  fof(f21,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/1.03    inference(flattening,[],[f20])).
% 2.19/1.03  
% 2.19/1.03  fof(f24,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/1.03    inference(nnf_transformation,[],[f21])).
% 2.19/1.03  
% 2.19/1.03  fof(f25,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/1.03    inference(flattening,[],[f24])).
% 2.19/1.03  
% 2.19/1.03  fof(f26,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/1.03    inference(rectify,[],[f25])).
% 2.19/1.03  
% 2.19/1.03  fof(f29,plain,(
% 2.19/1.03    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,X0) & r1_tarski(sK2,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f28,plain,(
% 2.19/1.03    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f27,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f30,plain,(
% 2.19/1.03    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.19/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 2.19/1.03  
% 2.19/1.03  fof(f43,plain,(
% 2.19/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f45,plain,(
% 2.19/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f7,axiom,(
% 2.19/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f17,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/1.03    inference(ennf_transformation,[],[f7])).
% 2.19/1.03  
% 2.19/1.03  fof(f18,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/1.03    inference(flattening,[],[f17])).
% 2.19/1.03  
% 2.19/1.03  fof(f38,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f18])).
% 2.19/1.03  
% 2.19/1.03  fof(f42,plain,(
% 2.19/1.03    l1_pre_topc(sK0)),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f47,plain,(
% 2.19/1.03    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f8,axiom,(
% 2.19/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f19,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/1.03    inference(ennf_transformation,[],[f8])).
% 2.19/1.03  
% 2.19/1.03  fof(f23,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/1.03    inference(nnf_transformation,[],[f19])).
% 2.19/1.03  
% 2.19/1.03  fof(f40,plain,(
% 2.19/1.03    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f23])).
% 2.19/1.03  
% 2.19/1.03  fof(f39,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f23])).
% 2.19/1.03  
% 2.19/1.03  fof(f5,axiom,(
% 2.19/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f14,plain,(
% 2.19/1.03    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f5])).
% 2.19/1.03  
% 2.19/1.03  fof(f15,plain,(
% 2.19/1.03    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.19/1.03    inference(flattening,[],[f14])).
% 2.19/1.03  
% 2.19/1.03  fof(f36,plain,(
% 2.19/1.03    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f15])).
% 2.19/1.03  
% 2.19/1.03  fof(f41,plain,(
% 2.19/1.03    v2_pre_topc(sK0)),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f6,axiom,(
% 2.19/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f16,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/1.03    inference(ennf_transformation,[],[f6])).
% 2.19/1.03  
% 2.19/1.03  fof(f37,plain,(
% 2.19/1.03    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f16])).
% 2.19/1.03  
% 2.19/1.03  fof(f4,axiom,(
% 2.19/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f22,plain,(
% 2.19/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.19/1.03    inference(nnf_transformation,[],[f4])).
% 2.19/1.03  
% 2.19/1.03  fof(f34,plain,(
% 2.19/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f22])).
% 2.19/1.03  
% 2.19/1.03  fof(f44,plain,(
% 2.19/1.03    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f1,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f11,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.19/1.03    inference(ennf_transformation,[],[f1])).
% 2.19/1.03  
% 2.19/1.03  fof(f12,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.19/1.03    inference(flattening,[],[f11])).
% 2.19/1.03  
% 2.19/1.03  fof(f31,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f12])).
% 2.19/1.03  
% 2.19/1.03  fof(f35,plain,(
% 2.19/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f22])).
% 2.19/1.03  
% 2.19/1.03  fof(f46,plain,(
% 2.19/1.03    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f2,axiom,(
% 2.19/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f32,plain,(
% 2.19/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f2])).
% 2.19/1.03  
% 2.19/1.03  fof(f3,axiom,(
% 2.19/1.03    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f13,plain,(
% 2.19/1.03    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f3])).
% 2.19/1.03  
% 2.19/1.03  fof(f33,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f13])).
% 2.19/1.03  
% 2.19/1.03  fof(f48,plain,(
% 2.19/1.03    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 2.19/1.03    inference(cnf_transformation,[],[f30])).
% 2.19/1.03  
% 2.19/1.03  cnf(c_15,negated_conjecture,
% 2.19/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.19/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1440,plain,
% 2.19/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_13,negated_conjecture,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0)
% 2.19/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.19/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1442,plain,
% 2.19/1.03      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.19/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_7,plain,
% 2.19/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | ~ r1_tarski(X0,X2)
% 2.19/1.03      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.19/1.03      | ~ l1_pre_topc(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_16,negated_conjecture,
% 2.19/1.03      ( l1_pre_topc(sK0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_293,plain,
% 2.19/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | ~ r1_tarski(X0,X2)
% 2.19/1.03      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.19/1.03      | sK0 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_294,plain,
% 2.19/1.03      ( ~ v3_pre_topc(X0,sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ r1_tarski(X0,X1)
% 2.19/1.03      | r1_tarski(X0,k1_tops_1(sK0,X1)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_293]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1436,plain,
% 2.19/1.03      ( v3_pre_topc(X0,sK0) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.19/1.03      | r1_tarski(X0,X1) != iProver_top
% 2.19/1.03      | r1_tarski(X0,k1_tops_1(sK0,X1)) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1809,plain,
% 2.19/1.03      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.19/1.03      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,X0) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1442,c_1436]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_20,plain,
% 2.19/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_11,negated_conjecture,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_343,plain,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ r1_tarski(X0,X1)
% 2.19/1.03      | r1_tarski(X0,k1_tops_1(sK0,X1))
% 2.19/1.03      | sK0 != sK0
% 2.19/1.03      | sK2 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_294]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_344,plain,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ r1_tarski(sK2,X0)
% 2.19/1.03      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_343]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_345,plain,
% 2.19/1.03      ( v2_tops_1(sK1,sK0) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.19/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,X0) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_8,plain,
% 2.19/1.03      ( v2_tops_1(X0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | ~ l1_pre_topc(X1)
% 2.19/1.03      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_278,plain,
% 2.19/1.03      ( v2_tops_1(X0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.19/1.03      | sK0 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_279,plain,
% 2.19/1.03      ( v2_tops_1(X0,sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_278]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_533,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.19/1.03      | sK0 != sK0
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_279]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_534,plain,
% 2.19/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_533]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_536,plain,
% 2.19/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_534,c_15]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_538,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.19/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1568,plain,
% 2.19/1.03      ( v2_tops_1(sK1,sK0)
% 2.19/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_279]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1569,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.19/1.03      | v2_tops_1(sK1,sK0) = iProver_top
% 2.19/1.03      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_9,plain,
% 2.19/1.03      ( ~ v2_tops_1(X0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | ~ l1_pre_topc(X1)
% 2.19/1.03      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_263,plain,
% 2.19/1.03      ( ~ v2_tops_1(X0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.19/1.03      | sK0 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_264,plain,
% 2.19/1.03      ( ~ v2_tops_1(X0,sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_263]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1438,plain,
% 2.19/1.03      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.19/1.03      | v2_tops_1(X0,sK0) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2398,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.19/1.03      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1440,c_1438]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5,plain,
% 2.19/1.03      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.19/1.03      | ~ v2_pre_topc(X0)
% 2.19/1.03      | ~ l1_pre_topc(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_17,negated_conjecture,
% 2.19/1.03      ( v2_pre_topc(sK0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_242,plain,
% 2.19/1.03      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.19/1.03      | ~ l1_pre_topc(X0)
% 2.19/1.03      | sK0 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_243,plain,
% 2.19/1.03      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ l1_pre_topc(sK0) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_242]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_247,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_243,c_16]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_248,plain,
% 2.19/1.03      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_247]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1565,plain,
% 2.19/1.03      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.19/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_248]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_6,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.19/1.03      | ~ l1_pre_topc(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_314,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.19/1.03      | sK0 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_315,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_314]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1571,plain,
% 2.19/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_315]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_4,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1594,plain,
% 2.19/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_14,negated_conjecture,
% 2.19/1.03      ( v2_tops_1(sK1,sK0)
% 2.19/1.03      | ~ v3_pre_topc(X0,sK0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ r1_tarski(X0,sK1)
% 2.19/1.03      | k1_xboole_0 = X0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1646,plain,
% 2.19/1.03      ( v2_tops_1(sK1,sK0)
% 2.19/1.03      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 2.19/1.03      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.19/1.03      | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_0,plain,
% 2.19/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f31]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1689,plain,
% 2.19/1.03      ( r1_tarski(X0,u1_struct_0(sK0))
% 2.19/1.03      | ~ r1_tarski(X0,sK1)
% 2.19/1.03      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1760,plain,
% 2.19/1.03      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 2.19/1.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 2.19/1.03      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1689]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1024,plain,( X0 = X0 ),theory(equality) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1774,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1024]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3,plain,
% 2.19/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1861,plain,
% 2.19/1.03      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1025,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1653,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != X0
% 2.19/1.03      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.19/1.03      | k1_xboole_0 != X0 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1025]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2073,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != k1_tops_1(X0,sK1)
% 2.19/1.03      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.19/1.03      | k1_xboole_0 != k1_tops_1(X0,sK1) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1653]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2074,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 2.19/1.03      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.19/1.03      | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_2073]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2419,plain,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.19/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2398]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2572,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_2398,c_15,c_1565,c_1571,c_1594,c_1646,c_1760,c_1774,
% 2.19/1.03                 c_1861,c_2074,c_2419]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2913,plain,
% 2.19/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,X0) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,k1_tops_1(sK0,X0)) = iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1809,c_15,c_20,c_345,c_538,c_1565,c_1569,c_1571,
% 2.19/1.03                 c_1594,c_1646,c_1760,c_1774,c_1861,c_2074,c_2419]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2924,plain,
% 2.19/1.03      ( r1_tarski(sK2,k1_tops_1(sK0,sK1)) = iProver_top
% 2.19/1.03      | r1_tarski(sK2,sK1) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1440,c_2913]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2927,plain,
% 2.19/1.03      ( r1_tarski(sK2,sK1) != iProver_top
% 2.19/1.03      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.19/1.03      inference(light_normalisation,[status(thm)],[c_2924,c_2572]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_12,negated_conjecture,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_547,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | r1_tarski(sK2,sK1)
% 2.19/1.03      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.19/1.03      | sK0 != sK0
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_279]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_548,plain,
% 2.19/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | r1_tarski(sK2,sK1)
% 2.19/1.03      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_547]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_550,plain,
% 2.19/1.03      ( r1_tarski(sK2,sK1) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_548,c_15]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_552,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.19/1.03      | r1_tarski(sK2,sK1) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3609,plain,
% 2.19/1.03      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_2927,c_15,c_552,c_1565,c_1571,c_1594,c_1646,c_1760,
% 2.19/1.03                 c_1774,c_1861,c_2074,c_2419]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1,plain,
% 2.19/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1449,plain,
% 2.19/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1450,plain,
% 2.19/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.19/1.03      | r1_tarski(X2,X0) != iProver_top
% 2.19/1.03      | r1_tarski(X2,X1) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2424,plain,
% 2.19/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.19/1.03      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1449,c_1450]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3615,plain,
% 2.19/1.03      ( r1_tarski(sK2,X0) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_3609,c_2424]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2,plain,
% 2.19/1.03      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1448,plain,
% 2.19/1.03      ( k1_xboole_0 = X0
% 2.19/1.03      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5012,plain,
% 2.19/1.03      ( sK2 = k1_xboole_0 ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_3615,c_1448]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_10,negated_conjecture,
% 2.19/1.03      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2 ),
% 2.19/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_575,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,X0) != k1_xboole_0
% 2.19/1.03      | sK0 != sK0
% 2.19/1.03      | sK1 != X0
% 2.19/1.03      | sK2 != k1_xboole_0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_279]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_576,plain,
% 2.19/1.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.19/1.03      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 2.19/1.03      | sK2 != k1_xboole_0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_575]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_578,plain,
% 2.19/1.03      ( k1_tops_1(sK0,sK1) != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_576,c_15]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(contradiction,plain,
% 2.19/1.03      ( $false ),
% 2.19/1.03      inference(minisat,[status(thm)],[c_5012,c_2572,c_578]) ).
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  ------                               Statistics
% 2.19/1.03  
% 2.19/1.03  ------ General
% 2.19/1.03  
% 2.19/1.03  abstr_ref_over_cycles:                  0
% 2.19/1.03  abstr_ref_under_cycles:                 0
% 2.19/1.03  gc_basic_clause_elim:                   0
% 2.19/1.03  forced_gc_time:                         0
% 2.19/1.03  parsing_time:                           0.015
% 2.19/1.03  unif_index_cands_time:                  0.
% 2.19/1.03  unif_index_add_time:                    0.
% 2.19/1.03  orderings_time:                         0.
% 2.19/1.03  out_proof_time:                         0.008
% 2.19/1.03  total_time:                             0.181
% 2.19/1.03  num_of_symbols:                         45
% 2.19/1.03  num_of_terms:                           2251
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing
% 2.19/1.03  
% 2.19/1.03  num_of_splits:                          0
% 2.19/1.03  num_of_split_atoms:                     0
% 2.19/1.03  num_of_reused_defs:                     0
% 2.19/1.03  num_eq_ax_congr_red:                    10
% 2.19/1.03  num_of_sem_filtered_clauses:            1
% 2.19/1.03  num_of_subtypes:                        0
% 2.19/1.03  monotx_restored_types:                  0
% 2.19/1.03  sat_num_of_epr_types:                   0
% 2.19/1.03  sat_num_of_non_cyclic_types:            0
% 2.19/1.03  sat_guarded_non_collapsed_types:        0
% 2.19/1.03  num_pure_diseq_elim:                    0
% 2.19/1.03  simp_replaced_by:                       0
% 2.19/1.03  res_preprocessed:                       85
% 2.19/1.03  prep_upred:                             0
% 2.19/1.03  prep_unflattend:                        23
% 2.19/1.03  smt_new_axioms:                         0
% 2.19/1.03  pred_elim_cands:                        4
% 2.19/1.03  pred_elim:                              2
% 2.19/1.03  pred_elim_cl:                           2
% 2.19/1.03  pred_elim_cycles:                       6
% 2.19/1.03  merged_defs:                            8
% 2.19/1.03  merged_defs_ncl:                        0
% 2.19/1.03  bin_hyper_res:                          8
% 2.19/1.03  prep_cycles:                            4
% 2.19/1.03  pred_elim_time:                         0.021
% 2.19/1.03  splitting_time:                         0.
% 2.19/1.03  sem_filter_time:                        0.
% 2.19/1.03  monotx_time:                            0.
% 2.19/1.03  subtype_inf_time:                       0.
% 2.19/1.03  
% 2.19/1.03  ------ Problem properties
% 2.19/1.03  
% 2.19/1.03  clauses:                                16
% 2.19/1.03  conjectures:                            6
% 2.19/1.03  epr:                                    5
% 2.19/1.03  horn:                                   15
% 2.19/1.03  ground:                                 5
% 2.19/1.03  unary:                                  2
% 2.19/1.03  binary:                                 9
% 2.19/1.03  lits:                                   39
% 2.19/1.03  lits_eq:                                5
% 2.19/1.03  fd_pure:                                0
% 2.19/1.03  fd_pseudo:                              0
% 2.19/1.03  fd_cond:                                2
% 2.19/1.03  fd_pseudo_cond:                         0
% 2.19/1.03  ac_symbols:                             0
% 2.19/1.03  
% 2.19/1.03  ------ Propositional Solver
% 2.19/1.03  
% 2.19/1.03  prop_solver_calls:                      30
% 2.19/1.03  prop_fast_solver_calls:                 785
% 2.19/1.03  smt_solver_calls:                       0
% 2.19/1.03  smt_fast_solver_calls:                  0
% 2.19/1.03  prop_num_of_clauses:                    1459
% 2.19/1.03  prop_preprocess_simplified:             4810
% 2.19/1.03  prop_fo_subsumed:                       37
% 2.19/1.03  prop_solver_time:                       0.
% 2.19/1.03  smt_solver_time:                        0.
% 2.19/1.03  smt_fast_solver_time:                   0.
% 2.19/1.03  prop_fast_solver_time:                  0.
% 2.19/1.03  prop_unsat_core_time:                   0.
% 2.19/1.03  
% 2.19/1.03  ------ QBF
% 2.19/1.03  
% 2.19/1.03  qbf_q_res:                              0
% 2.19/1.03  qbf_num_tautologies:                    0
% 2.19/1.03  qbf_prep_cycles:                        0
% 2.19/1.03  
% 2.19/1.03  ------ BMC1
% 2.19/1.03  
% 2.19/1.03  bmc1_current_bound:                     -1
% 2.19/1.03  bmc1_last_solved_bound:                 -1
% 2.19/1.03  bmc1_unsat_core_size:                   -1
% 2.19/1.03  bmc1_unsat_core_parents_size:           -1
% 2.19/1.03  bmc1_merge_next_fun:                    0
% 2.19/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation
% 2.19/1.03  
% 2.19/1.03  inst_num_of_clauses:                    480
% 2.19/1.03  inst_num_in_passive:                    153
% 2.19/1.03  inst_num_in_active:                     290
% 2.19/1.03  inst_num_in_unprocessed:                37
% 2.19/1.03  inst_num_of_loops:                      310
% 2.19/1.03  inst_num_of_learning_restarts:          0
% 2.19/1.03  inst_num_moves_active_passive:          16
% 2.19/1.03  inst_lit_activity:                      0
% 2.19/1.03  inst_lit_activity_moves:                0
% 2.19/1.03  inst_num_tautologies:                   0
% 2.19/1.03  inst_num_prop_implied:                  0
% 2.19/1.03  inst_num_existing_simplified:           0
% 2.19/1.03  inst_num_eq_res_simplified:             0
% 2.19/1.03  inst_num_child_elim:                    0
% 2.19/1.03  inst_num_of_dismatching_blockings:      102
% 2.19/1.03  inst_num_of_non_proper_insts:           505
% 2.19/1.03  inst_num_of_duplicates:                 0
% 2.19/1.03  inst_inst_num_from_inst_to_res:         0
% 2.19/1.03  inst_dismatching_checking_time:         0.
% 2.19/1.03  
% 2.19/1.03  ------ Resolution
% 2.19/1.03  
% 2.19/1.03  res_num_of_clauses:                     0
% 2.19/1.03  res_num_in_passive:                     0
% 2.19/1.03  res_num_in_active:                      0
% 2.19/1.03  res_num_of_loops:                       89
% 2.19/1.03  res_forward_subset_subsumed:            91
% 2.19/1.03  res_backward_subset_subsumed:           0
% 2.19/1.03  res_forward_subsumed:                   0
% 2.19/1.03  res_backward_subsumed:                  0
% 2.19/1.03  res_forward_subsumption_resolution:     0
% 2.19/1.03  res_backward_subsumption_resolution:    0
% 2.19/1.03  res_clause_to_clause_subsumption:       492
% 2.19/1.03  res_orphan_elimination:                 0
% 2.19/1.03  res_tautology_del:                      122
% 2.19/1.03  res_num_eq_res_simplified:              0
% 2.19/1.03  res_num_sel_changes:                    0
% 2.19/1.03  res_moves_from_active_to_pass:          0
% 2.19/1.03  
% 2.19/1.03  ------ Superposition
% 2.19/1.03  
% 2.19/1.03  sup_time_total:                         0.
% 2.19/1.03  sup_time_generating:                    0.
% 2.19/1.03  sup_time_sim_full:                      0.
% 2.19/1.03  sup_time_sim_immed:                     0.
% 2.19/1.03  
% 2.19/1.03  sup_num_of_clauses:                     84
% 2.19/1.03  sup_num_in_active:                      58
% 2.19/1.03  sup_num_in_passive:                     26
% 2.19/1.03  sup_num_of_loops:                       61
% 2.19/1.03  sup_fw_superposition:                   114
% 2.19/1.03  sup_bw_superposition:                   60
% 2.19/1.03  sup_immediate_simplified:               67
% 2.19/1.03  sup_given_eliminated:                   3
% 2.19/1.03  comparisons_done:                       0
% 2.19/1.03  comparisons_avoided:                    0
% 2.19/1.03  
% 2.19/1.03  ------ Simplifications
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  sim_fw_subset_subsumed:                 46
% 2.19/1.03  sim_bw_subset_subsumed:                 2
% 2.19/1.03  sim_fw_subsumed:                        20
% 2.19/1.03  sim_bw_subsumed:                        2
% 2.19/1.03  sim_fw_subsumption_res:                 0
% 2.19/1.03  sim_bw_subsumption_res:                 0
% 2.19/1.03  sim_tautology_del:                      15
% 2.19/1.03  sim_eq_tautology_del:                   1
% 2.19/1.03  sim_eq_res_simp:                        0
% 2.19/1.03  sim_fw_demodulated:                     0
% 2.19/1.03  sim_bw_demodulated:                     3
% 2.19/1.03  sim_light_normalised:                   4
% 2.19/1.03  sim_joinable_taut:                      0
% 2.19/1.03  sim_joinable_simp:                      0
% 2.19/1.03  sim_ac_normalised:                      0
% 2.19/1.03  sim_smt_subsumption:                    0
% 2.19/1.03  
%------------------------------------------------------------------------------
