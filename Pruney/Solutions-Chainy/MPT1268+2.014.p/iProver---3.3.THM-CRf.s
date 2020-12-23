%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:04 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  176 (3185 expanded)
%              Number of clauses        :  111 ( 801 expanded)
%              Number of leaves         :   16 ( 770 expanded)
%              Depth                    :   23
%              Number of atoms          :  616 (26647 expanded)
%              Number of equality atoms :  210 (4682 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,X0)
        & r1_tarski(sK3,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
              & r1_tarski(X2,sK2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK2,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
                & v3_pre_topc(X2,sK1)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ v2_tops_1(X1,sK1) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK1)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | v2_tops_1(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,sK1)
        & r1_tarski(sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v2_tops_1(sK2,sK1) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK1)
          | ~ r1_tarski(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | v2_tops_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK1)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tops_1(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,
    ( k1_xboole_0 != sK3
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,
    ( r1_tarski(sK3,sK2)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1726,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1718,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1722,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2304,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1722])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1725,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3632,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK1),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2304,c_1725])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_372,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_373,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_25])).

cnf(c_378,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_1885,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_1886,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_17,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_408,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_409,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1888,plain,
    ( v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_1889,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | v2_tops_1(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_1891,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_1892,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1891])).

cnf(c_1716,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2305,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1722])).

cnf(c_1710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_2031,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1710])).

cnf(c_3634,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1725])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_23,negated_conjecture,
    ( v2_tops_1(sK2,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1717,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK2,sK1) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2881,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK2,sK1) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1717])).

cnf(c_4771,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | v2_tops_1(sK2,sK1) = iProver_top
    | v3_pre_topc(k1_tops_1(sK1,sK2),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3634,c_2881])).

cnf(c_5246,plain,
    ( r1_tarski(u1_struct_0(sK1),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3632,c_29,c_1886,c_1889,c_1892,c_2305,c_4771])).

cnf(c_5254,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_5246])).

cnf(c_5461,plain,
    ( sK3 = k1_xboole_0
    | v2_tops_1(sK2,sK1) = iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5254,c_2881])).

cnf(c_2030,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1710])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1727,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3050,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_1727])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_423,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_424,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_1711,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_2153,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1711])).

cnf(c_33,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_473,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1))
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_424])).

cnf(c_474,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_475,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_3411,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_33,c_475])).

cnf(c_3420,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_3411])).

cnf(c_3516,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3420,c_1726])).

cnf(c_3518,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_1727])).

cnf(c_5780,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3050,c_29,c_1886,c_1889,c_1892,c_2030,c_2305,c_3518,c_4771])).

cnf(c_5784,plain,
    ( k1_tops_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5780,c_29,c_1886,c_1889,c_1892,c_2030,c_2305,c_3518,c_4771])).

cnf(c_1714,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_2878,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1714])).

cnf(c_5802,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5784,c_2878])).

cnf(c_1712,plain,
    ( k1_tops_1(sK1,X0) != k1_xboole_0
    | v2_tops_1(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_5804,plain,
    ( sK3 != k1_xboole_0
    | v2_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5784,c_1712])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | sK1 != sK1
    | sK2 != X0
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_409])).

cnf(c_706,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_708,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_24])).

cnf(c_18,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_393,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_394,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1713,plain,
    ( k1_tops_1(sK1,X0) = k1_xboole_0
    | v2_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_2709,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1713])).

cnf(c_5927,plain,
    ( sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5804,c_24,c_29,c_706,c_1886,c_1889,c_1892,c_2305,c_2709,c_4771])).

cnf(c_3421,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_3411])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3537,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3421,c_34])).

cnf(c_3538,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3537])).

cnf(c_3639,plain,
    ( v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_1725])).

cnf(c_6073,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3639,c_29,c_1886,c_1889,c_1892,c_2305,c_4771])).

cnf(c_6083,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_6073])).

cnf(c_8123,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5461,c_29,c_1886,c_1889,c_1892,c_2305,c_4771])).

cnf(c_8128,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8123,c_2709])).

cnf(c_3543,plain,
    ( k1_tops_1(sK1,sK2) = sK3
    | v2_tops_1(sK2,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_1727])).

cnf(c_5931,plain,
    ( k1_tops_1(sK1,sK2) = sK3
    | r1_tarski(k1_tops_1(sK1,sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3543,c_29,c_1886,c_1889,c_1892,c_2305,c_4771])).

cnf(c_8169,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8128,c_5931])).

cnf(c_8877,plain,
    ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8169,c_24,c_29,c_706,c_1886,c_1889,c_1892,c_2305,c_2709,c_4771])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1729,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_338,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_339,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_196])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_247])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1715,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_2732,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_1715])).

cnf(c_4518,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_2732])).

cnf(c_4528,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_4518])).

cnf(c_8882,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8877,c_4528])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.63/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/0.99  
% 2.63/0.99  ------  iProver source info
% 2.63/0.99  
% 2.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/0.99  git: non_committed_changes: false
% 2.63/0.99  git: last_make_outside_of_git: false
% 2.63/0.99  
% 2.63/0.99  ------ 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options
% 2.63/0.99  
% 2.63/0.99  --out_options                           all
% 2.63/0.99  --tptp_safe_out                         true
% 2.63/0.99  --problem_path                          ""
% 2.63/0.99  --include_path                          ""
% 2.63/0.99  --clausifier                            res/vclausify_rel
% 2.63/0.99  --clausifier_options                    --mode clausify
% 2.63/0.99  --stdin                                 false
% 2.63/0.99  --stats_out                             all
% 2.63/0.99  
% 2.63/0.99  ------ General Options
% 2.63/0.99  
% 2.63/0.99  --fof                                   false
% 2.63/0.99  --time_out_real                         305.
% 2.63/0.99  --time_out_virtual                      -1.
% 2.63/0.99  --symbol_type_check                     false
% 2.63/0.99  --clausify_out                          false
% 2.63/0.99  --sig_cnt_out                           false
% 2.63/0.99  --trig_cnt_out                          false
% 2.63/0.99  --trig_cnt_out_tolerance                1.
% 2.63/0.99  --trig_cnt_out_sk_spl                   false
% 2.63/0.99  --abstr_cl_out                          false
% 2.63/0.99  
% 2.63/0.99  ------ Global Options
% 2.63/0.99  
% 2.63/0.99  --schedule                              default
% 2.63/0.99  --add_important_lit                     false
% 2.63/0.99  --prop_solver_per_cl                    1000
% 2.63/0.99  --min_unsat_core                        false
% 2.63/0.99  --soft_assumptions                      false
% 2.63/0.99  --soft_lemma_size                       3
% 2.63/0.99  --prop_impl_unit_size                   0
% 2.63/0.99  --prop_impl_unit                        []
% 2.63/0.99  --share_sel_clauses                     true
% 2.63/0.99  --reset_solvers                         false
% 2.63/0.99  --bc_imp_inh                            [conj_cone]
% 2.63/0.99  --conj_cone_tolerance                   3.
% 2.63/0.99  --extra_neg_conj                        none
% 2.63/0.99  --large_theory_mode                     true
% 2.63/0.99  --prolific_symb_bound                   200
% 2.63/0.99  --lt_threshold                          2000
% 2.63/0.99  --clause_weak_htbl                      true
% 2.63/0.99  --gc_record_bc_elim                     false
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing Options
% 2.63/0.99  
% 2.63/0.99  --preprocessing_flag                    true
% 2.63/0.99  --time_out_prep_mult                    0.1
% 2.63/0.99  --splitting_mode                        input
% 2.63/0.99  --splitting_grd                         true
% 2.63/0.99  --splitting_cvd                         false
% 2.63/0.99  --splitting_cvd_svl                     false
% 2.63/0.99  --splitting_nvd                         32
% 2.63/0.99  --sub_typing                            true
% 2.63/0.99  --prep_gs_sim                           true
% 2.63/0.99  --prep_unflatten                        true
% 2.63/0.99  --prep_res_sim                          true
% 2.63/0.99  --prep_upred                            true
% 2.63/0.99  --prep_sem_filter                       exhaustive
% 2.63/0.99  --prep_sem_filter_out                   false
% 2.63/0.99  --pred_elim                             true
% 2.63/0.99  --res_sim_input                         true
% 2.63/0.99  --eq_ax_congr_red                       true
% 2.63/0.99  --pure_diseq_elim                       true
% 2.63/0.99  --brand_transform                       false
% 2.63/0.99  --non_eq_to_eq                          false
% 2.63/0.99  --prep_def_merge                        true
% 2.63/0.99  --prep_def_merge_prop_impl              false
% 2.63/0.99  --prep_def_merge_mbd                    true
% 2.63/0.99  --prep_def_merge_tr_red                 false
% 2.63/0.99  --prep_def_merge_tr_cl                  false
% 2.63/0.99  --smt_preprocessing                     true
% 2.63/0.99  --smt_ac_axioms                         fast
% 2.63/0.99  --preprocessed_out                      false
% 2.63/0.99  --preprocessed_stats                    false
% 2.63/0.99  
% 2.63/0.99  ------ Abstraction refinement Options
% 2.63/0.99  
% 2.63/0.99  --abstr_ref                             []
% 2.63/0.99  --abstr_ref_prep                        false
% 2.63/0.99  --abstr_ref_until_sat                   false
% 2.63/0.99  --abstr_ref_sig_restrict                funpre
% 2.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.99  --abstr_ref_under                       []
% 2.63/0.99  
% 2.63/0.99  ------ SAT Options
% 2.63/0.99  
% 2.63/0.99  --sat_mode                              false
% 2.63/0.99  --sat_fm_restart_options                ""
% 2.63/0.99  --sat_gr_def                            false
% 2.63/0.99  --sat_epr_types                         true
% 2.63/0.99  --sat_non_cyclic_types                  false
% 2.63/0.99  --sat_finite_models                     false
% 2.63/0.99  --sat_fm_lemmas                         false
% 2.63/0.99  --sat_fm_prep                           false
% 2.63/0.99  --sat_fm_uc_incr                        true
% 2.63/0.99  --sat_out_model                         small
% 2.63/0.99  --sat_out_clauses                       false
% 2.63/0.99  
% 2.63/0.99  ------ QBF Options
% 2.63/0.99  
% 2.63/0.99  --qbf_mode                              false
% 2.63/0.99  --qbf_elim_univ                         false
% 2.63/0.99  --qbf_dom_inst                          none
% 2.63/0.99  --qbf_dom_pre_inst                      false
% 2.63/0.99  --qbf_sk_in                             false
% 2.63/0.99  --qbf_pred_elim                         true
% 2.63/0.99  --qbf_split                             512
% 2.63/0.99  
% 2.63/0.99  ------ BMC1 Options
% 2.63/0.99  
% 2.63/0.99  --bmc1_incremental                      false
% 2.63/0.99  --bmc1_axioms                           reachable_all
% 2.63/0.99  --bmc1_min_bound                        0
% 2.63/0.99  --bmc1_max_bound                        -1
% 2.63/0.99  --bmc1_max_bound_default                -1
% 2.63/0.99  --bmc1_symbol_reachability              true
% 2.63/0.99  --bmc1_property_lemmas                  false
% 2.63/0.99  --bmc1_k_induction                      false
% 2.63/0.99  --bmc1_non_equiv_states                 false
% 2.63/0.99  --bmc1_deadlock                         false
% 2.63/0.99  --bmc1_ucm                              false
% 2.63/0.99  --bmc1_add_unsat_core                   none
% 2.63/0.99  --bmc1_unsat_core_children              false
% 2.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.99  --bmc1_out_stat                         full
% 2.63/0.99  --bmc1_ground_init                      false
% 2.63/0.99  --bmc1_pre_inst_next_state              false
% 2.63/0.99  --bmc1_pre_inst_state                   false
% 2.63/0.99  --bmc1_pre_inst_reach_state             false
% 2.63/0.99  --bmc1_out_unsat_core                   false
% 2.63/0.99  --bmc1_aig_witness_out                  false
% 2.63/0.99  --bmc1_verbose                          false
% 2.63/0.99  --bmc1_dump_clauses_tptp                false
% 2.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.99  --bmc1_dump_file                        -
% 2.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.99  --bmc1_ucm_extend_mode                  1
% 2.63/0.99  --bmc1_ucm_init_mode                    2
% 2.63/0.99  --bmc1_ucm_cone_mode                    none
% 2.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.99  --bmc1_ucm_relax_model                  4
% 2.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.99  --bmc1_ucm_layered_model                none
% 2.63/0.99  --bmc1_ucm_max_lemma_size               10
% 2.63/0.99  
% 2.63/0.99  ------ AIG Options
% 2.63/0.99  
% 2.63/0.99  --aig_mode                              false
% 2.63/0.99  
% 2.63/0.99  ------ Instantiation Options
% 2.63/0.99  
% 2.63/0.99  --instantiation_flag                    true
% 2.63/0.99  --inst_sos_flag                         false
% 2.63/0.99  --inst_sos_phase                        true
% 2.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel_side                     num_symb
% 2.63/0.99  --inst_solver_per_active                1400
% 2.63/0.99  --inst_solver_calls_frac                1.
% 2.63/0.99  --inst_passive_queue_type               priority_queues
% 2.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.99  --inst_passive_queues_freq              [25;2]
% 2.63/0.99  --inst_dismatching                      true
% 2.63/0.99  --inst_eager_unprocessed_to_passive     true
% 2.63/0.99  --inst_prop_sim_given                   true
% 2.63/0.99  --inst_prop_sim_new                     false
% 2.63/0.99  --inst_subs_new                         false
% 2.63/0.99  --inst_eq_res_simp                      false
% 2.63/0.99  --inst_subs_given                       false
% 2.63/0.99  --inst_orphan_elimination               true
% 2.63/0.99  --inst_learning_loop_flag               true
% 2.63/0.99  --inst_learning_start                   3000
% 2.63/0.99  --inst_learning_factor                  2
% 2.63/0.99  --inst_start_prop_sim_after_learn       3
% 2.63/0.99  --inst_sel_renew                        solver
% 2.63/0.99  --inst_lit_activity_flag                true
% 2.63/0.99  --inst_restr_to_given                   false
% 2.63/0.99  --inst_activity_threshold               500
% 2.63/0.99  --inst_out_proof                        true
% 2.63/0.99  
% 2.63/0.99  ------ Resolution Options
% 2.63/0.99  
% 2.63/0.99  --resolution_flag                       true
% 2.63/0.99  --res_lit_sel                           adaptive
% 2.63/0.99  --res_lit_sel_side                      none
% 2.63/0.99  --res_ordering                          kbo
% 2.63/0.99  --res_to_prop_solver                    active
% 2.63/0.99  --res_prop_simpl_new                    false
% 2.63/0.99  --res_prop_simpl_given                  true
% 2.63/0.99  --res_passive_queue_type                priority_queues
% 2.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.99  --res_passive_queues_freq               [15;5]
% 2.63/0.99  --res_forward_subs                      full
% 2.63/0.99  --res_backward_subs                     full
% 2.63/0.99  --res_forward_subs_resolution           true
% 2.63/0.99  --res_backward_subs_resolution          true
% 2.63/0.99  --res_orphan_elimination                true
% 2.63/0.99  --res_time_limit                        2.
% 2.63/0.99  --res_out_proof                         true
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Options
% 2.63/0.99  
% 2.63/0.99  --superposition_flag                    true
% 2.63/0.99  --sup_passive_queue_type                priority_queues
% 2.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.99  --demod_completeness_check              fast
% 2.63/0.99  --demod_use_ground                      true
% 2.63/0.99  --sup_to_prop_solver                    passive
% 2.63/0.99  --sup_prop_simpl_new                    true
% 2.63/0.99  --sup_prop_simpl_given                  true
% 2.63/0.99  --sup_fun_splitting                     false
% 2.63/0.99  --sup_smt_interval                      50000
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Simplification Setup
% 2.63/0.99  
% 2.63/0.99  --sup_indices_passive                   []
% 2.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_full_bw                           [BwDemod]
% 2.63/0.99  --sup_immed_triv                        [TrivRules]
% 2.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_immed_bw_main                     []
% 2.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  
% 2.63/0.99  ------ Combination Options
% 2.63/0.99  
% 2.63/0.99  --comb_res_mult                         3
% 2.63/0.99  --comb_sup_mult                         2
% 2.63/0.99  --comb_inst_mult                        10
% 2.63/0.99  
% 2.63/0.99  ------ Debug Options
% 2.63/0.99  
% 2.63/0.99  --dbg_backtrace                         false
% 2.63/0.99  --dbg_dump_prop_clauses                 false
% 2.63/0.99  --dbg_dump_prop_clauses_file            -
% 2.63/0.99  --dbg_out_stat                          false
% 2.63/0.99  ------ Parsing...
% 2.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/0.99  ------ Proving...
% 2.63/0.99  ------ Problem Properties 
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  clauses                                 22
% 2.63/0.99  conjectures                             6
% 2.63/0.99  EPR                                     8
% 2.63/0.99  Horn                                    20
% 2.63/0.99  unary                                   4
% 2.63/0.99  binary                                  10
% 2.63/0.99  lits                                    52
% 2.63/0.99  lits eq                                 6
% 2.63/0.99  fd_pure                                 0
% 2.63/0.99  fd_pseudo                               0
% 2.63/0.99  fd_cond                                 1
% 2.63/0.99  fd_pseudo_cond                          1
% 2.63/0.99  AC symbols                              0
% 2.63/0.99  
% 2.63/0.99  ------ Schedule dynamic 5 is on 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  ------ 
% 2.63/0.99  Current options:
% 2.63/0.99  ------ 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options
% 2.63/0.99  
% 2.63/0.99  --out_options                           all
% 2.63/0.99  --tptp_safe_out                         true
% 2.63/0.99  --problem_path                          ""
% 2.63/0.99  --include_path                          ""
% 2.63/0.99  --clausifier                            res/vclausify_rel
% 2.63/0.99  --clausifier_options                    --mode clausify
% 2.63/0.99  --stdin                                 false
% 2.63/0.99  --stats_out                             all
% 2.63/0.99  
% 2.63/0.99  ------ General Options
% 2.63/0.99  
% 2.63/0.99  --fof                                   false
% 2.63/0.99  --time_out_real                         305.
% 2.63/0.99  --time_out_virtual                      -1.
% 2.63/0.99  --symbol_type_check                     false
% 2.63/0.99  --clausify_out                          false
% 2.63/0.99  --sig_cnt_out                           false
% 2.63/0.99  --trig_cnt_out                          false
% 2.63/0.99  --trig_cnt_out_tolerance                1.
% 2.63/0.99  --trig_cnt_out_sk_spl                   false
% 2.63/0.99  --abstr_cl_out                          false
% 2.63/0.99  
% 2.63/0.99  ------ Global Options
% 2.63/0.99  
% 2.63/0.99  --schedule                              default
% 2.63/0.99  --add_important_lit                     false
% 2.63/0.99  --prop_solver_per_cl                    1000
% 2.63/0.99  --min_unsat_core                        false
% 2.63/0.99  --soft_assumptions                      false
% 2.63/0.99  --soft_lemma_size                       3
% 2.63/0.99  --prop_impl_unit_size                   0
% 2.63/0.99  --prop_impl_unit                        []
% 2.63/0.99  --share_sel_clauses                     true
% 2.63/0.99  --reset_solvers                         false
% 2.63/0.99  --bc_imp_inh                            [conj_cone]
% 2.63/0.99  --conj_cone_tolerance                   3.
% 2.63/0.99  --extra_neg_conj                        none
% 2.63/0.99  --large_theory_mode                     true
% 2.63/0.99  --prolific_symb_bound                   200
% 2.63/0.99  --lt_threshold                          2000
% 2.63/0.99  --clause_weak_htbl                      true
% 2.63/0.99  --gc_record_bc_elim                     false
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing Options
% 2.63/0.99  
% 2.63/0.99  --preprocessing_flag                    true
% 2.63/0.99  --time_out_prep_mult                    0.1
% 2.63/0.99  --splitting_mode                        input
% 2.63/0.99  --splitting_grd                         true
% 2.63/0.99  --splitting_cvd                         false
% 2.63/0.99  --splitting_cvd_svl                     false
% 2.63/0.99  --splitting_nvd                         32
% 2.63/0.99  --sub_typing                            true
% 2.63/0.99  --prep_gs_sim                           true
% 2.63/0.99  --prep_unflatten                        true
% 2.63/0.99  --prep_res_sim                          true
% 2.63/0.99  --prep_upred                            true
% 2.63/0.99  --prep_sem_filter                       exhaustive
% 2.63/0.99  --prep_sem_filter_out                   false
% 2.63/0.99  --pred_elim                             true
% 2.63/0.99  --res_sim_input                         true
% 2.63/0.99  --eq_ax_congr_red                       true
% 2.63/0.99  --pure_diseq_elim                       true
% 2.63/0.99  --brand_transform                       false
% 2.63/0.99  --non_eq_to_eq                          false
% 2.63/0.99  --prep_def_merge                        true
% 2.63/0.99  --prep_def_merge_prop_impl              false
% 2.63/0.99  --prep_def_merge_mbd                    true
% 2.63/0.99  --prep_def_merge_tr_red                 false
% 2.63/0.99  --prep_def_merge_tr_cl                  false
% 2.63/0.99  --smt_preprocessing                     true
% 2.63/0.99  --smt_ac_axioms                         fast
% 2.63/0.99  --preprocessed_out                      false
% 2.63/0.99  --preprocessed_stats                    false
% 2.63/0.99  
% 2.63/0.99  ------ Abstraction refinement Options
% 2.63/0.99  
% 2.63/0.99  --abstr_ref                             []
% 2.63/0.99  --abstr_ref_prep                        false
% 2.63/0.99  --abstr_ref_until_sat                   false
% 2.63/0.99  --abstr_ref_sig_restrict                funpre
% 2.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.99  --abstr_ref_under                       []
% 2.63/0.99  
% 2.63/0.99  ------ SAT Options
% 2.63/0.99  
% 2.63/0.99  --sat_mode                              false
% 2.63/0.99  --sat_fm_restart_options                ""
% 2.63/0.99  --sat_gr_def                            false
% 2.63/0.99  --sat_epr_types                         true
% 2.63/0.99  --sat_non_cyclic_types                  false
% 2.63/0.99  --sat_finite_models                     false
% 2.63/0.99  --sat_fm_lemmas                         false
% 2.63/0.99  --sat_fm_prep                           false
% 2.63/0.99  --sat_fm_uc_incr                        true
% 2.63/0.99  --sat_out_model                         small
% 2.63/0.99  --sat_out_clauses                       false
% 2.63/0.99  
% 2.63/0.99  ------ QBF Options
% 2.63/0.99  
% 2.63/0.99  --qbf_mode                              false
% 2.63/0.99  --qbf_elim_univ                         false
% 2.63/0.99  --qbf_dom_inst                          none
% 2.63/0.99  --qbf_dom_pre_inst                      false
% 2.63/0.99  --qbf_sk_in                             false
% 2.63/0.99  --qbf_pred_elim                         true
% 2.63/0.99  --qbf_split                             512
% 2.63/0.99  
% 2.63/0.99  ------ BMC1 Options
% 2.63/0.99  
% 2.63/0.99  --bmc1_incremental                      false
% 2.63/0.99  --bmc1_axioms                           reachable_all
% 2.63/0.99  --bmc1_min_bound                        0
% 2.63/0.99  --bmc1_max_bound                        -1
% 2.63/0.99  --bmc1_max_bound_default                -1
% 2.63/0.99  --bmc1_symbol_reachability              true
% 2.63/0.99  --bmc1_property_lemmas                  false
% 2.63/0.99  --bmc1_k_induction                      false
% 2.63/0.99  --bmc1_non_equiv_states                 false
% 2.63/0.99  --bmc1_deadlock                         false
% 2.63/0.99  --bmc1_ucm                              false
% 2.63/0.99  --bmc1_add_unsat_core                   none
% 2.63/0.99  --bmc1_unsat_core_children              false
% 2.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.99  --bmc1_out_stat                         full
% 2.63/0.99  --bmc1_ground_init                      false
% 2.63/0.99  --bmc1_pre_inst_next_state              false
% 2.63/0.99  --bmc1_pre_inst_state                   false
% 2.63/0.99  --bmc1_pre_inst_reach_state             false
% 2.63/0.99  --bmc1_out_unsat_core                   false
% 2.63/0.99  --bmc1_aig_witness_out                  false
% 2.63/0.99  --bmc1_verbose                          false
% 2.63/0.99  --bmc1_dump_clauses_tptp                false
% 2.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.99  --bmc1_dump_file                        -
% 2.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.99  --bmc1_ucm_extend_mode                  1
% 2.63/0.99  --bmc1_ucm_init_mode                    2
% 2.63/0.99  --bmc1_ucm_cone_mode                    none
% 2.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.99  --bmc1_ucm_relax_model                  4
% 2.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.99  --bmc1_ucm_layered_model                none
% 2.63/0.99  --bmc1_ucm_max_lemma_size               10
% 2.63/0.99  
% 2.63/0.99  ------ AIG Options
% 2.63/0.99  
% 2.63/0.99  --aig_mode                              false
% 2.63/0.99  
% 2.63/0.99  ------ Instantiation Options
% 2.63/0.99  
% 2.63/0.99  --instantiation_flag                    true
% 2.63/0.99  --inst_sos_flag                         false
% 2.63/0.99  --inst_sos_phase                        true
% 2.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel_side                     none
% 2.63/0.99  --inst_solver_per_active                1400
% 2.63/0.99  --inst_solver_calls_frac                1.
% 2.63/0.99  --inst_passive_queue_type               priority_queues
% 2.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.99  --inst_passive_queues_freq              [25;2]
% 2.63/0.99  --inst_dismatching                      true
% 2.63/0.99  --inst_eager_unprocessed_to_passive     true
% 2.63/0.99  --inst_prop_sim_given                   true
% 2.63/0.99  --inst_prop_sim_new                     false
% 2.63/0.99  --inst_subs_new                         false
% 2.63/0.99  --inst_eq_res_simp                      false
% 2.63/0.99  --inst_subs_given                       false
% 2.63/0.99  --inst_orphan_elimination               true
% 2.63/0.99  --inst_learning_loop_flag               true
% 2.63/0.99  --inst_learning_start                   3000
% 2.63/0.99  --inst_learning_factor                  2
% 2.63/0.99  --inst_start_prop_sim_after_learn       3
% 2.63/0.99  --inst_sel_renew                        solver
% 2.63/0.99  --inst_lit_activity_flag                true
% 2.63/0.99  --inst_restr_to_given                   false
% 2.63/0.99  --inst_activity_threshold               500
% 2.63/0.99  --inst_out_proof                        true
% 2.63/0.99  
% 2.63/0.99  ------ Resolution Options
% 2.63/0.99  
% 2.63/0.99  --resolution_flag                       false
% 2.63/0.99  --res_lit_sel                           adaptive
% 2.63/0.99  --res_lit_sel_side                      none
% 2.63/0.99  --res_ordering                          kbo
% 2.63/0.99  --res_to_prop_solver                    active
% 2.63/0.99  --res_prop_simpl_new                    false
% 2.63/0.99  --res_prop_simpl_given                  true
% 2.63/0.99  --res_passive_queue_type                priority_queues
% 2.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.99  --res_passive_queues_freq               [15;5]
% 2.63/0.99  --res_forward_subs                      full
% 2.63/0.99  --res_backward_subs                     full
% 2.63/0.99  --res_forward_subs_resolution           true
% 2.63/0.99  --res_backward_subs_resolution          true
% 2.63/0.99  --res_orphan_elimination                true
% 2.63/0.99  --res_time_limit                        2.
% 2.63/0.99  --res_out_proof                         true
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Options
% 2.63/0.99  
% 2.63/0.99  --superposition_flag                    true
% 2.63/0.99  --sup_passive_queue_type                priority_queues
% 2.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.99  --demod_completeness_check              fast
% 2.63/0.99  --demod_use_ground                      true
% 2.63/0.99  --sup_to_prop_solver                    passive
% 2.63/0.99  --sup_prop_simpl_new                    true
% 2.63/0.99  --sup_prop_simpl_given                  true
% 2.63/0.99  --sup_fun_splitting                     false
% 2.63/0.99  --sup_smt_interval                      50000
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Simplification Setup
% 2.63/0.99  
% 2.63/0.99  --sup_indices_passive                   []
% 2.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_full_bw                           [BwDemod]
% 2.63/0.99  --sup_immed_triv                        [TrivRules]
% 2.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_immed_bw_main                     []
% 2.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  
% 2.63/0.99  ------ Combination Options
% 2.63/0.99  
% 2.63/0.99  --comb_res_mult                         3
% 2.63/0.99  --comb_sup_mult                         2
% 2.63/0.99  --comb_inst_mult                        10
% 2.63/0.99  
% 2.63/0.99  ------ Debug Options
% 2.63/0.99  
% 2.63/0.99  --dbg_backtrace                         false
% 2.63/0.99  --dbg_dump_prop_clauses                 false
% 2.63/0.99  --dbg_dump_prop_clauses_file            -
% 2.63/0.99  --dbg_out_stat                          false
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  ------ Proving...
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  % SZS status Theorem for theBenchmark.p
% 2.63/0.99  
% 2.63/0.99   Resolution empty clause
% 2.63/0.99  
% 2.63/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  fof(f2,axiom,(
% 2.63/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f34,plain,(
% 2.63/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.63/0.99    inference(nnf_transformation,[],[f2])).
% 2.63/0.99  
% 2.63/0.99  fof(f35,plain,(
% 2.63/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.63/0.99    inference(flattening,[],[f34])).
% 2.63/0.99  
% 2.63/0.99  fof(f48,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.63/0.99    inference(cnf_transformation,[],[f35])).
% 2.63/0.99  
% 2.63/0.99  fof(f73,plain,(
% 2.63/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.63/0.99    inference(equality_resolution,[],[f48])).
% 2.63/0.99  
% 2.63/0.99  fof(f14,conjecture,(
% 2.63/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f15,negated_conjecture,(
% 2.63/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.63/0.99    inference(negated_conjecture,[],[f14])).
% 2.63/0.99  
% 2.63/0.99  fof(f28,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f15])).
% 2.63/0.99  
% 2.63/0.99  fof(f29,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.99    inference(flattening,[],[f28])).
% 2.63/0.99  
% 2.63/0.99  fof(f38,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.99    inference(nnf_transformation,[],[f29])).
% 2.63/0.99  
% 2.63/0.99  fof(f39,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.99    inference(flattening,[],[f38])).
% 2.63/0.99  
% 2.63/0.99  fof(f40,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.63/0.99    inference(rectify,[],[f39])).
% 2.63/0.99  
% 2.63/0.99  fof(f43,plain,(
% 2.63/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK3 & v3_pre_topc(sK3,X0) & r1_tarski(sK3,X1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f42,plain,(
% 2.63/0.99    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK2,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f41,plain,(
% 2.63/0.99    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK1) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(X1,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f44,plain,(
% 2.63/0.99    (((k1_xboole_0 != sK3 & v3_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(sK2,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 2.63/0.99  
% 2.63/0.99  fof(f68,plain,(
% 2.63/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_tops_1(sK2,sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f8,axiom,(
% 2.63/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f36,plain,(
% 2.63/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.63/0.99    inference(nnf_transformation,[],[f8])).
% 2.63/0.99  
% 2.63/0.99  fof(f56,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.63/0.99    inference(cnf_transformation,[],[f36])).
% 2.63/0.99  
% 2.63/0.99  fof(f3,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f17,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.63/0.99    inference(ennf_transformation,[],[f3])).
% 2.63/0.99  
% 2.63/0.99  fof(f18,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.63/0.99    inference(flattening,[],[f17])).
% 2.63/0.99  
% 2.63/0.99  fof(f51,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f18])).
% 2.63/0.99  
% 2.63/0.99  fof(f66,plain,(
% 2.63/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f10,axiom,(
% 2.63/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f22,plain,(
% 2.63/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f10])).
% 2.63/0.99  
% 2.63/0.99  fof(f23,plain,(
% 2.63/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.63/0.99    inference(flattening,[],[f22])).
% 2.63/0.99  
% 2.63/0.99  fof(f59,plain,(
% 2.63/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f23])).
% 2.63/0.99  
% 2.63/0.99  fof(f64,plain,(
% 2.63/0.99    v2_pre_topc(sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f65,plain,(
% 2.63/0.99    l1_pre_topc(sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f13,axiom,(
% 2.63/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f27,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f13])).
% 2.63/0.99  
% 2.63/0.99  fof(f37,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.99    inference(nnf_transformation,[],[f27])).
% 2.63/0.99  
% 2.63/0.99  fof(f63,plain,(
% 2.63/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f37])).
% 2.63/0.99  
% 2.63/0.99  fof(f11,axiom,(
% 2.63/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f24,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f11])).
% 2.63/0.99  
% 2.63/0.99  fof(f60,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f24])).
% 2.63/0.99  
% 2.63/0.99  fof(f57,plain,(
% 2.63/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f36])).
% 2.63/0.99  
% 2.63/0.99  fof(f67,plain,(
% 2.63/0.99    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tops_1(sK2,sK1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f50,plain,(
% 2.63/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f35])).
% 2.63/0.99  
% 2.63/0.99  fof(f12,axiom,(
% 2.63/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f25,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f12])).
% 2.63/0.99  
% 2.63/0.99  fof(f26,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.63/0.99    inference(flattening,[],[f25])).
% 2.63/0.99  
% 2.63/0.99  fof(f61,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f26])).
% 2.63/0.99  
% 2.63/0.99  fof(f70,plain,(
% 2.63/0.99    v3_pre_topc(sK3,sK1) | ~v2_tops_1(sK2,sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f71,plain,(
% 2.63/0.99    k1_xboole_0 != sK3 | ~v2_tops_1(sK2,sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f62,plain,(
% 2.63/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f37])).
% 2.63/0.99  
% 2.63/0.99  fof(f69,plain,(
% 2.63/0.99    r1_tarski(sK3,sK2) | ~v2_tops_1(sK2,sK1)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f1,axiom,(
% 2.63/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f16,plain,(
% 2.63/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f1])).
% 2.63/0.99  
% 2.63/0.99  fof(f30,plain,(
% 2.63/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.63/0.99    inference(nnf_transformation,[],[f16])).
% 2.63/0.99  
% 2.63/0.99  fof(f31,plain,(
% 2.63/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.63/0.99    inference(rectify,[],[f30])).
% 2.63/0.99  
% 2.63/0.99  fof(f32,plain,(
% 2.63/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f33,plain,(
% 2.63/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.63/0.99  
% 2.63/0.99  fof(f46,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f33])).
% 2.63/0.99  
% 2.63/0.99  fof(f4,axiom,(
% 2.63/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f52,plain,(
% 2.63/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f4])).
% 2.63/0.99  
% 2.63/0.99  fof(f5,axiom,(
% 2.63/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f19,plain,(
% 2.63/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f5])).
% 2.63/0.99  
% 2.63/0.99  fof(f20,plain,(
% 2.63/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.63/0.99    inference(flattening,[],[f19])).
% 2.63/0.99  
% 2.63/0.99  fof(f53,plain,(
% 2.63/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f20])).
% 2.63/0.99  
% 2.63/0.99  fof(f9,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f21,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f9])).
% 2.63/0.99  
% 2.63/0.99  fof(f58,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f21])).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f73]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1726,plain,
% 2.63/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_22,negated_conjecture,
% 2.63/0.99      ( ~ v2_tops_1(sK2,sK1) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.63/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1718,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_12,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1722,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.63/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2304,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1718,c_1722]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_6,plain,
% 2.63/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.63/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1725,plain,
% 2.63/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.63/0.99      | r1_tarski(X1,X2) != iProver_top
% 2.63/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3632,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(u1_struct_0(sK1),X0) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2304,c_1725]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_24,negated_conjecture,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.63/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_29,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_14,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.99      | ~ v2_pre_topc(X0)
% 2.63/0.99      | ~ l1_pre_topc(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_26,negated_conjecture,
% 2.63/0.99      ( v2_pre_topc(sK1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_372,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.99      | ~ l1_pre_topc(X0)
% 2.63/0.99      | sK1 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_373,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ l1_pre_topc(sK1) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_372]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_25,negated_conjecture,
% 2.63/0.99      ( l1_pre_topc(sK1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_377,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 2.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_373,c_25]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_378,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.63/0.99      inference(renaming,[status(thm)],[c_377]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1885,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1)
% 2.63/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_378]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1886,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(sK1,sK2),sK1) = iProver_top
% 2.63/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_17,plain,
% 2.63/0.99      ( v2_tops_1(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ l1_pre_topc(X1)
% 2.63/0.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_408,plain,
% 2.63/0.99      ( v2_tops_1(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | k1_tops_1(X1,X0) != k1_xboole_0
% 2.63/0.99      | sK1 != X1 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_409,plain,
% 2.63/0.99      ( v2_tops_1(X0,sK1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | k1_tops_1(sK1,X0) != k1_xboole_0 ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1888,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1)
% 2.63/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_409]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1889,plain,
% 2.63/0.99      ( k1_tops_1(sK1,sK2) != k1_xboole_0
% 2.63/0.99      | v2_tops_1(sK2,sK1) = iProver_top
% 2.63/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_15,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.63/0.99      | ~ l1_pre_topc(X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_444,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.63/0.99      | sK1 != X1 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_445,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1891,plain,
% 2.63/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_445]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1892,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1891]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1716,plain,
% 2.63/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2305,plain,
% 2.63/0.99      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1716,c_1722]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1710,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2031,plain,
% 2.63/0.99      ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1716,c_1710]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3634,plain,
% 2.63/0.99      ( r1_tarski(k1_tops_1(sK1,sK2),X0) = iProver_top
% 2.63/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2031,c_1725]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_11,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1723,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.63/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_23,negated_conjecture,
% 2.63/0.99      ( v2_tops_1(sK2,sK1)
% 2.63/0.99      | ~ v3_pre_topc(X0,sK1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ r1_tarski(X0,sK2)
% 2.63/0.99      | k1_xboole_0 = X0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1717,plain,
% 2.63/0.99      ( k1_xboole_0 = X0
% 2.63/0.99      | v2_tops_1(sK2,sK1) = iProver_top
% 2.63/0.99      | v3_pre_topc(X0,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(X0,sK2) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2881,plain,
% 2.63/0.99      ( k1_xboole_0 = X0
% 2.63/0.99      | v2_tops_1(sK2,sK1) = iProver_top
% 2.63/0.99      | v3_pre_topc(X0,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
% 2.63/0.99      | r1_tarski(X0,sK2) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1723,c_1717]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_4771,plain,
% 2.63/0.99      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 2.63/0.99      | v2_tops_1(sK2,sK1) = iProver_top
% 2.63/0.99      | v3_pre_topc(k1_tops_1(sK1,sK2),sK1) != iProver_top
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,sK2),sK2) != iProver_top
% 2.63/0.99      | r1_tarski(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_3634,c_2881]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5246,plain,
% 2.63/0.99      ( r1_tarski(u1_struct_0(sK1),X0) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_3632,c_29,c_1886,c_1889,c_1892,c_2305,c_4771]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5254,plain,
% 2.63/0.99      ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1726,c_5246]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5461,plain,
% 2.63/0.99      ( sK3 = k1_xboole_0
% 2.63/0.99      | v2_tops_1(sK2,sK1) = iProver_top
% 2.63/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,sK2) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_5254,c_2881]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2030,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1718,c_1710]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3,plain,
% 2.63/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1727,plain,
% 2.63/0.99      ( X0 = X1
% 2.63/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.63/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3050,plain,
% 2.63/0.99      ( k1_tops_1(sK1,sK3) = sK3
% 2.63/0.99      | v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2030,c_1727]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_16,plain,
% 2.63/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ r1_tarski(X0,X2)
% 2.63/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.63/0.99      | ~ l1_pre_topc(X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_423,plain,
% 2.63/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ r1_tarski(X0,X2)
% 2.63/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.63/0.99      | sK1 != X1 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_424,plain,
% 2.63/0.99      ( ~ v3_pre_topc(X0,sK1)
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ r1_tarski(X0,X1)
% 2.63/0.99      | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_423]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1711,plain,
% 2.63/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.63/0.99      | r1_tarski(X0,k1_tops_1(sK1,X1)) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2153,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,X0) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1718,c_1711]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_33,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_20,negated_conjecture,
% 2.63/0.99      ( ~ v2_tops_1(sK2,sK1) | v3_pre_topc(sK3,sK1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_473,plain,
% 2.63/0.99      ( ~ v2_tops_1(sK2,sK1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ r1_tarski(X0,X1)
% 2.63/0.99      | r1_tarski(X0,k1_tops_1(sK1,X1))
% 2.63/0.99      | sK1 != sK1
% 2.63/0.99      | sK3 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_424]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_474,plain,
% 2.63/0.99      ( ~ v2_tops_1(sK2,sK1)
% 2.63/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | ~ r1_tarski(sK3,X0)
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_475,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,X0) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3411,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,X0) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_2153,c_33,c_475]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3420,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,sK3)) = iProver_top
% 2.63/0.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1718,c_3411]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3516,plain,
% 2.63/0.99      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3420,c_1726]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_3518,plain,
% 2.63/0.99      ( k1_tops_1(sK1,sK3) = sK3
% 2.63/0.99      | v2_tops_1(sK2,sK1) != iProver_top
% 2.63/0.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_3516,c_1727]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5780,plain,
% 2.63/0.99      ( k1_tops_1(sK1,sK3) = sK3
% 2.63/0.99      | r1_tarski(sK3,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_3050,c_29,c_1886,c_1889,c_1892,c_2030,c_2305,c_3518,c_4771]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5784,plain,
% 2.63/0.99      ( k1_tops_1(sK1,sK3) = sK3 ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_5780,c_29,c_1886,c_1889,c_1892,c_2030,c_2305,c_3518,c_4771]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1714,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1) = iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2878,plain,
% 2.63/0.99      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1) = iProver_top
% 2.63/0.99      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1723,c_1714]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5802,plain,
% 2.63/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 2.63/0.99      | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_5784,c_2878]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1712,plain,
% 2.63/0.99      ( k1_tops_1(sK1,X0) != k1_xboole_0
% 2.63/0.99      | v2_tops_1(X0,sK1) = iProver_top
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5804,plain,
% 2.63/0.99      ( sK3 != k1_xboole_0
% 2.63/0.99      | v2_tops_1(sK3,sK1) = iProver_top
% 2.63/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_5784,c_1712]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_19,negated_conjecture,
% 2.63/0.99      ( ~ v2_tops_1(sK2,sK1) | k1_xboole_0 != sK3 ),
% 2.63/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_705,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/0.99      | k1_tops_1(sK1,X0) != k1_xboole_0
% 2.63/0.99      | sK1 != sK1
% 2.63/0.99      | sK2 != X0
% 2.63/0.99      | sK3 != k1_xboole_0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_409]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_706,plain,
% 2.63/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0
% 2.63/1.00      | sK3 != k1_xboole_0 ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_705]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_708,plain,
% 2.63/1.00      ( k1_tops_1(sK1,sK2) != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 2.63/1.00      inference(global_propositional_subsumption,[status(thm)],[c_706,c_24]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_18,plain,
% 2.63/1.00      ( ~ v2_tops_1(X0,X1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/1.00      | ~ l1_pre_topc(X1)
% 2.63/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.63/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_393,plain,
% 2.63/1.00      ( ~ v2_tops_1(X0,X1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.63/1.00      | sK1 != X1 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_394,plain,
% 2.63/1.00      ( ~ v2_tops_1(X0,sK1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.63/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0 ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1713,plain,
% 2.63/1.00      ( k1_tops_1(sK1,X0) = k1_xboole_0
% 2.63/1.00      | v2_tops_1(X0,sK1) != iProver_top
% 2.63/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2709,plain,
% 2.63/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0 | v2_tops_1(sK2,sK1) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1716,c_1713]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5927,plain,
% 2.63/1.00      ( sK3 != k1_xboole_0 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_5804,c_24,c_29,c_706,c_1886,c_1889,c_1892,c_2305,c_2709,
% 2.63/1.00                 c_4771]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3421,plain,
% 2.63/1.00      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/1.00      | r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top
% 2.63/1.00      | r1_tarski(sK3,sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1716,c_3411]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_21,negated_conjecture,
% 2.63/1.00      ( ~ v2_tops_1(sK2,sK1) | r1_tarski(sK3,sK2) ),
% 2.63/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_34,plain,
% 2.63/1.00      ( v2_tops_1(sK2,sK1) != iProver_top | r1_tarski(sK3,sK2) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3537,plain,
% 2.63/1.00      ( r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top
% 2.63/1.00      | v2_tops_1(sK2,sK1) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3421,c_34]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3538,plain,
% 2.63/1.00      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/1.00      | r1_tarski(sK3,k1_tops_1(sK1,sK2)) = iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_3537]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3639,plain,
% 2.63/1.00      ( v2_tops_1(sK2,sK1) != iProver_top
% 2.63/1.00      | r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top
% 2.63/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3538,c_1725]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_6073,plain,
% 2.63/1.00      ( r1_tarski(k1_tops_1(sK1,sK2),X0) != iProver_top
% 2.63/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3639,c_29,c_1886,c_1889,c_1892,c_2305,c_4771]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_6083,plain,
% 2.63/1.00      ( r1_tarski(sK3,sK2) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2031,c_6073]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8123,plain,
% 2.63/1.00      ( v2_tops_1(sK2,sK1) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_5461,c_29,c_1886,c_1889,c_1892,c_2305,c_4771]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8128,plain,
% 2.63/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_8123,c_2709]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3543,plain,
% 2.63/1.00      ( k1_tops_1(sK1,sK2) = sK3
% 2.63/1.00      | v2_tops_1(sK2,sK1) != iProver_top
% 2.63/1.00      | r1_tarski(k1_tops_1(sK1,sK2),sK3) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3538,c_1727]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5931,plain,
% 2.63/1.00      ( k1_tops_1(sK1,sK2) = sK3
% 2.63/1.00      | r1_tarski(k1_tops_1(sK1,sK2),sK3) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3543,c_29,c_1886,c_1889,c_1892,c_2305,c_4771]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8169,plain,
% 2.63/1.00      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_8128,c_5931]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8877,plain,
% 2.63/1.00      ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_8169,c_24,c_29,c_706,c_1886,c_1889,c_1892,c_2305,c_2709,
% 2.63/1.00                 c_4771]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1,plain,
% 2.63/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1729,plain,
% 2.63/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.63/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_7,plain,
% 2.63/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8,plain,
% 2.63/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_338,plain,
% 2.63/1.00      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_339,plain,
% 2.63/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_13,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.63/1.00      | ~ r2_hidden(X2,X0)
% 2.63/1.00      | ~ v1_xboole_0(X1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_195,plain,
% 2.63/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.63/1.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_196,plain,
% 2.63/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_195]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_247,plain,
% 2.63/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.63/1.00      inference(bin_hyper_res,[status(thm)],[c_13,c_196]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_353,plain,
% 2.63/1.00      ( ~ r2_hidden(X0,X1)
% 2.63/1.00      | ~ r1_tarski(X1,X2)
% 2.63/1.00      | ~ r1_tarski(X3,k1_xboole_0)
% 2.63/1.00      | X2 != X3 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_339,c_247]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_354,plain,
% 2.63/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ r1_tarski(X2,k1_xboole_0) ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1715,plain,
% 2.63/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.63/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.63/1.00      | r1_tarski(X2,k1_xboole_0) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2732,plain,
% 2.63/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.63/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1726,c_1715]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4518,plain,
% 2.63/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.63/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1729,c_2732]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4528,plain,
% 2.63/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1726,c_4518]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8882,plain,
% 2.63/1.00      ( $false ),
% 2.63/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8877,c_4528]) ).
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  ------                               Statistics
% 2.63/1.00  
% 2.63/1.00  ------ General
% 2.63/1.00  
% 2.63/1.00  abstr_ref_over_cycles:                  0
% 2.63/1.00  abstr_ref_under_cycles:                 0
% 2.63/1.00  gc_basic_clause_elim:                   0
% 2.63/1.00  forced_gc_time:                         0
% 2.63/1.00  parsing_time:                           0.009
% 2.63/1.00  unif_index_cands_time:                  0.
% 2.63/1.00  unif_index_add_time:                    0.
% 2.63/1.00  orderings_time:                         0.
% 2.63/1.00  out_proof_time:                         0.012
% 2.63/1.00  total_time:                             0.229
% 2.63/1.00  num_of_symbols:                         49
% 2.63/1.00  num_of_terms:                           4652
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing
% 2.63/1.00  
% 2.63/1.00  num_of_splits:                          0
% 2.63/1.00  num_of_split_atoms:                     0
% 2.63/1.00  num_of_reused_defs:                     0
% 2.63/1.00  num_eq_ax_congr_red:                    18
% 2.63/1.00  num_of_sem_filtered_clauses:            1
% 2.63/1.00  num_of_subtypes:                        0
% 2.63/1.00  monotx_restored_types:                  0
% 2.63/1.00  sat_num_of_epr_types:                   0
% 2.63/1.00  sat_num_of_non_cyclic_types:            0
% 2.63/1.00  sat_guarded_non_collapsed_types:        0
% 2.63/1.00  num_pure_diseq_elim:                    0
% 2.63/1.00  simp_replaced_by:                       0
% 2.63/1.00  res_preprocessed:                       113
% 2.63/1.00  prep_upred:                             0
% 2.63/1.00  prep_unflattend:                        26
% 2.63/1.00  smt_new_axioms:                         0
% 2.63/1.00  pred_elim_cands:                        5
% 2.63/1.00  pred_elim:                              4
% 2.63/1.00  pred_elim_cl:                           4
% 2.63/1.00  pred_elim_cycles:                       8
% 2.63/1.00  merged_defs:                            8
% 2.63/1.00  merged_defs_ncl:                        0
% 2.63/1.00  bin_hyper_res:                          9
% 2.63/1.00  prep_cycles:                            4
% 2.63/1.00  pred_elim_time:                         0.011
% 2.63/1.00  splitting_time:                         0.
% 2.63/1.00  sem_filter_time:                        0.
% 2.63/1.00  monotx_time:                            0.001
% 2.63/1.00  subtype_inf_time:                       0.
% 2.63/1.00  
% 2.63/1.00  ------ Problem properties
% 2.63/1.00  
% 2.63/1.00  clauses:                                22
% 2.63/1.00  conjectures:                            6
% 2.63/1.00  epr:                                    8
% 2.63/1.00  horn:                                   20
% 2.63/1.00  ground:                                 5
% 2.63/1.00  unary:                                  4
% 2.63/1.00  binary:                                 10
% 2.63/1.00  lits:                                   52
% 2.63/1.00  lits_eq:                                6
% 2.63/1.00  fd_pure:                                0
% 2.63/1.00  fd_pseudo:                              0
% 2.63/1.00  fd_cond:                                1
% 2.63/1.00  fd_pseudo_cond:                         1
% 2.63/1.00  ac_symbols:                             0
% 2.63/1.00  
% 2.63/1.00  ------ Propositional Solver
% 2.63/1.00  
% 2.63/1.00  prop_solver_calls:                      29
% 2.63/1.00  prop_fast_solver_calls:                 1096
% 2.63/1.00  smt_solver_calls:                       0
% 2.63/1.00  smt_fast_solver_calls:                  0
% 2.63/1.00  prop_num_of_clauses:                    2949
% 2.63/1.00  prop_preprocess_simplified:             6523
% 2.63/1.00  prop_fo_subsumed:                       49
% 2.63/1.00  prop_solver_time:                       0.
% 2.63/1.00  smt_solver_time:                        0.
% 2.63/1.00  smt_fast_solver_time:                   0.
% 2.63/1.00  prop_fast_solver_time:                  0.
% 2.63/1.00  prop_unsat_core_time:                   0.
% 2.63/1.00  
% 2.63/1.00  ------ QBF
% 2.63/1.00  
% 2.63/1.00  qbf_q_res:                              0
% 2.63/1.00  qbf_num_tautologies:                    0
% 2.63/1.00  qbf_prep_cycles:                        0
% 2.63/1.00  
% 2.63/1.00  ------ BMC1
% 2.63/1.00  
% 2.63/1.00  bmc1_current_bound:                     -1
% 2.63/1.00  bmc1_last_solved_bound:                 -1
% 2.63/1.00  bmc1_unsat_core_size:                   -1
% 2.63/1.00  bmc1_unsat_core_parents_size:           -1
% 2.63/1.00  bmc1_merge_next_fun:                    0
% 2.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation
% 2.63/1.00  
% 2.63/1.00  inst_num_of_clauses:                    781
% 2.63/1.00  inst_num_in_passive:                    169
% 2.63/1.00  inst_num_in_active:                     377
% 2.63/1.00  inst_num_in_unprocessed:                236
% 2.63/1.00  inst_num_of_loops:                      520
% 2.63/1.00  inst_num_of_learning_restarts:          0
% 2.63/1.00  inst_num_moves_active_passive:          139
% 2.63/1.00  inst_lit_activity:                      0
% 2.63/1.00  inst_lit_activity_moves:                0
% 2.63/1.00  inst_num_tautologies:                   0
% 2.63/1.00  inst_num_prop_implied:                  0
% 2.63/1.00  inst_num_existing_simplified:           0
% 2.63/1.00  inst_num_eq_res_simplified:             0
% 2.63/1.00  inst_num_child_elim:                    0
% 2.63/1.00  inst_num_of_dismatching_blockings:      397
% 2.63/1.00  inst_num_of_non_proper_insts:           1098
% 2.63/1.00  inst_num_of_duplicates:                 0
% 2.63/1.00  inst_inst_num_from_inst_to_res:         0
% 2.63/1.00  inst_dismatching_checking_time:         0.
% 2.63/1.00  
% 2.63/1.00  ------ Resolution
% 2.63/1.00  
% 2.63/1.00  res_num_of_clauses:                     0
% 2.63/1.00  res_num_in_passive:                     0
% 2.63/1.00  res_num_in_active:                      0
% 2.63/1.00  res_num_of_loops:                       117
% 2.63/1.00  res_forward_subset_subsumed:            70
% 2.63/1.00  res_backward_subset_subsumed:           2
% 2.63/1.00  res_forward_subsumed:                   0
% 2.63/1.00  res_backward_subsumed:                  0
% 2.63/1.00  res_forward_subsumption_resolution:     0
% 2.63/1.00  res_backward_subsumption_resolution:    0
% 2.63/1.00  res_clause_to_clause_subsumption:       1065
% 2.63/1.00  res_orphan_elimination:                 0
% 2.63/1.00  res_tautology_del:                      108
% 2.63/1.00  res_num_eq_res_simplified:              0
% 2.63/1.00  res_num_sel_changes:                    0
% 2.63/1.00  res_moves_from_active_to_pass:          0
% 2.63/1.00  
% 2.63/1.00  ------ Superposition
% 2.63/1.00  
% 2.63/1.00  sup_time_total:                         0.
% 2.63/1.00  sup_time_generating:                    0.
% 2.63/1.00  sup_time_sim_full:                      0.
% 2.63/1.00  sup_time_sim_immed:                     0.
% 2.63/1.00  
% 2.63/1.00  sup_num_of_clauses:                     157
% 2.63/1.00  sup_num_in_active:                      78
% 2.63/1.00  sup_num_in_passive:                     79
% 2.63/1.00  sup_num_of_loops:                       103
% 2.63/1.00  sup_fw_superposition:                   117
% 2.63/1.00  sup_bw_superposition:                   131
% 2.63/1.00  sup_immediate_simplified:               29
% 2.63/1.00  sup_given_eliminated:                   1
% 2.63/1.00  comparisons_done:                       0
% 2.63/1.00  comparisons_avoided:                    0
% 2.63/1.00  
% 2.63/1.00  ------ Simplifications
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  sim_fw_subset_subsumed:                 16
% 2.63/1.00  sim_bw_subset_subsumed:                 9
% 2.63/1.00  sim_fw_subsumed:                        17
% 2.63/1.00  sim_bw_subsumed:                        2
% 2.63/1.00  sim_fw_subsumption_res:                 4
% 2.63/1.00  sim_bw_subsumption_res:                 0
% 2.63/1.00  sim_tautology_del:                      15
% 2.63/1.00  sim_eq_tautology_del:                   5
% 2.63/1.00  sim_eq_res_simp:                        0
% 2.63/1.00  sim_fw_demodulated:                     0
% 2.63/1.00  sim_bw_demodulated:                     23
% 2.63/1.00  sim_light_normalised:                   11
% 2.63/1.00  sim_joinable_taut:                      0
% 2.63/1.00  sim_joinable_simp:                      0
% 2.63/1.00  sim_ac_normalised:                      0
% 2.63/1.00  sim_smt_subsumption:                    0
% 2.63/1.00  
%------------------------------------------------------------------------------
