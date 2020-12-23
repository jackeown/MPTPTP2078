%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:09 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  169 (1723 expanded)
%              Number of clauses        :  107 ( 444 expanded)
%              Number of leaves         :   15 ( 415 expanded)
%              Depth                    :   30
%              Number of atoms          :  707 (14905 expanded)
%              Number of equality atoms :  215 (2583 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK4
        & v3_pre_topc(sK4,X0)
        & r1_tarski(sK4,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
              & r1_tarski(X2,sK3)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tops_1(sK3,X0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,X0)
              | ~ r1_tarski(X3,sK3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v2_tops_1(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
                & v3_pre_topc(X2,sK2)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
            | ~ v2_tops_1(X1,sK2) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK2)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | v2_tops_1(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ( k1_xboole_0 != sK4
        & v3_pre_topc(sK4,sK2)
        & r1_tarski(sK4,sK3)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v2_tops_1(sK3,sK2) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK2)
          | ~ r1_tarski(X3,sK3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v2_tops_1(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f50,f53,f52,f51])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                & r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,
    ( r1_tarski(sK4,sK3)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,
    ( k1_xboole_0 != sK4
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2538,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2521,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_2510,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_3083,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_2510])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2535,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4102,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_2535])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2533,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6017,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4102,c_2533])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2775,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_2776,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2775])).

cnf(c_23,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_640,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_641,plain,
    ( ~ v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_2512,plain,
    ( k1_tops_1(sK2,X0) = k1_xboole_0
    | v2_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_3582,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_2512])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,k1_tops_1(sK2,X0)) = k1_tops_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_2509,plain,
    ( k1_tops_1(sK2,k1_tops_1(sK2,X0)) = k1_tops_1(sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_3290,plain,
    ( k1_tops_1(sK2,k1_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2521,c_2509])).

cnf(c_20,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_448,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_449,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_30])).

cnf(c_454,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_694,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_454])).

cnf(c_695,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_1775,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_695])).

cnf(c_2507,plain,
    ( k1_tops_1(sK2,X0) != X0
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_1776,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_695])).

cnf(c_1806,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_1807,plain,
    ( k1_tops_1(sK2,X0) != X0
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_695])).

cnf(c_2508,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_2962,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_2508])).

cnf(c_3017,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top
    | k1_tops_1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_1806,c_1807,c_2962])).

cnf(c_3018,plain,
    ( k1_tops_1(sK2,X0) != X0
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3017])).

cnf(c_3303,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3018])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2529,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3655,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_2529])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2883,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4449,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2883])).

cnf(c_4450,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4449])).

cnf(c_3123,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK2))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4267,plain,
    ( r1_tarski(X0,u1_struct_0(sK2))
    | ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3123])).

cnf(c_5692,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4267])).

cnf(c_5693,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5692])).

cnf(c_6451,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_34,c_2776,c_3655,c_4450,c_5693])).

cnf(c_2530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_28,negated_conjecture,
    ( v2_tops_1(sK3,sK2)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2522,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3688,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2522])).

cnf(c_4268,plain,
    ( r1_tarski(X0,u1_struct_0(sK2)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4267])).

cnf(c_5619,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v2_tops_1(sK3,sK2) = iProver_top
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3688,c_3655,c_4268])).

cnf(c_5620,plain,
    ( k1_xboole_0 = X0
    | v2_tops_1(sK3,sK2) = iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5619])).

cnf(c_6456,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6451,c_5620])).

cnf(c_6586,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6017,c_34,c_2776,c_3582,c_6456])).

cnf(c_27,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2523,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_536,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_537,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_30])).

cnf(c_540,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_2516,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_4009,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2523,c_2516])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | v3_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_999,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k1_tops_1(sK2,X1))
    | ~ r1_tarski(X0,X1)
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_540])).

cnf(c_1000,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ r2_hidden(X1,sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tops_1(sK3,sK2)
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ r2_hidden(X1,sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_27])).

cnf(c_1005,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ r2_hidden(X1,sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(renaming,[status(thm)],[c_1004])).

cnf(c_1006,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_4762,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4009,c_1006])).

cnf(c_4775,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_4762])).

cnf(c_26,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4943,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4775,c_39])).

cnf(c_4944,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4943])).

cnf(c_6591,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6586,c_4944])).

cnf(c_22,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_655,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_656,plain,
    ( v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_2772,plain,
    ( v2_tops_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_2773,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2772])).

cnf(c_8271,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6591,c_34,c_2773,c_2776,c_3582,c_6456])).

cnf(c_8279,plain,
    ( r2_hidden(sK0(sK4,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_8271])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2539,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8631,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_2539])).

cnf(c_8690,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8631,c_2533])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_656])).

cnf(c_887,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,sK3) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_889,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8690,c_6586,c_889])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.21/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/1.00  
% 3.21/1.00  ------  iProver source info
% 3.21/1.00  
% 3.21/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.21/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/1.00  git: non_committed_changes: false
% 3.21/1.00  git: last_make_outside_of_git: false
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     num_symb
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       true
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  ------ Parsing...
% 3.21/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/1.00  ------ Proving...
% 3.21/1.00  ------ Problem Properties 
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  clauses                                 34
% 3.21/1.00  conjectures                             6
% 3.21/1.00  EPR                                     10
% 3.21/1.00  Horn                                    30
% 3.21/1.00  unary                                   4
% 3.21/1.00  binary                                  17
% 3.21/1.00  lits                                    84
% 3.21/1.00  lits eq                                 8
% 3.21/1.00  fd_pure                                 0
% 3.21/1.00  fd_pseudo                               0
% 3.21/1.00  fd_cond                                 2
% 3.21/1.00  fd_pseudo_cond                          0
% 3.21/1.00  AC symbols                              0
% 3.21/1.00  
% 3.21/1.00  ------ Schedule dynamic 5 is on 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  Current options:
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     none
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       false
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ Proving...
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS status Theorem for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  fof(f1,axiom,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f20,plain,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f1])).
% 3.21/1.00  
% 3.21/1.00  fof(f38,plain,(
% 3.21/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(nnf_transformation,[],[f20])).
% 3.21/1.00  
% 3.21/1.00  fof(f39,plain,(
% 3.21/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(rectify,[],[f38])).
% 3.21/1.00  
% 3.21/1.00  fof(f40,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f41,plain,(
% 3.21/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.21/1.00  
% 3.21/1.00  fof(f56,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f41])).
% 3.21/1.00  
% 3.21/1.00  fof(f18,conjecture,(
% 3.21/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f19,negated_conjecture,(
% 3.21/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 3.21/1.00    inference(negated_conjecture,[],[f18])).
% 3.21/1.00  
% 3.21/1.00  fof(f36,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f19])).
% 3.21/1.00  
% 3.21/1.00  fof(f37,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.21/1.00    inference(flattening,[],[f36])).
% 3.21/1.00  
% 3.21/1.00  fof(f48,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.21/1.00    inference(nnf_transformation,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f49,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.21/1.00    inference(flattening,[],[f48])).
% 3.21/1.00  
% 3.21/1.00  fof(f50,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.21/1.00    inference(rectify,[],[f49])).
% 3.21/1.00  
% 3.21/1.00  fof(f53,plain,(
% 3.21/1.00    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK4 & v3_pre_topc(sK4,X0) & r1_tarski(sK4,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f52,plain,(
% 3.21/1.00    ( ! [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(sK3,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f51,plain,(
% 3.21/1.00    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f54,plain,(
% 3.21/1.00    (((k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f50,f53,f52,f51])).
% 3.21/1.00  
% 3.21/1.00  fof(f83,plain,(
% 3.21/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f14,axiom,(
% 3.21/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f30,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/1.00    inference(ennf_transformation,[],[f14])).
% 3.21/1.00  
% 3.21/1.00  fof(f71,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f30])).
% 3.21/1.00  
% 3.21/1.00  fof(f82,plain,(
% 3.21/1.00    l1_pre_topc(sK2)),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f4,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f22,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(ennf_transformation,[],[f4])).
% 3.21/1.00  
% 3.21/1.00  fof(f23,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.21/1.00    inference(flattening,[],[f22])).
% 3.21/1.00  
% 3.21/1.00  fof(f60,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f23])).
% 3.21/1.00  
% 3.21/1.00  fof(f6,axiom,(
% 3.21/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f24,plain,(
% 3.21/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.21/1.00    inference(ennf_transformation,[],[f6])).
% 3.21/1.00  
% 3.21/1.00  fof(f62,plain,(
% 3.21/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f24])).
% 3.21/1.00  
% 3.21/1.00  fof(f17,axiom,(
% 3.21/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f35,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/1.00    inference(ennf_transformation,[],[f17])).
% 3.21/1.00  
% 3.21/1.00  fof(f47,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.21/1.00    inference(nnf_transformation,[],[f35])).
% 3.21/1.00  
% 3.21/1.00  fof(f79,plain,(
% 3.21/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f47])).
% 3.21/1.00  
% 3.21/1.00  fof(f13,axiom,(
% 3.21/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f28,plain,(
% 3.21/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f13])).
% 3.21/1.00  
% 3.21/1.00  fof(f29,plain,(
% 3.21/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.21/1.00    inference(flattening,[],[f28])).
% 3.21/1.00  
% 3.21/1.00  fof(f70,plain,(
% 3.21/1.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f29])).
% 3.21/1.00  
% 3.21/1.00  fof(f16,axiom,(
% 3.21/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f33,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f16])).
% 3.21/1.00  
% 3.21/1.00  fof(f34,plain,(
% 3.21/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/1.00    inference(flattening,[],[f33])).
% 3.21/1.00  
% 3.21/1.00  fof(f78,plain,(
% 3.21/1.00    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f34])).
% 3.21/1.00  
% 3.21/1.00  fof(f81,plain,(
% 3.21/1.00    v2_pre_topc(sK2)),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f10,axiom,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f42,plain,(
% 3.21/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.21/1.00    inference(nnf_transformation,[],[f10])).
% 3.21/1.00  
% 3.21/1.00  fof(f66,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f42])).
% 3.21/1.00  
% 3.21/1.00  fof(f67,plain,(
% 3.21/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f42])).
% 3.21/1.00  
% 3.21/1.00  fof(f84,plain,(
% 3.21/1.00    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f85,plain,(
% 3.21/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tops_1(sK3,sK2)),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f15,axiom,(
% 3.21/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f31,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f15])).
% 3.21/1.00  
% 3.21/1.00  fof(f32,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/1.00    inference(flattening,[],[f31])).
% 3.21/1.00  
% 3.21/1.00  fof(f43,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/1.00    inference(nnf_transformation,[],[f32])).
% 3.21/1.00  
% 3.21/1.00  fof(f44,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/1.00    inference(rectify,[],[f43])).
% 3.21/1.00  
% 3.21/1.00  fof(f45,plain,(
% 3.21/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f46,plain,(
% 3.21/1.00    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 3.21/1.00  
% 3.21/1.00  fof(f76,plain,(
% 3.21/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f46])).
% 3.21/1.00  
% 3.21/1.00  fof(f87,plain,(
% 3.21/1.00    v3_pre_topc(sK4,sK2) | ~v2_tops_1(sK3,sK2)),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f86,plain,(
% 3.21/1.00    r1_tarski(sK4,sK3) | ~v2_tops_1(sK3,sK2)),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  fof(f80,plain,(
% 3.21/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f47])).
% 3.21/1.00  
% 3.21/1.00  fof(f57,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f41])).
% 3.21/1.00  
% 3.21/1.00  fof(f88,plain,(
% 3.21/1.00    k1_xboole_0 != sK4 | ~v2_tops_1(sK3,sK2)),
% 3.21/1.00    inference(cnf_transformation,[],[f54])).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2538,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_29,negated_conjecture,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.21/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2521,plain,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_14,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.21/1.00      | ~ l1_pre_topc(X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_30,negated_conjecture,
% 3.21/1.00      ( l1_pre_topc(sK2) ),
% 3.21/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_670,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.21/1.00      | sK2 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_671,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,X0),X0) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_670]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2510,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,X0),X0) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3083,plain,
% 3.21/1.00      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2521,c_2510]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.21/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2535,plain,
% 3.21/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.21/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X2) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4102,plain,
% 3.21/1.00      ( r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top
% 3.21/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3083,c_2535]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2533,plain,
% 3.21/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6017,plain,
% 3.21/1.00      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.21/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4102,c_2533]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_34,plain,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2775,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_671]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2776,plain,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2775]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_23,plain,
% 3.21/1.00      ( ~ v2_tops_1(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ l1_pre_topc(X1)
% 3.21/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_640,plain,
% 3.21/1.00      ( ~ v2_tops_1(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.21/1.00      | sK2 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_641,plain,
% 3.21/1.00      ( ~ v2_tops_1(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,X0) = k1_xboole_0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_640]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2512,plain,
% 3.21/1.00      ( k1_tops_1(sK2,X0) = k1_xboole_0
% 3.21/1.00      | v2_tops_1(X0,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3582,plain,
% 3.21/1.00      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.21/1.00      | v2_tops_1(sK3,sK2) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2521,c_2512]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_13,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ l1_pre_topc(X1)
% 3.21/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_682,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 3.21/1.00      | sK2 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_683,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,k1_tops_1(sK2,X0)) = k1_tops_1(sK2,X0) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_682]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2509,plain,
% 3.21/1.00      ( k1_tops_1(sK2,k1_tops_1(sK2,X0)) = k1_tops_1(sK2,X0)
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3290,plain,
% 3.21/1.00      ( k1_tops_1(sK2,k1_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2521,c_2509]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_20,plain,
% 3.21/1.00      ( v3_pre_topc(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.21/1.00      | ~ v2_pre_topc(X1)
% 3.21/1.00      | ~ l1_pre_topc(X1)
% 3.21/1.00      | ~ l1_pre_topc(X3)
% 3.21/1.00      | k1_tops_1(X1,X0) != X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_31,negated_conjecture,
% 3.21/1.00      ( v2_pre_topc(sK2) ),
% 3.21/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_448,plain,
% 3.21/1.00      ( v3_pre_topc(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.21/1.00      | ~ l1_pre_topc(X1)
% 3.21/1.00      | ~ l1_pre_topc(X3)
% 3.21/1.00      | k1_tops_1(X1,X0) != X0
% 3.21/1.00      | sK2 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_449,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ l1_pre_topc(X2)
% 3.21/1.00      | ~ l1_pre_topc(sK2)
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_448]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_453,plain,
% 3.21/1.00      ( ~ l1_pre_topc(X2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.21/1.00      | v3_pre_topc(X0,sK2)
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_449,c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_454,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ l1_pre_topc(X2)
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0 ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_453]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_694,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0
% 3.21/1.00      | sK2 != X2 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_454]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_695,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_694]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1775,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0
% 3.21/1.00      | ~ sP1_iProver_split ),
% 3.21/1.00      inference(splitting,
% 3.21/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.21/1.00                [c_695]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2507,plain,
% 3.21/1.00      ( k1_tops_1(sK2,X0) != X0
% 3.21/1.00      | v3_pre_topc(X0,sK2) = iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | sP1_iProver_split != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1776,plain,
% 3.21/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.21/1.00      inference(splitting,
% 3.21/1.00                [splitting(split),new_symbols(definition,[])],
% 3.21/1.00                [c_695]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1806,plain,
% 3.21/1.00      ( sP1_iProver_split = iProver_top
% 3.21/1.00      | sP0_iProver_split = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1807,plain,
% 3.21/1.00      ( k1_tops_1(sK2,X0) != X0
% 3.21/1.00      | v3_pre_topc(X0,sK2) = iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | sP1_iProver_split != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1774,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ sP0_iProver_split ),
% 3.21/1.00      inference(splitting,
% 3.21/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.21/1.00                [c_695]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2508,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | sP0_iProver_split != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2962,plain,
% 3.21/1.00      ( sP0_iProver_split != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2521,c_2508]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3017,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | v3_pre_topc(X0,sK2) = iProver_top
% 3.21/1.00      | k1_tops_1(sK2,X0) != X0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2507,c_1806,c_1807,c_2962]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3018,plain,
% 3.21/1.00      ( k1_tops_1(sK2,X0) != X0
% 3.21/1.00      | v3_pre_topc(X0,sK2) = iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_3017]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3303,plain,
% 3.21/1.00      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top
% 3.21/1.00      | m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3290,c_3018]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2529,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3655,plain,
% 3.21/1.00      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2521,c_2529]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2883,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4449,plain,
% 3.21/1.00      ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2883]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4450,plain,
% 3.21/1.00      ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_4449]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3123,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1)
% 3.21/1.00      | ~ r1_tarski(X1,u1_struct_0(sK2))
% 3.21/1.00      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4267,plain,
% 3.21/1.00      ( r1_tarski(X0,u1_struct_0(sK2))
% 3.21/1.00      | ~ r1_tarski(X0,sK3)
% 3.21/1.00      | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_3123]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5692,plain,
% 3.21/1.00      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2))
% 3.21/1.00      | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 3.21/1.00      | ~ r1_tarski(sK3,u1_struct_0(sK2)) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4267]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5693,plain,
% 3.21/1.00      ( r1_tarski(k1_tops_1(sK2,sK3),u1_struct_0(sK2)) = iProver_top
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top
% 3.21/1.00      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_5692]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6451,plain,
% 3.21/1.00      ( v3_pre_topc(k1_tops_1(sK2,sK3),sK2) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3303,c_34,c_2776,c_3655,c_4450,c_5693]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2530,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_28,negated_conjecture,
% 3.21/1.00      ( v2_tops_1(sK3,sK2)
% 3.21/1.00      | ~ v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ r1_tarski(X0,sK3)
% 3.21/1.00      | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2522,plain,
% 3.21/1.00      ( k1_xboole_0 = X0
% 3.21/1.00      | v2_tops_1(sK3,sK2) = iProver_top
% 3.21/1.00      | v3_pre_topc(X0,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3688,plain,
% 3.21/1.00      ( k1_xboole_0 = X0
% 3.21/1.00      | v2_tops_1(sK3,sK2) = iProver_top
% 3.21/1.00      | v3_pre_topc(X0,sK2) != iProver_top
% 3.21/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 3.21/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2530,c_2522]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4268,plain,
% 3.21/1.00      ( r1_tarski(X0,u1_struct_0(sK2)) = iProver_top
% 3.21/1.00      | r1_tarski(X0,sK3) != iProver_top
% 3.21/1.00      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_4267]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5619,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.21/1.00      | v2_tops_1(sK3,sK2) = iProver_top
% 3.21/1.00      | k1_xboole_0 = X0
% 3.21/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3688,c_3655,c_4268]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5620,plain,
% 3.21/1.00      ( k1_xboole_0 = X0
% 3.21/1.00      | v2_tops_1(sK3,sK2) = iProver_top
% 3.21/1.00      | v3_pre_topc(X0,sK2) != iProver_top
% 3.21/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_5619]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6456,plain,
% 3.21/1.00      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.21/1.00      | v2_tops_1(sK3,sK2) = iProver_top
% 3.21/1.00      | r1_tarski(k1_tops_1(sK2,sK3),sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_6451,c_5620]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6586,plain,
% 3.21/1.00      ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6017,c_34,c_2776,c_3582,c_6456]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_27,negated_conjecture,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2)
% 3.21/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.21/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2523,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_15,plain,
% 3.21/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ r2_hidden(X3,X0)
% 3.21/1.00      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.21/1.00      | ~ r1_tarski(X0,X2)
% 3.21/1.00      | ~ v2_pre_topc(X1)
% 3.21/1.00      | ~ l1_pre_topc(X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_536,plain,
% 3.21/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ r2_hidden(X3,X0)
% 3.21/1.00      | r2_hidden(X3,k1_tops_1(X1,X2))
% 3.21/1.00      | ~ r1_tarski(X0,X2)
% 3.21/1.00      | ~ l1_pre_topc(X1)
% 3.21/1.00      | sK2 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_537,plain,
% 3.21/1.00      ( ~ v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.21/1.00      | ~ r1_tarski(X0,X1)
% 3.21/1.00      | ~ l1_pre_topc(sK2) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_536]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_539,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1)
% 3.21/1.00      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ v3_pre_topc(X0,sK2) ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_537,c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_540,plain,
% 3.21/1.00      ( ~ v3_pre_topc(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.21/1.00      | ~ r1_tarski(X0,X1) ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_539]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2516,plain,
% 3.21/1.00      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.21/1.00      | r2_hidden(X2,k1_tops_1(sK2,X1)) = iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4009,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 3.21/1.00      | r2_hidden(X1,sK4) != iProver_top
% 3.21/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2523,c_2516]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_25,negated_conjecture,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2) | v3_pre_topc(sK4,sK2) ),
% 3.21/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_999,plain,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | r2_hidden(X2,k1_tops_1(sK2,X1))
% 3.21/1.00      | ~ r1_tarski(X0,X1)
% 3.21/1.00      | sK2 != sK2
% 3.21/1.00      | sK4 != X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_540]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1000,plain,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.21/1.00      | ~ r2_hidden(X1,sK4)
% 3.21/1.00      | ~ r1_tarski(sK4,X0) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_999]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1004,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | ~ v2_tops_1(sK3,sK2)
% 3.21/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.21/1.00      | ~ r2_hidden(X1,sK4)
% 3.21/1.00      | ~ r1_tarski(sK4,X0) ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_1000,c_27]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1005,plain,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 3.21/1.00      | ~ r2_hidden(X1,sK4)
% 3.21/1.00      | ~ r1_tarski(sK4,X0) ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_1004]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1006,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 3.21/1.00      | r2_hidden(X1,sK4) != iProver_top
% 3.21/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4762,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.21/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0)) = iProver_top
% 3.21/1.00      | r2_hidden(X1,sK4) != iProver_top
% 3.21/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4009,c_1006]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4775,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.21/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.21/1.00      | r1_tarski(sK4,sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2521,c_4762]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_26,negated_conjecture,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2) | r1_tarski(sK4,sK3) ),
% 3.21/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_39,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | r1_tarski(sK4,sK3) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4943,plain,
% 3.21/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.21/1.00      | v2_tops_1(sK3,sK2) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4775,c_39]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4944,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.21/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_4943]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6591,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_6586,c_4944]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_22,plain,
% 3.21/1.00      ( v2_tops_1(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | ~ l1_pre_topc(X1)
% 3.21/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_655,plain,
% 3.21/1.00      ( v2_tops_1(X0,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.21/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.21/1.00      | sK2 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_656,plain,
% 3.21/1.00      ( v2_tops_1(X0,sK2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,X0) != k1_xboole_0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_655]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2772,plain,
% 3.21/1.00      ( v2_tops_1(sK3,sK2)
% 3.21/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,sK3) != k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_656]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2773,plain,
% 3.21/1.00      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 3.21/1.00      | v2_tops_1(sK3,sK2) = iProver_top
% 3.21/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2772]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8271,plain,
% 3.21/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_6591,c_34,c_2773,c_2776,c_3582,c_6456]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8279,plain,
% 3.21/1.00      ( r2_hidden(sK0(sK4,X0),k1_xboole_0) = iProver_top
% 3.21/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2538,c_8271]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_0,plain,
% 3.21/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2539,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8631,plain,
% 3.21/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_8279,c_2539]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8690,plain,
% 3.21/1.00      ( sK4 = k1_xboole_0 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_8631,c_2533]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_24,negated_conjecture,
% 3.21/1.00      ( ~ v2_tops_1(sK3,sK2) | k1_xboole_0 != sK4 ),
% 3.21/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_886,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,X0) != k1_xboole_0
% 3.21/1.00      | sK2 != sK2
% 3.21/1.00      | sK3 != X0
% 3.21/1.00      | sK4 != k1_xboole_0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_656]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_887,plain,
% 3.21/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.21/1.00      | k1_tops_1(sK2,sK3) != k1_xboole_0
% 3.21/1.00      | sK4 != k1_xboole_0 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_886]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_889,plain,
% 3.21/1.00      ( k1_tops_1(sK2,sK3) != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_887,c_29]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(contradiction,plain,
% 3.21/1.00      ( $false ),
% 3.21/1.00      inference(minisat,[status(thm)],[c_8690,c_6586,c_889]) ).
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  ------                               Statistics
% 3.21/1.00  
% 3.21/1.00  ------ General
% 3.21/1.00  
% 3.21/1.00  abstr_ref_over_cycles:                  0
% 3.21/1.00  abstr_ref_under_cycles:                 0
% 3.21/1.00  gc_basic_clause_elim:                   0
% 3.21/1.00  forced_gc_time:                         0
% 3.21/1.00  parsing_time:                           0.018
% 3.21/1.00  unif_index_cands_time:                  0.
% 3.21/1.00  unif_index_add_time:                    0.
% 3.21/1.00  orderings_time:                         0.
% 3.21/1.00  out_proof_time:                         0.012
% 3.21/1.00  total_time:                             0.315
% 3.21/1.00  num_of_symbols:                         54
% 3.21/1.00  num_of_terms:                           6045
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing
% 3.21/1.00  
% 3.21/1.00  num_of_splits:                          4
% 3.21/1.00  num_of_split_atoms:                     3
% 3.21/1.00  num_of_reused_defs:                     1
% 3.21/1.00  num_eq_ax_congr_red:                    26
% 3.21/1.00  num_of_sem_filtered_clauses:            4
% 3.21/1.00  num_of_subtypes:                        0
% 3.21/1.00  monotx_restored_types:                  0
% 3.21/1.00  sat_num_of_epr_types:                   0
% 3.21/1.00  sat_num_of_non_cyclic_types:            0
% 3.21/1.00  sat_guarded_non_collapsed_types:        0
% 3.21/1.00  num_pure_diseq_elim:                    0
% 3.21/1.00  simp_replaced_by:                       0
% 3.21/1.00  res_preprocessed:                       152
% 3.21/1.00  prep_upred:                             0
% 3.21/1.00  prep_unflattend:                        35
% 3.21/1.00  smt_new_axioms:                         0
% 3.21/1.00  pred_elim_cands:                        5
% 3.21/1.00  pred_elim:                              2
% 3.21/1.00  pred_elim_cl:                           2
% 3.21/1.00  pred_elim_cycles:                       6
% 3.21/1.01  merged_defs:                            8
% 3.21/1.01  merged_defs_ncl:                        0
% 3.21/1.01  bin_hyper_res:                          8
% 3.21/1.01  prep_cycles:                            4
% 3.21/1.01  pred_elim_time:                         0.042
% 3.21/1.01  splitting_time:                         0.
% 3.21/1.01  sem_filter_time:                        0.
% 3.21/1.01  monotx_time:                            0.
% 3.21/1.01  subtype_inf_time:                       0.
% 3.21/1.01  
% 3.21/1.01  ------ Problem properties
% 3.21/1.01  
% 3.21/1.01  clauses:                                34
% 3.21/1.01  conjectures:                            6
% 3.21/1.01  epr:                                    10
% 3.21/1.01  horn:                                   30
% 3.21/1.01  ground:                                 7
% 3.21/1.01  unary:                                  4
% 3.21/1.01  binary:                                 17
% 3.21/1.01  lits:                                   84
% 3.21/1.01  lits_eq:                                8
% 3.21/1.01  fd_pure:                                0
% 3.21/1.01  fd_pseudo:                              0
% 3.21/1.01  fd_cond:                                2
% 3.21/1.01  fd_pseudo_cond:                         0
% 3.21/1.01  ac_symbols:                             0
% 3.21/1.01  
% 3.21/1.01  ------ Propositional Solver
% 3.21/1.01  
% 3.21/1.01  prop_solver_calls:                      27
% 3.21/1.01  prop_fast_solver_calls:                 1388
% 3.21/1.01  smt_solver_calls:                       0
% 3.21/1.01  smt_fast_solver_calls:                  0
% 3.21/1.01  prop_num_of_clauses:                    2975
% 3.21/1.01  prop_preprocess_simplified:             8913
% 3.21/1.01  prop_fo_subsumed:                       49
% 3.21/1.01  prop_solver_time:                       0.
% 3.21/1.01  smt_solver_time:                        0.
% 3.21/1.01  smt_fast_solver_time:                   0.
% 3.21/1.01  prop_fast_solver_time:                  0.
% 3.21/1.01  prop_unsat_core_time:                   0.
% 3.21/1.01  
% 3.21/1.01  ------ QBF
% 3.21/1.01  
% 3.21/1.01  qbf_q_res:                              0
% 3.21/1.01  qbf_num_tautologies:                    0
% 3.21/1.01  qbf_prep_cycles:                        0
% 3.21/1.01  
% 3.21/1.01  ------ BMC1
% 3.21/1.01  
% 3.21/1.01  bmc1_current_bound:                     -1
% 3.21/1.01  bmc1_last_solved_bound:                 -1
% 3.21/1.01  bmc1_unsat_core_size:                   -1
% 3.21/1.01  bmc1_unsat_core_parents_size:           -1
% 3.21/1.01  bmc1_merge_next_fun:                    0
% 3.21/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.01  
% 3.21/1.01  ------ Instantiation
% 3.21/1.01  
% 3.21/1.01  inst_num_of_clauses:                    795
% 3.21/1.01  inst_num_in_passive:                    378
% 3.21/1.01  inst_num_in_active:                     377
% 3.21/1.01  inst_num_in_unprocessed:                40
% 3.21/1.01  inst_num_of_loops:                      480
% 3.21/1.01  inst_num_of_learning_restarts:          0
% 3.21/1.01  inst_num_moves_active_passive:          100
% 3.21/1.01  inst_lit_activity:                      0
% 3.21/1.01  inst_lit_activity_moves:                0
% 3.21/1.01  inst_num_tautologies:                   0
% 3.21/1.01  inst_num_prop_implied:                  0
% 3.21/1.01  inst_num_existing_simplified:           0
% 3.21/1.01  inst_num_eq_res_simplified:             0
% 3.21/1.01  inst_num_child_elim:                    0
% 3.21/1.01  inst_num_of_dismatching_blockings:      325
% 3.21/1.01  inst_num_of_non_proper_insts:           680
% 3.21/1.01  inst_num_of_duplicates:                 0
% 3.21/1.01  inst_inst_num_from_inst_to_res:         0
% 3.21/1.01  inst_dismatching_checking_time:         0.
% 3.21/1.01  
% 3.21/1.01  ------ Resolution
% 3.21/1.01  
% 3.21/1.01  res_num_of_clauses:                     0
% 3.21/1.01  res_num_in_passive:                     0
% 3.21/1.01  res_num_in_active:                      0
% 3.21/1.01  res_num_of_loops:                       156
% 3.21/1.01  res_forward_subset_subsumed:            34
% 3.21/1.01  res_backward_subset_subsumed:           0
% 3.21/1.01  res_forward_subsumed:                   0
% 3.21/1.01  res_backward_subsumed:                  0
% 3.21/1.01  res_forward_subsumption_resolution:     3
% 3.21/1.01  res_backward_subsumption_resolution:    0
% 3.21/1.01  res_clause_to_clause_subsumption:       833
% 3.21/1.01  res_orphan_elimination:                 0
% 3.21/1.01  res_tautology_del:                      59
% 3.21/1.01  res_num_eq_res_simplified:              0
% 3.21/1.01  res_num_sel_changes:                    0
% 3.21/1.01  res_moves_from_active_to_pass:          0
% 3.21/1.01  
% 3.21/1.01  ------ Superposition
% 3.21/1.01  
% 3.21/1.01  sup_time_total:                         0.
% 3.21/1.01  sup_time_generating:                    0.
% 3.21/1.01  sup_time_sim_full:                      0.
% 3.21/1.01  sup_time_sim_immed:                     0.
% 3.21/1.01  
% 3.21/1.01  sup_num_of_clauses:                     154
% 3.21/1.01  sup_num_in_active:                      78
% 3.21/1.01  sup_num_in_passive:                     76
% 3.21/1.01  sup_num_of_loops:                       94
% 3.21/1.01  sup_fw_superposition:                   120
% 3.21/1.01  sup_bw_superposition:                   75
% 3.21/1.01  sup_immediate_simplified:               32
% 3.21/1.01  sup_given_eliminated:                   3
% 3.21/1.01  comparisons_done:                       0
% 3.21/1.01  comparisons_avoided:                    0
% 3.21/1.01  
% 3.21/1.01  ------ Simplifications
% 3.21/1.01  
% 3.21/1.01  
% 3.21/1.01  sim_fw_subset_subsumed:                 10
% 3.21/1.01  sim_bw_subset_subsumed:                 8
% 3.21/1.01  sim_fw_subsumed:                        12
% 3.21/1.01  sim_bw_subsumed:                        1
% 3.21/1.01  sim_fw_subsumption_res:                 1
% 3.21/1.01  sim_bw_subsumption_res:                 0
% 3.21/1.01  sim_tautology_del:                      6
% 3.21/1.01  sim_eq_tautology_del:                   5
% 3.21/1.01  sim_eq_res_simp:                        0
% 3.21/1.01  sim_fw_demodulated:                     0
% 3.21/1.01  sim_bw_demodulated:                     16
% 3.21/1.01  sim_light_normalised:                   10
% 3.21/1.01  sim_joinable_taut:                      0
% 3.21/1.01  sim_joinable_simp:                      0
% 3.21/1.01  sim_ac_normalised:                      0
% 3.21/1.01  sim_smt_subsumption:                    0
% 3.21/1.01  
%------------------------------------------------------------------------------
