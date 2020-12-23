%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:35 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  179 (1233 expanded)
%              Number of clauses        :   80 ( 237 expanded)
%              Number of leaves         :   28 ( 339 expanded)
%              Depth                    :   26
%              Number of atoms          :  568 (9923 expanded)
%              Number of equality atoms :  167 (1229 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK3
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK2,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK2,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK1)
                      | ~ v3_pre_topc(X3,sK1) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK1)
                        & v3_pre_topc(X3,sK1) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( k1_xboole_0 = sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | ~ r2_hidden(sK2,X3)
            | ~ v4_pre_topc(X3,sK1)
            | ~ v3_pre_topc(X3,sK1) )
          & ( ( r2_hidden(sK2,X3)
              & v4_pre_topc(X3,sK1)
              & v3_pre_topc(X3,sK1) )
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f55,f54,f53])).

fof(f97,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(sK2,X3)
      | ~ v4_pre_topc(X3,sK1)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f98,plain,(
    k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    ! [X0] : r1_tarski(sK3,X0) ),
    inference(definition_unfolding,[],[f62,f98])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(sK3,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f79,f98])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f99])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f100])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f101])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f102])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f81,f103])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f104])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f105])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f106,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = sK3 ),
    inference(definition_unfolding,[],[f61,f104,f98,f98])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f108,plain,(
    ! [X0] : k5_xboole_0(X0,sK3) = X0 ),
    inference(definition_unfolding,[],[f63,f98])).

fof(f16,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK3 = X0 ) ),
    inference(definition_unfolding,[],[f80,f98])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1231,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1227,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1223,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2689,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1223])).

cnf(c_24,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_22,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_448,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_449,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_65,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_451,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_31,c_30,c_65])).

cnf(c_470,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0)
    | k2_struct_0(sK1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_451])).

cnf(c_471,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_23,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_62,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_473,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_31,c_30,c_62])).

cnf(c_1212,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_20,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_423,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_20,c_19])).

cnf(c_463,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_423,c_30])).

cnf(c_464,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_1319,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1212,c_464])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_410,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_411,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_68,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_71,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_413,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_32,c_30,c_68,c_71])).

cnf(c_1213,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_1241,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1213,c_464])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1214,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1244,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1214,c_464])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1222,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1985,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1222])).

cnf(c_2090,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1319,c_1241,c_1985])).

cnf(c_2091,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2090])).

cnf(c_6068,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2689,c_2091])).

cnf(c_6596,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6068,c_1231])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1217,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6599,plain,
    ( r1_tarski(sK3,k2_struct_0(sK1)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6596,c_1217])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK3,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1230,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7371,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6599,c_1230])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1225,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1221,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4772,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))) = k3_subset_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1220,c_1221])).

cnf(c_3,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = sK3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5,negated_conjecture,
    ( k5_xboole_0(X0,sK3) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4774,plain,
    ( k3_subset_1(X0,sK3) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4772,c_3,c_5])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k3_subset_1(X1,X2))
    | sK3 = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1219,plain,
    ( sK3 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1744,plain,
    ( sK3 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r1_tarski(k3_subset_1(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1217])).

cnf(c_2225,plain,
    ( sK3 = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k3_subset_1(X0,X1),X0) != iProver_top
    | r2_hidden(k3_subset_1(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1744])).

cnf(c_4900,plain,
    ( sK3 = X0
    | m1_subset_1(X0,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k3_subset_1(X0,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_2225])).

cnf(c_4966,plain,
    ( sK3 = X0
    | m1_subset_1(X0,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4900,c_4774])).

cnf(c_53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_57,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4705,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4706,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4705])).

cnf(c_5095,plain,
    ( sK3 = X0
    | m1_subset_1(X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4966,c_53,c_57,c_4706])).

cnf(c_5103,plain,
    ( sK3 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_5095])).

cnf(c_7373,plain,
    ( k1_zfmisc_1(k2_struct_0(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_7371,c_5103])).

cnf(c_7728,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7373,c_1227])).

cnf(c_1873,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1217])).

cnf(c_7726,plain,
    ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7373,c_1873])).

cnf(c_8509,plain,
    ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7728,c_57,c_7726])).

cnf(c_8516,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1231,c_8509])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:10:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.90/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.98  
% 3.90/0.98  ------  iProver source info
% 3.90/0.98  
% 3.90/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.98  git: non_committed_changes: false
% 3.90/0.98  git: last_make_outside_of_git: false
% 3.90/0.98  
% 3.90/0.98  ------ 
% 3.90/0.98  ------ Parsing...
% 3.90/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.98  ------ Proving...
% 3.90/0.98  ------ Problem Properties 
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  clauses                                 24
% 3.90/0.98  conjectures                             8
% 3.90/0.98  EPR                                     8
% 3.90/0.98  Horn                                    20
% 3.90/0.98  unary                                   9
% 3.90/0.98  binary                                  4
% 3.90/0.98  lits                                    52
% 3.90/0.98  lits eq                                 8
% 3.90/0.98  fd_pure                                 0
% 3.90/0.98  fd_pseudo                               0
% 3.90/0.98  fd_cond                                 1
% 3.90/0.98  fd_pseudo_cond                          3
% 3.90/0.98  AC symbols                              0
% 3.90/0.98  
% 3.90/0.98  ------ Input Options Time Limit: Unbounded
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  ------ 
% 3.90/0.98  Current options:
% 3.90/0.98  ------ 
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  ------ Proving...
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  % SZS status Theorem for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98   Resolution empty clause
% 3.90/0.98  
% 3.90/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  fof(f1,axiom,(
% 3.90/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f44,plain,(
% 3.90/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.90/0.98    inference(nnf_transformation,[],[f1])).
% 3.90/0.98  
% 3.90/0.98  fof(f45,plain,(
% 3.90/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.90/0.98    inference(flattening,[],[f44])).
% 3.90/0.98  
% 3.90/0.98  fof(f58,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.90/0.98    inference(cnf_transformation,[],[f45])).
% 3.90/0.98  
% 3.90/0.98  fof(f112,plain,(
% 3.90/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.90/0.98    inference(equality_resolution,[],[f58])).
% 3.90/0.98  
% 3.90/0.98  fof(f12,axiom,(
% 3.90/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f46,plain,(
% 3.90/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.90/0.98    inference(nnf_transformation,[],[f12])).
% 3.90/0.98  
% 3.90/0.98  fof(f47,plain,(
% 3.90/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.90/0.98    inference(rectify,[],[f46])).
% 3.90/0.98  
% 3.90/0.98  fof(f48,plain,(
% 3.90/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f49,plain,(
% 3.90/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 3.90/0.98  
% 3.90/0.98  fof(f71,plain,(
% 3.90/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.90/0.98    inference(cnf_transformation,[],[f49])).
% 3.90/0.98  
% 3.90/0.98  fof(f114,plain,(
% 3.90/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.90/0.98    inference(equality_resolution,[],[f71])).
% 3.90/0.98  
% 3.90/0.98  fof(f13,axiom,(
% 3.90/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f27,plain,(
% 3.90/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f13])).
% 3.90/0.98  
% 3.90/0.98  fof(f50,plain,(
% 3.90/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.90/0.98    inference(nnf_transformation,[],[f27])).
% 3.90/0.98  
% 3.90/0.98  fof(f75,plain,(
% 3.90/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f50])).
% 3.90/0.98  
% 3.90/0.98  fof(f25,conjecture,(
% 3.90/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f26,negated_conjecture,(
% 3.90/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 3.90/0.98    inference(negated_conjecture,[],[f25])).
% 3.90/0.98  
% 3.90/0.98  fof(f42,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f26])).
% 3.90/0.98  
% 3.90/0.98  fof(f43,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.90/0.98    inference(flattening,[],[f42])).
% 3.90/0.98  
% 3.90/0.98  fof(f51,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.90/0.98    inference(nnf_transformation,[],[f43])).
% 3.90/0.98  
% 3.90/0.98  fof(f52,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.90/0.98    inference(flattening,[],[f51])).
% 3.90/0.98  
% 3.90/0.98  fof(f55,plain,(
% 3.90/0.98    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f54,plain,(
% 3.90/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f53,plain,(
% 3.90/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f56,plain,(
% 3.90/0.98    ((k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f55,f54,f53])).
% 3.90/0.98  
% 3.90/0.98  fof(f97,plain,(
% 3.90/0.98    ( ! [X3] : (r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f23,axiom,(
% 3.90/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f38,plain,(
% 3.90/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f23])).
% 3.90/0.98  
% 3.90/0.98  fof(f39,plain,(
% 3.90/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.98    inference(flattening,[],[f38])).
% 3.90/0.98  
% 3.90/0.98  fof(f87,plain,(
% 3.90/0.98    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f39])).
% 3.90/0.98  
% 3.90/0.98  fof(f90,plain,(
% 3.90/0.98    v2_pre_topc(sK1)),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f91,plain,(
% 3.90/0.98    l1_pre_topc(sK1)),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f24,axiom,(
% 3.90/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f40,plain,(
% 3.90/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f24])).
% 3.90/0.98  
% 3.90/0.98  fof(f41,plain,(
% 3.90/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.90/0.98    inference(flattening,[],[f40])).
% 3.90/0.98  
% 3.90/0.98  fof(f88,plain,(
% 3.90/0.98    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f41])).
% 3.90/0.98  
% 3.90/0.98  fof(f21,axiom,(
% 3.90/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f35,plain,(
% 3.90/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f21])).
% 3.90/0.98  
% 3.90/0.98  fof(f85,plain,(
% 3.90/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f35])).
% 3.90/0.98  
% 3.90/0.98  fof(f20,axiom,(
% 3.90/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f34,plain,(
% 3.90/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f20])).
% 3.90/0.98  
% 3.90/0.98  fof(f84,plain,(
% 3.90/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f34])).
% 3.90/0.98  
% 3.90/0.98  fof(f22,axiom,(
% 3.90/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f36,plain,(
% 3.90/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f22])).
% 3.90/0.98  
% 3.90/0.98  fof(f37,plain,(
% 3.90/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.90/0.98    inference(flattening,[],[f36])).
% 3.90/0.98  
% 3.90/0.98  fof(f86,plain,(
% 3.90/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f37])).
% 3.90/0.98  
% 3.90/0.98  fof(f89,plain,(
% 3.90/0.98    ~v2_struct_0(sK1)),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f92,plain,(
% 3.90/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f74,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f50])).
% 3.90/0.98  
% 3.90/0.98  fof(f19,axiom,(
% 3.90/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f33,plain,(
% 3.90/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.90/0.98    inference(ennf_transformation,[],[f19])).
% 3.90/0.98  
% 3.90/0.98  fof(f83,plain,(
% 3.90/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f33])).
% 3.90/0.98  
% 3.90/0.98  fof(f4,axiom,(
% 3.90/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f62,plain,(
% 3.90/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f4])).
% 3.90/0.98  
% 3.90/0.98  fof(f98,plain,(
% 3.90/0.98    k1_xboole_0 = sK3),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f107,plain,(
% 3.90/0.98    ( ! [X0] : (r1_tarski(sK3,X0)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f62,f98])).
% 3.90/0.98  
% 3.90/0.98  fof(f77,plain,(
% 3.90/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f50])).
% 3.90/0.98  
% 3.90/0.98  fof(f15,axiom,(
% 3.90/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f79,plain,(
% 3.90/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f15])).
% 3.90/0.98  
% 3.90/0.98  fof(f110,plain,(
% 3.90/0.98    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(X0))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f79,f98])).
% 3.90/0.98  
% 3.90/0.98  fof(f14,axiom,(
% 3.90/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f28,plain,(
% 3.90/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f14])).
% 3.90/0.98  
% 3.90/0.98  fof(f78,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f28])).
% 3.90/0.98  
% 3.90/0.98  fof(f2,axiom,(
% 3.90/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f60,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f2])).
% 3.90/0.98  
% 3.90/0.98  fof(f17,axiom,(
% 3.90/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f81,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f17])).
% 3.90/0.98  
% 3.90/0.98  fof(f6,axiom,(
% 3.90/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f64,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f6])).
% 3.90/0.98  
% 3.90/0.98  fof(f7,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f65,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f7])).
% 3.90/0.98  
% 3.90/0.98  fof(f8,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f66,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f8])).
% 3.90/0.98  
% 3.90/0.98  fof(f9,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f67,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f9])).
% 3.90/0.98  
% 3.90/0.98  fof(f10,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f68,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f10])).
% 3.90/0.98  
% 3.90/0.98  fof(f11,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f69,plain,(
% 3.90/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f11])).
% 3.90/0.98  
% 3.90/0.98  fof(f99,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f68,f69])).
% 3.90/0.98  
% 3.90/0.98  fof(f100,plain,(
% 3.90/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f67,f99])).
% 3.90/0.98  
% 3.90/0.98  fof(f101,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f66,f100])).
% 3.90/0.98  
% 3.90/0.98  fof(f102,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f65,f101])).
% 3.90/0.98  
% 3.90/0.98  fof(f103,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f64,f102])).
% 3.90/0.98  
% 3.90/0.98  fof(f104,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f81,f103])).
% 3.90/0.98  
% 3.90/0.98  fof(f105,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f60,f104])).
% 3.90/0.98  
% 3.90/0.98  fof(f109,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f78,f105])).
% 3.90/0.98  
% 3.90/0.98  fof(f3,axiom,(
% 3.90/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f61,plain,(
% 3.90/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f3])).
% 3.90/0.98  
% 3.90/0.98  fof(f106,plain,(
% 3.90/0.98    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = sK3) )),
% 3.90/0.98    inference(definition_unfolding,[],[f61,f104,f98,f98])).
% 3.90/0.98  
% 3.90/0.98  fof(f5,axiom,(
% 3.90/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f63,plain,(
% 3.90/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f5])).
% 3.90/0.98  
% 3.90/0.98  fof(f108,plain,(
% 3.90/0.98    ( ! [X0] : (k5_xboole_0(X0,sK3) = X0) )),
% 3.90/0.98    inference(definition_unfolding,[],[f63,f98])).
% 3.90/0.98  
% 3.90/0.98  fof(f16,axiom,(
% 3.90/0.98    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f29,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 3.90/0.98    inference(ennf_transformation,[],[f16])).
% 3.90/0.98  
% 3.90/0.98  fof(f30,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 3.90/0.98    inference(flattening,[],[f29])).
% 3.90/0.98  
% 3.90/0.98  fof(f80,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f30])).
% 3.90/0.98  
% 3.90/0.98  fof(f111,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK3 = X0) )),
% 3.90/0.98    inference(definition_unfolding,[],[f80,f98])).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f112]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1231,plain,
% 3.90/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8,plain,
% 3.90/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1227,plain,
% 3.90/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.90/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_12,plain,
% 3.90/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1223,plain,
% 3.90/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.90/0.98      | r2_hidden(X0,X1) != iProver_top
% 3.90/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2689,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.90/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.90/0.98      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1227,c_1223]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_24,negated_conjecture,
% 3.90/0.98      ( ~ v3_pre_topc(X0,sK1)
% 3.90/0.98      | ~ v4_pre_topc(X0,sK1)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.90/0.98      | r2_hidden(X0,sK3)
% 3.90/0.98      | ~ r2_hidden(sK2,X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_22,plain,
% 3.90/0.98      ( v4_pre_topc(k2_struct_0(X0),X0)
% 3.90/0.98      | ~ v2_pre_topc(X0)
% 3.90/0.98      | ~ l1_pre_topc(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_31,negated_conjecture,
% 3.90/0.98      ( v2_pre_topc(sK1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_448,plain,
% 3.90/0.98      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK1 != X0 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_449,plain,
% 3.90/0.98      ( v4_pre_topc(k2_struct_0(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_30,negated_conjecture,
% 3.90/0.98      ( l1_pre_topc(sK1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_65,plain,
% 3.90/0.98      ( v4_pre_topc(k2_struct_0(sK1),sK1)
% 3.90/0.98      | ~ v2_pre_topc(sK1)
% 3.90/0.98      | ~ l1_pre_topc(sK1) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_451,plain,
% 3.90/0.98      ( v4_pre_topc(k2_struct_0(sK1),sK1) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_449,c_31,c_30,c_65]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_470,plain,
% 3.90/0.98      ( ~ v3_pre_topc(X0,sK1)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.90/0.98      | r2_hidden(X0,sK3)
% 3.90/0.98      | ~ r2_hidden(sK2,X0)
% 3.90/0.98      | k2_struct_0(sK1) != X0
% 3.90/0.98      | sK1 != sK1 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_451]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_471,plain,
% 3.90/0.98      ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
% 3.90/0.98      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.90/0.98      | r2_hidden(k2_struct_0(sK1),sK3)
% 3.90/0.98      | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_470]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_23,plain,
% 3.90/0.98      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.90/0.98      | ~ v2_pre_topc(X0)
% 3.90/0.98      | ~ l1_pre_topc(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_62,plain,
% 3.90/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1)
% 3.90/0.98      | ~ v2_pre_topc(sK1)
% 3.90/0.98      | ~ l1_pre_topc(sK1) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_473,plain,
% 3.90/0.98      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.90/0.98      | r2_hidden(k2_struct_0(sK1),sK3)
% 3.90/0.98      | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_471,c_31,c_30,c_62]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1212,plain,
% 3.90/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.90/0.98      | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 3.90/0.98      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_20,plain,
% 3.90/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_19,plain,
% 3.90/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_423,plain,
% 3.90/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.90/0.98      inference(resolution,[status(thm)],[c_20,c_19]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_463,plain,
% 3.90/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_423,c_30]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_464,plain,
% 3.90/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_463]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1319,plain,
% 3.90/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 3.90/0.98      | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 3.90/0.98      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_1212,c_464]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_21,plain,
% 3.90/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_32,negated_conjecture,
% 3.90/0.98      ( ~ v2_struct_0(sK1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_410,plain,
% 3.90/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_411,plain,
% 3.90/0.98      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_410]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_68,plain,
% 3.90/0.98      ( v2_struct_0(sK1)
% 3.90/0.98      | ~ l1_struct_0(sK1)
% 3.90/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_71,plain,
% 3.90/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_413,plain,
% 3.90/0.98      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_411,c_32,c_30,c_68,c_71]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1213,plain,
% 3.90/0.98      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1241,plain,
% 3.90/0.98      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_1213,c_464]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_29,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1214,plain,
% 3.90/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1244,plain,
% 3.90/0.98      ( m1_subset_1(sK2,k2_struct_0(sK1)) = iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_1214,c_464]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1222,plain,
% 3.90/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.90/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.90/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1985,plain,
% 3.90/0.98      ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top
% 3.90/0.98      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1244,c_1222]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2090,plain,
% 3.90/0.98      ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 3.90/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_1319,c_1241,c_1985]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2091,plain,
% 3.90/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 3.90/0.98      | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_2090]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6068,plain,
% 3.90/0.98      ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 3.90/0.98      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 3.90/0.98      | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2689,c_2091]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6596,plain,
% 3.90/0.98      ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 3.90/0.98      | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 3.90/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6068,c_1231]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_18,plain,
% 3.90/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1217,plain,
% 3.90/0.98      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6599,plain,
% 3.90/0.98      ( r1_tarski(sK3,k2_struct_0(sK1)) != iProver_top
% 3.90/0.98      | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_6596,c_1217]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4,negated_conjecture,
% 3.90/0.98      ( r1_tarski(sK3,X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1230,plain,
% 3.90/0.98      ( r1_tarski(sK3,X0) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7371,plain,
% 3.90/0.98      ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 3.90/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6599,c_1230]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_10,plain,
% 3.90/0.98      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1225,plain,
% 3.90/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.90/0.98      | v1_xboole_0(X1) != iProver_top
% 3.90/0.98      | v1_xboole_0(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1220,plain,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_14,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.98      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1221,plain,
% 3.90/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 3.90/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4772,plain,
% 3.90/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))) = k3_subset_1(X0,sK3) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1220,c_1221]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3,negated_conjecture,
% 3.90/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = sK3 ),
% 3.90/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5,negated_conjecture,
% 3.90/0.98      ( k5_xboole_0(X0,sK3) = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4774,plain,
% 3.90/0.98      ( k3_subset_1(X0,sK3) = X0 ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_4772,c_3,c_5]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_16,negated_conjecture,
% 3.90/0.98      ( ~ m1_subset_1(X0,X1)
% 3.90/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.90/0.98      | r2_hidden(X0,X2)
% 3.90/0.98      | r2_hidden(X0,k3_subset_1(X1,X2))
% 3.90/0.98      | sK3 = X1 ),
% 3.90/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1219,plain,
% 3.90/0.98      ( sK3 = X0
% 3.90/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.90/0.98      | r2_hidden(X1,X2) = iProver_top
% 3.90/0.98      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1744,plain,
% 3.90/0.98      ( sK3 = X0
% 3.90/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.90/0.98      | r2_hidden(X1,X2) = iProver_top
% 3.90/0.98      | r1_tarski(k3_subset_1(X0,X2),X1) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1219,c_1217]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2225,plain,
% 3.90/0.98      ( sK3 = X0
% 3.90/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.90/0.98      | m1_subset_1(k3_subset_1(X0,X1),X0) != iProver_top
% 3.90/0.98      | r2_hidden(k3_subset_1(X0,X1),X1) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1231,c_1744]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4900,plain,
% 3.90/0.98      ( sK3 = X0
% 3.90/0.98      | m1_subset_1(X0,X0) != iProver_top
% 3.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.90/0.98      | r2_hidden(k3_subset_1(X0,sK3),sK3) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4774,c_2225]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4966,plain,
% 3.90/0.98      ( sK3 = X0
% 3.90/0.98      | m1_subset_1(X0,X0) != iProver_top
% 3.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.90/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_4900,c_4774]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_53,plain,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_57,plain,
% 3.90/0.98      ( r1_tarski(sK3,X0) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4705,plain,
% 3.90/0.98      ( ~ r2_hidden(X0,sK3) | ~ r1_tarski(sK3,X0) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4706,plain,
% 3.90/0.98      ( r2_hidden(X0,sK3) != iProver_top | r1_tarski(sK3,X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_4705]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5095,plain,
% 3.90/0.98      ( sK3 = X0 | m1_subset_1(X0,X0) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_4966,c_53,c_57,c_4706]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5103,plain,
% 3.90/0.98      ( sK3 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1225,c_5095]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7373,plain,
% 3.90/0.98      ( k1_zfmisc_1(k2_struct_0(sK1)) = sK3 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7371,c_5103]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7728,plain,
% 3.90/0.98      ( r2_hidden(X0,sK3) = iProver_top
% 3.90/0.98      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7373,c_1227]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1873,plain,
% 3.90/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.90/0.98      | r1_tarski(k1_zfmisc_1(X1),X0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1227,c_1217]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7726,plain,
% 3.90/0.98      ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 3.90/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7373,c_1873]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8509,plain,
% 3.90/0.98      ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_7728,c_57,c_7726]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8516,plain,
% 3.90/0.98      ( $false ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_1231,c_8509]) ).
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  ------                               Statistics
% 3.90/0.98  
% 3.90/0.98  ------ Selected
% 3.90/0.98  
% 3.90/0.98  total_time:                             0.408
% 3.90/0.98  
%------------------------------------------------------------------------------
