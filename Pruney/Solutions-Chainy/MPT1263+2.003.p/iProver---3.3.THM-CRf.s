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
% DateTime   : Thu Dec  3 12:14:51 EST 2020

% Result     : Theorem 55.31s
% Output     : CNFRefutation 55.31s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_99722)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f88])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f77,f88])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f70])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_xboole_0(X1,X2)
          & v3_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK8)
        & v3_pre_topc(sK8,X0)
        & k1_xboole_0 != sK8
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( r1_xboole_0(sK7,X2)
              & v3_pre_topc(X2,X0)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(sK7,X0) )
        & ( ! [X3] :
              ( ~ r1_xboole_0(sK7,X3)
              | ~ v3_pre_topc(X3,X0)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v1_tops_1(sK7,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v1_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,sK6)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
            | ~ v1_tops_1(X1,sK6) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,sK6)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
            | v1_tops_1(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ( ( r1_xboole_0(sK7,sK8)
        & v3_pre_topc(sK8,sK6)
        & k1_xboole_0 != sK8
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) )
      | ~ v1_tops_1(sK7,sK6) )
    & ( ! [X3] :
          ( ~ r1_xboole_0(sK7,X3)
          | ~ v3_pre_topc(X3,sK6)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
      | v1_tops_1(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f71,f74,f73,f72])).

fof(f122,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f106,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f117,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ! [X4] :
                ( ~ r1_xboole_0(X1,X4)
                | ~ r2_hidden(X3,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ r2_hidden(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X1,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X3,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( r1_xboole_0(X1,X4)
                    & r2_hidden(X3,X4)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X3,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ r2_hidden(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f56,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X1,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X3,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( r1_xboole_0(X1,X4)
                    & r2_hidden(X3,X4)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X3,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ r2_hidden(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f55])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X0,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X5] :
                  ( ~ r1_xboole_0(X0,X5)
                  | ~ r2_hidden(X3,X5)
                  | ~ v3_pre_topc(X5,X1)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ? [X7] :
                    ( r1_xboole_0(X0,X7)
                    & r2_hidden(X6,X7)
                    & v3_pre_topc(X7,X1)
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ! [X8] :
                    ( ~ r1_xboole_0(X0,X8)
                    | ~ r2_hidden(X6,X8)
                    | ~ v3_pre_topc(X8,X1)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ r2_hidden(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f56])).

fof(f60,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X0,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_xboole_0(X0,sK4(X0,X1,X6))
        & r2_hidden(X6,sK4(X0,X1,X6))
        & v3_pre_topc(sK4(X0,X1,X6),X1)
        & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X0,X4)
          & r2_hidden(X3,X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_xboole_0(X0,sK3(X0,X1,X2))
        & r2_hidden(X3,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X0,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X0,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X1)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X1)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X0,X4)
              & r2_hidden(sK2(X0,X1,X2),X4)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X0,X5)
              | ~ r2_hidden(sK2(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X1)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( r1_xboole_0(X0,sK3(X0,X1,X2))
              & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
              & v3_pre_topc(sK3(X0,X1,X2),X1)
              & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X0,X5)
                | ~ r2_hidden(sK2(X0,X1,X2),X5)
                | ~ v3_pre_topc(X5,X1)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1,X2),X2) )
          & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ( r1_xboole_0(X0,sK4(X0,X1,X6))
                  & r2_hidden(X6,sK4(X0,X1,X6))
                  & v3_pre_topc(sK4(X0,X1,X6),X1)
                  & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ! [X8] :
                    ( ~ r1_xboole_0(X0,X8)
                    | ~ r2_hidden(X6,X8)
                    | ~ v3_pre_topc(X8,X1)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ r2_hidden(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    ! [X2,X0,X5,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_xboole_0(X0,X5)
      | ~ r2_hidden(sK2(X0,X1,X2),X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f129,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f78,f88])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f129])).

fof(f123,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f75])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f35,f50,f49])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X1,X2) = X0
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f118,plain,(
    ! [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f80,f88])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f134,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f81,f129])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_xboole_0(X0,sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f124,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK7,X3)
      | ~ v3_pre_topc(X3,sK6)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | v1_tops_1(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK5(X0,X1,X2))
        & r2_hidden(X2,sK5(X0,X1,X2))
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK5(X0,X1,X2))
                    & r2_hidden(X2,sK5(X0,X1,X2))
                    & v3_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f64,f65])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f127,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f128,plain,
    ( r1_xboole_0(sK7,sK8)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f88])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,
    ( k1_xboole_0 != sK8
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1663,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3044,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1662])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1668,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3730,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3044,c_1668])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1670,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4028,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3730,c_1670])).

cnf(c_49,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1624,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_28,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1645,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2744,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1645])).

cnf(c_27,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1646,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2835,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_2744,c_1646])).

cnf(c_39,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1634,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3840,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_1634])).

cnf(c_50,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_51,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_52,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_4486,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3840,c_51,c_52])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1653,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X3)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1654,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10903,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_1654])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_560,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6510,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_568,c_560])).

cnf(c_561,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5264,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_561,c_560])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5567,plain,
    ( X0 = k2_subset_1(X0) ),
    inference(resolution,[status(thm)],[c_5264,c_5])).

cnf(c_17407,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_6510,c_5567])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18605,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_17407,c_7])).

cnf(c_14477,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
    inference(resolution,[status(thm)],[c_19,c_20])).

cnf(c_18611,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_18605,c_14477])).

cnf(c_18612,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18611])).

cnf(c_35583,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10903,c_18612])).

cnf(c_35584,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_35583])).

cnf(c_35591,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_35584])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1655,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7611,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_1655])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1667,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16409,plain,
    ( k5_xboole_0(u1_struct_0(X0),k1_setfam_1(k2_tarski(u1_struct_0(X0),sK3(X1,X0,u1_struct_0(X0))))) = k3_subset_1(u1_struct_0(X0),sK3(X1,X0,u1_struct_0(X0)))
    | sP0(X1,X0,u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7611,c_1667])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1625,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_1666,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1666,c_5])).

cnf(c_26,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1647,plain,
    ( sP1(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7910,plain,
    ( sP1(u1_struct_0(X0),X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1647])).

cnf(c_20683,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_7910])).

cnf(c_9272,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_26,c_48])).

cnf(c_9540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | sP1(X0,sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9272,c_49])).

cnf(c_9541,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_9540])).

cnf(c_18626,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) ),
    inference(resolution,[status(thm)],[c_18605,c_9541])).

cnf(c_18627,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18626])).

cnf(c_20763,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20683,c_18627])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k2_pre_topc(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1660,plain,
    ( k2_pre_topc(X0,X1) = X2
    | sP1(X2,X0,X1) != iProver_top
    | sP0(X1,X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20768,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20763,c_1660])).

cnf(c_28678,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | k5_xboole_0(u1_struct_0(sK6),k1_setfam_1(k2_tarski(u1_struct_0(sK6),sK3(sK7,sK6,u1_struct_0(sK6))))) = k3_subset_1(u1_struct_0(sK6),sK3(sK7,sK6,u1_struct_0(sK6))) ),
    inference(superposition,[status(thm)],[c_16409,c_20768])).

cnf(c_40,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1633,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2969,plain,
    ( k2_pre_topc(sK6,k2_struct_0(sK6)) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_1624,c_1633])).

cnf(c_2970,plain,
    ( k2_pre_topc(sK6,u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(light_normalisation,[status(thm)],[c_2969,c_2835])).

cnf(c_29,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1644,plain,
    ( k2_pre_topc(X0,X1) != X1
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10302,plain,
    ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_1644])).

cnf(c_18578,plain,
    ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10302,c_51,c_52])).

cnf(c_18584,plain,
    ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18578,c_1683])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1665,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4146,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1663,c_1665])).

cnf(c_5199,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1663,c_1667])).

cnf(c_3,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1686,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_3])).

cnf(c_5212,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5199,c_3,c_1686])).

cnf(c_7242,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4146,c_5212])).

cnf(c_42,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1631,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7246,plain,
    ( v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | v3_pre_topc(k1_xboole_0,X0) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7242,c_1631])).

cnf(c_24486,plain,
    ( v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | v3_pre_topc(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7246,c_1683])).

cnf(c_24488,plain,
    ( v4_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24486])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1658,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6374,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_1658])).

cnf(c_47,negated_conjecture,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(sK7,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1626,plain,
    ( k1_xboole_0 = X0
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_16421,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7611,c_1626])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2)
    | v3_pre_topc(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1656,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6366,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_1656])).

cnf(c_16905,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16421,c_6366])).

cnf(c_16909,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6374,c_16905])).

cnf(c_53,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_104,plain,
    ( l1_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_107,plain,
    ( ~ l1_struct_0(sK6)
    | k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2230,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_2231,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2230])).

cnf(c_2412,plain,
    ( k2_pre_topc(sK6,sK7) != X0
    | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_2800,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_25746,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16909,c_49,c_52,c_53,c_104,c_107,c_2231,c_2800,c_20768])).

cnf(c_38,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1635,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4996,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_1635])).

cnf(c_5007,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4996,c_2835])).

cnf(c_5912,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5007,c_52])).

cnf(c_5913,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5912])).

cnf(c_25757,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_25746,c_5913])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1657,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_99694,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_25757,c_1657])).

cnf(c_14037,plain,
    ( sP0(X0,X1,u1_struct_0(X1))
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_57671,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6))
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_14037])).

cnf(c_57672,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57671])).

cnf(c_101521,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_99694,c_20768,c_57672])).

cnf(c_35,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1638,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1661,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1989,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1638,c_1661])).

cnf(c_13420,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k2_pre_topc(X0,X2)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1989])).

cnf(c_4027,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1670])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1664,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6267,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1664])).

cnf(c_44927,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13420,c_4027,c_6267])).

cnf(c_44935,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_44927])).

cnf(c_101532,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_101521,c_44935])).

cnf(c_101590,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v3_pre_topc(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101532])).

cnf(c_101863,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28678,c_52,c_18584,c_24488,c_101590])).

cnf(c_46,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1627,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_13422,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1989])).

cnf(c_44,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | v3_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_59,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_14348,plain,
    ( r1_xboole_0(X1,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13422,c_52,c_59])).

cnf(c_14349,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_14348])).

cnf(c_14362,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_14349])).

cnf(c_43,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | r1_xboole_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_60,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_14520,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14362,c_60])).

cnf(c_14521,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_14520])).

cnf(c_101997,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_101863,c_14521])).

cnf(c_6268,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1664])).

cnf(c_102921,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_101997,c_49,c_52,c_53,c_104,c_107,c_2231,c_2800,c_6268,c_18584,c_24488,c_101590])).

cnf(c_185286,plain,
    ( sP0(X0,sK6,sK8) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35591,c_102921])).

cnf(c_187544,plain,
    ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_185286])).

cnf(c_97998,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_103309,plain,
    ( X0 != k1_setfam_1(k2_tarski(sK7,sK8))
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_setfam_1(k2_tarski(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_97998])).

cnf(c_140877,plain,
    ( sK8 != k1_setfam_1(k2_tarski(sK7,sK8))
    | k1_xboole_0 != k1_setfam_1(k2_tarski(sK7,sK8))
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_103309])).

cnf(c_101232,plain,
    ( X0 != X1
    | X0 = k1_setfam_1(k2_tarski(sK7,sK8))
    | k1_setfam_1(k2_tarski(sK7,sK8)) != X1 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_105648,plain,
    ( X0 = k1_setfam_1(k2_tarski(sK7,sK8))
    | X0 != k1_xboole_0
    | k1_setfam_1(k2_tarski(sK7,sK8)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_101232])).

cnf(c_140728,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) != k1_xboole_0
    | sK8 = k1_setfam_1(k2_tarski(sK7,sK8))
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_105648])).

cnf(c_1630,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_25761,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_25746,c_1630])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1669,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25919,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25761,c_1669])).

cnf(c_16417,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) != iProver_top
    | r2_hidden(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7611,c_1989])).

cnf(c_72156,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16417,c_6366])).

cnf(c_72168,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),k2_pre_topc(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_72156])).

cnf(c_14042,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14037])).

cnf(c_78281,plain,
    ( r2_hidden(sK2(X0,X1,u1_struct_0(X1)),k2_pre_topc(X1,X2)) != iProver_top
    | sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72168,c_14042])).

cnf(c_78282,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),k2_pre_topc(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_78281])).

cnf(c_78312,plain,
    ( sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(X0,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_78282])).

cnf(c_574,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_590,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_595,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_2202,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2207,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_2209,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_2603,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_2942,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_4217,plain,
    ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2670,plain,
    ( X0 != X1
    | X0 = k2_subset_1(X2)
    | k2_subset_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_3872,plain,
    ( X0 != X1
    | X0 = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_2670])).

cnf(c_7559,plain,
    ( X0 != u1_struct_0(sK6)
    | X0 = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3872])).

cnf(c_17097,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK6) = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_7559])).

cnf(c_2277,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_3319,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X0 != k2_subset_1(X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2277])).

cnf(c_5774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X0 != k2_subset_1(X2)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_3319])).

cnf(c_8929,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5774])).

cnf(c_48535,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8929])).

cnf(c_48544,plain,
    ( u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48535])).

cnf(c_48546,plain,
    ( u1_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48544])).

cnf(c_99542,plain,
    ( r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(X0,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_78312,c_52,c_590,c_595,c_2209,c_2942,c_4217,c_17097,c_48546])).

cnf(c_99543,plain,
    ( sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(X0,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_99542])).

cnf(c_99551,plain,
    ( sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_99543,c_1653])).

cnf(c_99556,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r1_xboole_0(u1_struct_0(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25919,c_99551])).

cnf(c_27497,plain,
    ( ~ r1_xboole_0(sK7,sK8)
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_100973,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | r1_xboole_0(u1_struct_0(sK6),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_99556,c_49,c_48,c_43,c_104,c_107,c_2230,c_2800,c_20768,c_27497,c_99722])).

cnf(c_100979,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_100973,c_4027])).

cnf(c_36,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1637,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7398,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_1637])).

cnf(c_19759,plain,
    ( v2_struct_0(sK6) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7398,c_52])).

cnf(c_19760,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_19759])).

cnf(c_5489,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1661])).

cnf(c_19769,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19760,c_1683,c_5489])).

cnf(c_19773,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_19769])).

cnf(c_7907,plain,
    ( sP1(k1_xboole_0,X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1647])).

cnf(c_18917,plain,
    ( sP1(k1_xboole_0,X0,k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_7907])).

cnf(c_19002,plain,
    ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
    | sP0(k1_xboole_0,X0,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18917,c_1660])).

cnf(c_20514,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v2_struct_0(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_19773,c_19002])).

cnf(c_2212,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2217,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_2219,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_41,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1632,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5218,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5212,c_1632])).

cnf(c_5237,plain,
    ( v4_pre_topc(k1_xboole_0,sK6) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5218])).

cnf(c_30,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1643,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7407,plain,
    ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1643])).

cnf(c_7438,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7407])).

cnf(c_91726,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20514,c_51,c_52,c_2219,c_3840,c_5237,c_7438])).

cnf(c_7908,plain,
    ( sP1(sK8,sK6,X0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1647])).

cnf(c_8503,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | sP1(sK8,sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7908,c_52])).

cnf(c_8504,plain,
    ( sP1(sK8,sK6,X0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8503])).

cnf(c_8512,plain,
    ( sP1(sK8,sK6,k1_xboole_0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_8504])).

cnf(c_9806,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = sK8
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8512,c_1660])).

cnf(c_91731,plain,
    ( sK8 = k1_xboole_0
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_91726,c_9806])).

cnf(c_2523,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_3029,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_70500,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) != k1_xboole_0
    | k1_xboole_0 = k1_setfam_1(k2_tarski(sK7,sK8))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3029])).

cnf(c_3030,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_45,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f126])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_187544,c_140877,c_140728,c_101590,c_100979,c_91731,c_70500,c_24488,c_18584,c_3030,c_2800,c_2231,c_2230,c_107,c_104,c_45,c_53,c_48,c_52,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.31/7.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.31/7.50  
% 55.31/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.31/7.50  
% 55.31/7.50  ------  iProver source info
% 55.31/7.50  
% 55.31/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.31/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.31/7.50  git: non_committed_changes: false
% 55.31/7.50  git: last_make_outside_of_git: false
% 55.31/7.50  
% 55.31/7.50  ------ 
% 55.31/7.50  ------ Parsing...
% 55.31/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.31/7.50  
% 55.31/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 55.31/7.50  
% 55.31/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.31/7.50  
% 55.31/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.31/7.50  ------ Proving...
% 55.31/7.50  ------ Problem Properties 
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  clauses                                 51
% 55.31/7.50  conjectures                             8
% 55.31/7.50  EPR                                     6
% 55.31/7.50  Horn                                    36
% 55.31/7.50  unary                                   8
% 55.31/7.50  binary                                  15
% 55.31/7.50  lits                                    162
% 55.31/7.50  lits eq                                 17
% 55.31/7.50  fd_pure                                 0
% 55.31/7.50  fd_pseudo                               0
% 55.31/7.50  fd_cond                                 1
% 55.31/7.50  fd_pseudo_cond                          1
% 55.31/7.50  AC symbols                              0
% 55.31/7.50  
% 55.31/7.50  ------ Input Options Time Limit: Unbounded
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  ------ 
% 55.31/7.50  Current options:
% 55.31/7.50  ------ 
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  ------ Proving...
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  % SZS status Theorem for theBenchmark.p
% 55.31/7.50  
% 55.31/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.31/7.50  
% 55.31/7.50  fof(f11,axiom,(
% 55.31/7.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f87,plain,(
% 55.31/7.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f11])).
% 55.31/7.50  
% 55.31/7.50  fof(f13,axiom,(
% 55.31/7.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f26,plain,(
% 55.31/7.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 55.31/7.50    inference(unused_predicate_definition_removal,[],[f13])).
% 55.31/7.50  
% 55.31/7.50  fof(f31,plain,(
% 55.31/7.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 55.31/7.50    inference(ennf_transformation,[],[f26])).
% 55.31/7.50  
% 55.31/7.50  fof(f89,plain,(
% 55.31/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f31])).
% 55.31/7.50  
% 55.31/7.50  fof(f3,axiom,(
% 55.31/7.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f27,plain,(
% 55.31/7.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 55.31/7.50    inference(ennf_transformation,[],[f3])).
% 55.31/7.50  
% 55.31/7.50  fof(f79,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f27])).
% 55.31/7.50  
% 55.31/7.50  fof(f12,axiom,(
% 55.31/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f88,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f12])).
% 55.31/7.50  
% 55.31/7.50  fof(f132,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 55.31/7.50    inference(definition_unfolding,[],[f79,f88])).
% 55.31/7.50  
% 55.31/7.50  fof(f1,axiom,(
% 55.31/7.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f52,plain,(
% 55.31/7.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 55.31/7.50    inference(nnf_transformation,[],[f1])).
% 55.31/7.50  
% 55.31/7.50  fof(f77,plain,(
% 55.31/7.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 55.31/7.50    inference(cnf_transformation,[],[f52])).
% 55.31/7.50  
% 55.31/7.50  fof(f130,plain,(
% 55.31/7.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.31/7.50    inference(definition_unfolding,[],[f77,f88])).
% 55.31/7.50  
% 55.31/7.50  fof(f24,conjecture,(
% 55.31/7.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f25,negated_conjecture,(
% 55.31/7.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 55.31/7.50    inference(negated_conjecture,[],[f24])).
% 55.31/7.50  
% 55.31/7.50  fof(f47,plain,(
% 55.31/7.50    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 55.31/7.50    inference(ennf_transformation,[],[f25])).
% 55.31/7.50  
% 55.31/7.50  fof(f48,plain,(
% 55.31/7.50    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f47])).
% 55.31/7.50  
% 55.31/7.50  fof(f69,plain,(
% 55.31/7.50    ? [X0] : (? [X1] : (((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.31/7.50    inference(nnf_transformation,[],[f48])).
% 55.31/7.50  
% 55.31/7.50  fof(f70,plain,(
% 55.31/7.50    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f69])).
% 55.31/7.50  
% 55.31/7.50  fof(f71,plain,(
% 55.31/7.50    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 55.31/7.50    inference(rectify,[],[f70])).
% 55.31/7.50  
% 55.31/7.50  fof(f74,plain,(
% 55.31/7.50    ( ! [X0,X1] : (? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK8) & v3_pre_topc(sK8,X0) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f73,plain,(
% 55.31/7.50    ( ! [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (r1_xboole_0(sK7,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(sK7,X0)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f72,plain,(
% 55.31/7.50    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK6) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(X1,sK6)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f75,plain,(
% 55.31/7.50    (((r1_xboole_0(sK7,sK8) & v3_pre_topc(sK8,sK6) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(sK7,sK6)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 55.31/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f71,f74,f73,f72])).
% 55.31/7.50  
% 55.31/7.50  fof(f122,plain,(
% 55.31/7.50    l1_pre_topc(sK6)),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f17,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f37,plain,(
% 55.31/7.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f17])).
% 55.31/7.50  
% 55.31/7.50  fof(f106,plain,(
% 55.31/7.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f37])).
% 55.31/7.50  
% 55.31/7.50  fof(f16,axiom,(
% 55.31/7.50    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f36,plain,(
% 55.31/7.50    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f16])).
% 55.31/7.50  
% 55.31/7.50  fof(f105,plain,(
% 55.31/7.50    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f36])).
% 55.31/7.50  
% 55.31/7.50  fof(f21,axiom,(
% 55.31/7.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f43,plain,(
% 55.31/7.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 55.31/7.50    inference(ennf_transformation,[],[f21])).
% 55.31/7.50  
% 55.31/7.50  fof(f44,plain,(
% 55.31/7.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f43])).
% 55.31/7.50  
% 55.31/7.50  fof(f117,plain,(
% 55.31/7.50    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f44])).
% 55.31/7.50  
% 55.31/7.50  fof(f121,plain,(
% 55.31/7.50    v2_pre_topc(sK6)),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f49,plain,(
% 55.31/7.50    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0))))),
% 55.31/7.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 55.31/7.50  
% 55.31/7.50  fof(f55,plain,(
% 55.31/7.50    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2))) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 55.31/7.50    inference(nnf_transformation,[],[f49])).
% 55.31/7.50  
% 55.31/7.50  fof(f56,plain,(
% 55.31/7.50    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 55.31/7.50    inference(flattening,[],[f55])).
% 55.31/7.50  
% 55.31/7.50  fof(f57,plain,(
% 55.31/7.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 55.31/7.50    inference(rectify,[],[f56])).
% 55.31/7.50  
% 55.31/7.50  fof(f60,plain,(
% 55.31/7.50    ! [X6,X1,X0] : (? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))))),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f59,plain,(
% 55.31/7.50    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(X3,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f58,plain,(
% 55.31/7.50    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1))) => ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(sK2(X0,X1,X2),X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f61,plain,(
% 55.31/7.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 55.31/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).
% 55.31/7.50  
% 55.31/7.50  fof(f98,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f61])).
% 55.31/7.50  
% 55.31/7.50  fof(f99,plain,(
% 55.31/7.50    ( ! [X2,X0,X5,X1] : (sP0(X0,X1,X2) | ~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f61])).
% 55.31/7.50  
% 55.31/7.50  fof(f6,axiom,(
% 55.31/7.50    ! [X0] : k2_subset_1(X0) = X0),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f82,plain,(
% 55.31/7.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 55.31/7.50    inference(cnf_transformation,[],[f6])).
% 55.31/7.50  
% 55.31/7.50  fof(f8,axiom,(
% 55.31/7.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f84,plain,(
% 55.31/7.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f8])).
% 55.31/7.50  
% 55.31/7.50  fof(f100,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f61])).
% 55.31/7.50  
% 55.31/7.50  fof(f7,axiom,(
% 55.31/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f28,plain,(
% 55.31/7.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.31/7.50    inference(ennf_transformation,[],[f7])).
% 55.31/7.50  
% 55.31/7.50  fof(f83,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f28])).
% 55.31/7.50  
% 55.31/7.50  fof(f2,axiom,(
% 55.31/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f78,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f2])).
% 55.31/7.50  
% 55.31/7.50  fof(f129,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 55.31/7.50    inference(definition_unfolding,[],[f78,f88])).
% 55.31/7.50  
% 55.31/7.50  fof(f135,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.31/7.50    inference(definition_unfolding,[],[f83,f129])).
% 55.31/7.50  
% 55.31/7.50  fof(f123,plain,(
% 55.31/7.50    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f15,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f34,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f15])).
% 55.31/7.50  
% 55.31/7.50  fof(f35,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f34])).
% 55.31/7.50  
% 55.31/7.50  fof(f50,plain,(
% 55.31/7.50    ! [X2,X0,X1] : ((k2_pre_topc(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 55.31/7.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 55.31/7.50  
% 55.31/7.50  fof(f51,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(definition_folding,[],[f35,f50,f49])).
% 55.31/7.50  
% 55.31/7.50  fof(f104,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f51])).
% 55.31/7.50  
% 55.31/7.50  fof(f53,plain,(
% 55.31/7.50    ! [X2,X0,X1] : (((k2_pre_topc(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_pre_topc(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 55.31/7.50    inference(nnf_transformation,[],[f50])).
% 55.31/7.50  
% 55.31/7.50  fof(f54,plain,(
% 55.31/7.50    ! [X0,X1,X2] : (((k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 55.31/7.50    inference(rectify,[],[f53])).
% 55.31/7.50  
% 55.31/7.50  fof(f92,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f54])).
% 55.31/7.50  
% 55.31/7.50  fof(f22,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f45,plain,(
% 55.31/7.50    ! [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f22])).
% 55.31/7.50  
% 55.31/7.50  fof(f118,plain,(
% 55.31/7.50    ( ! [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f45])).
% 55.31/7.50  
% 55.31/7.50  fof(f18,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f38,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f18])).
% 55.31/7.50  
% 55.31/7.50  fof(f39,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f38])).
% 55.31/7.50  
% 55.31/7.50  fof(f108,plain,(
% 55.31/7.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f39])).
% 55.31/7.50  
% 55.31/7.50  fof(f9,axiom,(
% 55.31/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f29,plain,(
% 55.31/7.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.31/7.50    inference(ennf_transformation,[],[f9])).
% 55.31/7.50  
% 55.31/7.50  fof(f85,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f29])).
% 55.31/7.50  
% 55.31/7.50  fof(f4,axiom,(
% 55.31/7.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f80,plain,(
% 55.31/7.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.31/7.50    inference(cnf_transformation,[],[f4])).
% 55.31/7.50  
% 55.31/7.50  fof(f133,plain,(
% 55.31/7.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 55.31/7.50    inference(definition_unfolding,[],[f80,f88])).
% 55.31/7.50  
% 55.31/7.50  fof(f5,axiom,(
% 55.31/7.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f81,plain,(
% 55.31/7.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.31/7.50    inference(cnf_transformation,[],[f5])).
% 55.31/7.50  
% 55.31/7.50  fof(f134,plain,(
% 55.31/7.50    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 55.31/7.50    inference(definition_unfolding,[],[f81,f129])).
% 55.31/7.50  
% 55.31/7.50  fof(f23,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f46,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f23])).
% 55.31/7.50  
% 55.31/7.50  fof(f68,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(nnf_transformation,[],[f46])).
% 55.31/7.50  
% 55.31/7.50  fof(f119,plain,(
% 55.31/7.50    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f68])).
% 55.31/7.50  
% 55.31/7.50  fof(f103,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_xboole_0(X0,sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f61])).
% 55.31/7.50  
% 55.31/7.50  fof(f124,plain,(
% 55.31/7.50    ( ! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | v1_tops_1(sK7,sK6)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f101,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f61])).
% 55.31/7.50  
% 55.31/7.50  fof(f20,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f42,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f20])).
% 55.31/7.50  
% 55.31/7.50  fof(f67,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(nnf_transformation,[],[f42])).
% 55.31/7.50  
% 55.31/7.50  fof(f116,plain,(
% 55.31/7.50    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f67])).
% 55.31/7.50  
% 55.31/7.50  fof(f115,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f67])).
% 55.31/7.50  
% 55.31/7.50  fof(f102,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f61])).
% 55.31/7.50  
% 55.31/7.50  fof(f19,axiom,(
% 55.31/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f40,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(ennf_transformation,[],[f19])).
% 55.31/7.50  
% 55.31/7.50  fof(f41,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f40])).
% 55.31/7.50  
% 55.31/7.50  fof(f62,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(nnf_transformation,[],[f41])).
% 55.31/7.50  
% 55.31/7.50  fof(f63,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(flattening,[],[f62])).
% 55.31/7.50  
% 55.31/7.50  fof(f64,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(rectify,[],[f63])).
% 55.31/7.50  
% 55.31/7.50  fof(f65,plain,(
% 55.31/7.50    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 55.31/7.50    introduced(choice_axiom,[])).
% 55.31/7.50  
% 55.31/7.50  fof(f66,plain,(
% 55.31/7.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.31/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f64,f65])).
% 55.31/7.50  
% 55.31/7.50  fof(f110,plain,(
% 55.31/7.50    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f66])).
% 55.31/7.50  
% 55.31/7.50  fof(f14,axiom,(
% 55.31/7.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f32,plain,(
% 55.31/7.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 55.31/7.50    inference(ennf_transformation,[],[f14])).
% 55.31/7.50  
% 55.31/7.50  fof(f33,plain,(
% 55.31/7.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 55.31/7.50    inference(flattening,[],[f32])).
% 55.31/7.50  
% 55.31/7.50  fof(f90,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f33])).
% 55.31/7.50  
% 55.31/7.50  fof(f10,axiom,(
% 55.31/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 55.31/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.31/7.50  
% 55.31/7.50  fof(f30,plain,(
% 55.31/7.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.31/7.50    inference(ennf_transformation,[],[f10])).
% 55.31/7.50  
% 55.31/7.50  fof(f86,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.31/7.50    inference(cnf_transformation,[],[f30])).
% 55.31/7.50  
% 55.31/7.50  fof(f125,plain,(
% 55.31/7.50    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_tops_1(sK7,sK6)),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f127,plain,(
% 55.31/7.50    v3_pre_topc(sK8,sK6) | ~v1_tops_1(sK7,sK6)),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f128,plain,(
% 55.31/7.50    r1_xboole_0(sK7,sK8) | ~v1_tops_1(sK7,sK6)),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  fof(f76,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f52])).
% 55.31/7.50  
% 55.31/7.50  fof(f131,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 55.31/7.50    inference(definition_unfolding,[],[f76,f88])).
% 55.31/7.50  
% 55.31/7.50  fof(f109,plain,(
% 55.31/7.50    ( ! [X2,X0,X1] : (~v2_struct_0(X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f66])).
% 55.31/7.50  
% 55.31/7.50  fof(f120,plain,(
% 55.31/7.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f68])).
% 55.31/7.50  
% 55.31/7.50  fof(f107,plain,(
% 55.31/7.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.31/7.50    inference(cnf_transformation,[],[f39])).
% 55.31/7.50  
% 55.31/7.50  fof(f126,plain,(
% 55.31/7.50    k1_xboole_0 != sK8 | ~v1_tops_1(sK7,sK6)),
% 55.31/7.50    inference(cnf_transformation,[],[f75])).
% 55.31/7.50  
% 55.31/7.50  cnf(c_10,plain,
% 55.31/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f87]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1663,plain,
% 55.31/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_11,plain,
% 55.31/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f89]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1662,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 55.31/7.50      | r1_tarski(X0,X1) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3044,plain,
% 55.31/7.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1662]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2,plain,
% 55.31/7.50      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f132]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1668,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 55.31/7.50      | r1_tarski(X0,X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3730,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_3044,c_1668]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_0,plain,
% 55.31/7.50      ( r1_xboole_0(X0,X1)
% 55.31/7.50      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f130]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1670,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 55.31/7.50      | r1_xboole_0(X0,X1) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4028,plain,
% 55.31/7.50      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_3730,c_1670]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_49,negated_conjecture,
% 55.31/7.50      ( l1_pre_topc(sK6) ),
% 55.31/7.50      inference(cnf_transformation,[],[f122]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1624,plain,
% 55.31/7.50      ( l1_pre_topc(sK6) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_28,plain,
% 55.31/7.50      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 55.31/7.50      inference(cnf_transformation,[],[f106]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1645,plain,
% 55.31/7.50      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2744,plain,
% 55.31/7.50      ( l1_struct_0(sK6) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1624,c_1645]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_27,plain,
% 55.31/7.50      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 55.31/7.50      inference(cnf_transformation,[],[f105]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1646,plain,
% 55.31/7.50      ( k2_struct_0(X0) = u1_struct_0(X0)
% 55.31/7.50      | l1_struct_0(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2835,plain,
% 55.31/7.50      ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_2744,c_1646]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_39,plain,
% 55.31/7.50      ( v3_pre_topc(k2_struct_0(X0),X0)
% 55.31/7.50      | ~ v2_pre_topc(X0)
% 55.31/7.50      | ~ l1_pre_topc(X0) ),
% 55.31/7.50      inference(cnf_transformation,[],[f117]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1634,plain,
% 55.31/7.50      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 55.31/7.50      | v2_pre_topc(X0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3840,plain,
% 55.31/7.50      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
% 55.31/7.50      | v2_pre_topc(sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_2835,c_1634]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_50,negated_conjecture,
% 55.31/7.50      ( v2_pre_topc(sK6) ),
% 55.31/7.50      inference(cnf_transformation,[],[f121]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_51,plain,
% 55.31/7.50      ( v2_pre_topc(sK6) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_52,plain,
% 55.31/7.50      ( l1_pre_topc(sK6) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4486,plain,
% 55.31/7.50      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_3840,c_51,c_52]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_20,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f98]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1653,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_19,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | ~ v3_pre_topc(X3,X1)
% 55.31/7.50      | ~ r2_hidden(sK2(X0,X1,X2),X3)
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2)
% 55.31/7.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ r1_xboole_0(X0,X3) ),
% 55.31/7.50      inference(cnf_transformation,[],[f99]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1654,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | v3_pre_topc(X3,X1) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 55.31/7.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X0,X3) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_10903,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1653,c_1654]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_568,plain,
% 55.31/7.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.31/7.50      theory(equality) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_560,plain,( X0 = X0 ),theory(equality) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_6510,plain,
% 55.31/7.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_568,c_560]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_561,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5264,plain,
% 55.31/7.50      ( X0 != X1 | X1 = X0 ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_561,c_560]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5,plain,
% 55.31/7.50      ( k2_subset_1(X0) = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f82]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5567,plain,
% 55.31/7.50      ( X0 = k2_subset_1(X0) ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_5264,c_5]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_17407,plain,
% 55.31/7.50      ( m1_subset_1(X0,X1) | ~ m1_subset_1(k2_subset_1(X0),X1) ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_6510,c_5567]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7,plain,
% 55.31/7.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f84]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18605,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_17407,c_7]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14477,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | ~ v3_pre_topc(u1_struct_0(X1),X1)
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2)
% 55.31/7.50      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_19,c_20]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18611,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | ~ v3_pre_topc(u1_struct_0(X1),X1)
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2)
% 55.31/7.50      | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
% 55.31/7.50      inference(backward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_18605,c_14477]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18612,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 55.31/7.50      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_18611]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_35583,plain,
% 55.31/7.50      ( r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 55.31/7.50      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 55.31/7.50      | sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_10903,c_18612]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_35584,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 55.31/7.50      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_35583]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_35591,plain,
% 55.31/7.50      ( sP0(X0,sK6,X1) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
% 55.31/7.50      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_4486,c_35584]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 55.31/7.50      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
% 55.31/7.50      inference(cnf_transformation,[],[f100]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1655,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 55.31/7.50      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7611,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1653,c_1655]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_6,plain,
% 55.31/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.31/7.50      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 55.31/7.50      inference(cnf_transformation,[],[f135]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1667,plain,
% 55.31/7.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_16409,plain,
% 55.31/7.50      ( k5_xboole_0(u1_struct_0(X0),k1_setfam_1(k2_tarski(u1_struct_0(X0),sK3(X1,X0,u1_struct_0(X0))))) = k3_subset_1(u1_struct_0(X0),sK3(X1,X0,u1_struct_0(X0)))
% 55.31/7.50      | sP0(X1,X0,u1_struct_0(X0)) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_7611,c_1667]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_48,negated_conjecture,
% 55.31/7.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 55.31/7.50      inference(cnf_transformation,[],[f123]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1625,plain,
% 55.31/7.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1666,plain,
% 55.31/7.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1683,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 55.31/7.50      inference(light_normalisation,[status(thm)],[c_1666,c_5]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_26,plain,
% 55.31/7.50      ( sP1(X0,X1,X2)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ l1_pre_topc(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f104]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1647,plain,
% 55.31/7.50      ( sP1(X0,X1,X2) = iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7910,plain,
% 55.31/7.50      ( sP1(u1_struct_0(X0),X0,X1) = iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1683,c_1647]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_20683,plain,
% 55.31/7.50      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1625,c_7910]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_9272,plain,
% 55.31/7.50      ( sP1(X0,sK6,sK7)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 55.31/7.50      | ~ l1_pre_topc(sK6) ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_26,c_48]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_9540,plain,
% 55.31/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 55.31/7.50      | sP1(X0,sK6,sK7) ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_9272,c_49]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_9541,plain,
% 55.31/7.50      ( sP1(X0,sK6,sK7)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_9540]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18626,plain,
% 55.31/7.50      ( sP1(u1_struct_0(sK6),sK6,sK7) ),
% 55.31/7.50      inference(resolution,[status(thm)],[c_18605,c_9541]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18627,plain,
% 55.31/7.50      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_18626]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_20763,plain,
% 55.31/7.50      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_20683,c_18627]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_13,plain,
% 55.31/7.50      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | k2_pre_topc(X1,X2) = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f92]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1660,plain,
% 55.31/7.50      ( k2_pre_topc(X0,X1) = X2
% 55.31/7.50      | sP1(X2,X0,X1) != iProver_top
% 55.31/7.50      | sP0(X1,X0,X2) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_20768,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_20763,c_1660]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_28678,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | k5_xboole_0(u1_struct_0(sK6),k1_setfam_1(k2_tarski(u1_struct_0(sK6),sK3(sK7,sK6,u1_struct_0(sK6))))) = k3_subset_1(u1_struct_0(sK6),sK3(sK7,sK6,u1_struct_0(sK6))) ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_16409,c_20768]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_40,plain,
% 55.31/7.50      ( ~ l1_pre_topc(X0)
% 55.31/7.50      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 55.31/7.50      inference(cnf_transformation,[],[f118]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1633,plain,
% 55.31/7.50      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2969,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,k2_struct_0(sK6)) = k2_struct_0(sK6) ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1624,c_1633]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2970,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,u1_struct_0(sK6)) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(light_normalisation,[status(thm)],[c_2969,c_2835]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_29,plain,
% 55.31/7.50      ( v4_pre_topc(X0,X1)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ v2_pre_topc(X1)
% 55.31/7.50      | ~ l1_pre_topc(X1)
% 55.31/7.50      | k2_pre_topc(X1,X0) != X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f108]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1644,plain,
% 55.31/7.50      ( k2_pre_topc(X0,X1) != X1
% 55.31/7.50      | v4_pre_topc(X1,X0) = iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | v2_pre_topc(X0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_10302,plain,
% 55.31/7.50      ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | v2_pre_topc(sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_2970,c_1644]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18578,plain,
% 55.31/7.50      ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_10302,c_51,c_52]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18584,plain,
% 55.31/7.50      ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_18578,c_1683]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_8,plain,
% 55.31/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.31/7.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f85]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1665,plain,
% 55.31/7.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4146,plain,
% 55.31/7.50      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1665]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5199,plain,
% 55.31/7.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1667]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f133]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4,plain,
% 55.31/7.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f134]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1686,plain,
% 55.31/7.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.31/7.50      inference(light_normalisation,[status(thm)],[c_4,c_3]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5212,plain,
% 55.31/7.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 55.31/7.50      inference(light_normalisation,[status(thm)],[c_5199,c_3,c_1686]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7242,plain,
% 55.31/7.50      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 55.31/7.50      inference(light_normalisation,[status(thm)],[c_4146,c_5212]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_42,plain,
% 55.31/7.50      ( ~ v4_pre_topc(X0,X1)
% 55.31/7.50      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ l1_pre_topc(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f119]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1631,plain,
% 55.31/7.50      ( v4_pre_topc(X0,X1) != iProver_top
% 55.31/7.50      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7246,plain,
% 55.31/7.50      ( v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 55.31/7.50      | v3_pre_topc(k1_xboole_0,X0) = iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_7242,c_1631]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_24486,plain,
% 55.31/7.50      ( v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 55.31/7.50      | v3_pre_topc(k1_xboole_0,X0) = iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_7246,c_1683]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_24488,plain,
% 55.31/7.50      ( v4_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 55.31/7.50      | v3_pre_topc(k1_xboole_0,sK6) = iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_24486]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_15,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 55.31/7.50      | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f103]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1658,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 55.31/7.50      | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_6374,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1653,c_1658]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_47,negated_conjecture,
% 55.31/7.50      ( v1_tops_1(sK7,sK6)
% 55.31/7.50      | ~ v3_pre_topc(X0,sK6)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 55.31/7.50      | ~ r1_xboole_0(sK7,X0)
% 55.31/7.50      | k1_xboole_0 = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f124]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1626,plain,
% 55.31/7.50      ( k1_xboole_0 = X0
% 55.31/7.50      | v1_tops_1(sK7,sK6) = iProver_top
% 55.31/7.50      | v3_pre_topc(X0,sK6) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | r1_xboole_0(sK7,X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_16421,plain,
% 55.31/7.50      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) = iProver_top
% 55.31/7.50      | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
% 55.31/7.50      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_7611,c_1626]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_17,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | v3_pre_topc(sK3(X0,X1,X2),X1)
% 55.31/7.50      | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
% 55.31/7.50      inference(cnf_transformation,[],[f101]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1656,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_6366,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1653,c_1656]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_16905,plain,
% 55.31/7.50      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) = iProver_top
% 55.31/7.50      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_16421,c_6366]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_16909,plain,
% 55.31/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_6374,c_16905]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_53,plain,
% 55.31/7.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_104,plain,
% 55.31/7.50      ( l1_struct_0(sK6) | ~ l1_pre_topc(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_28]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_107,plain,
% 55.31/7.50      ( ~ l1_struct_0(sK6) | k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_27]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_37,plain,
% 55.31/7.50      ( v1_tops_1(X0,X1)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ l1_pre_topc(X1)
% 55.31/7.50      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f116]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2230,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6)
% 55.31/7.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 55.31/7.50      | ~ l1_pre_topc(sK6)
% 55.31/7.50      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_37]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2231,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 55.31/7.50      | v1_tops_1(sK7,sK6) = iProver_top
% 55.31/7.50      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_2230]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2412,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) != X0
% 55.31/7.50      | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 55.31/7.50      | k2_struct_0(sK6) != X0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_561]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2800,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 55.31/7.50      | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
% 55.31/7.50      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2412]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_25746,plain,
% 55.31/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | v1_tops_1(sK7,sK6) = iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_16909,c_49,c_52,c_53,c_104,c_107,c_2231,c_2800,
% 55.31/7.50                 c_20768]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_38,plain,
% 55.31/7.50      ( ~ v1_tops_1(X0,X1)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ l1_pre_topc(X1)
% 55.31/7.50      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f115]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1635,plain,
% 55.31/7.50      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 55.31/7.50      | v1_tops_1(X1,X0) != iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4996,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1625,c_1635]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5007,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(light_normalisation,[status(thm)],[c_4996,c_2835]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5912,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_5007,c_52]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5913,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_5912]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_25757,plain,
% 55.31/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_25746,c_5913]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_16,plain,
% 55.31/7.50      ( sP0(X0,X1,X2)
% 55.31/7.50      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f102]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1657,plain,
% 55.31/7.50      ( sP0(X0,X1,X2) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_99694,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_25757,c_1657]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14037,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1))
% 55.31/7.50      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_20]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_57671,plain,
% 55.31/7.50      ( sP0(sK7,sK6,u1_struct_0(sK6))
% 55.31/7.50      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_14037]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_57672,plain,
% 55.31/7.50      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_57671]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_101521,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_99694,c_20768,c_57672]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_35,plain,
% 55.31/7.50      ( ~ v3_pre_topc(X0,X1)
% 55.31/7.50      | ~ r2_hidden(X2,X0)
% 55.31/7.50      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 55.31/7.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 55.31/7.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ r1_xboole_0(X3,X0)
% 55.31/7.50      | ~ l1_pre_topc(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f110]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1638,plain,
% 55.31/7.50      ( v3_pre_topc(X0,X1) != iProver_top
% 55.31/7.50      | r2_hidden(X2,X0) != iProver_top
% 55.31/7.50      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X3,X0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_12,plain,
% 55.31/7.50      ( ~ r2_hidden(X0,X1)
% 55.31/7.50      | m1_subset_1(X0,X2)
% 55.31/7.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f90]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1661,plain,
% 55.31/7.50      ( r2_hidden(X0,X1) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,X2) = iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1989,plain,
% 55.31/7.50      ( v3_pre_topc(X0,X1) != iProver_top
% 55.31/7.50      | r2_hidden(X2,X0) != iProver_top
% 55.31/7.50      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X3,X0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_1638,c_1661]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_13420,plain,
% 55.31/7.50      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 55.31/7.50      | r2_hidden(X1,k2_pre_topc(X0,X2)) != iProver_top
% 55.31/7.50      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1989]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4027,plain,
% 55.31/7.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_3,c_1670]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_9,plain,
% 55.31/7.50      ( ~ r2_hidden(X0,X1)
% 55.31/7.50      | r2_hidden(X0,X2)
% 55.31/7.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 55.31/7.50      inference(cnf_transformation,[],[f86]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1664,plain,
% 55.31/7.50      ( r2_hidden(X0,X1) != iProver_top
% 55.31/7.50      | r2_hidden(X0,X2) = iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_6267,plain,
% 55.31/7.50      ( r2_hidden(X0,X1) = iProver_top
% 55.31/7.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1664]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_44927,plain,
% 55.31/7.50      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 55.31/7.50      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_13420,c_4027,c_6267]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_44935,plain,
% 55.31/7.50      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 55.31/7.50      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1683,c_44927]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_101532,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_101521,c_44935]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_101590,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 55.31/7.50      | v3_pre_topc(k1_xboole_0,sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_101532]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_101863,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_28678,c_52,c_18584,c_24488,c_101590]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_46,negated_conjecture,
% 55.31/7.50      ( ~ v1_tops_1(sK7,sK6)
% 55.31/7.50      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 55.31/7.50      inference(cnf_transformation,[],[f125]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1627,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_13422,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | v3_pre_topc(sK8,sK6) != iProver_top
% 55.31/7.50      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X1,sK8) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1627,c_1989]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_44,negated_conjecture,
% 55.31/7.50      ( ~ v1_tops_1(sK7,sK6) | v3_pre_topc(sK8,sK6) ),
% 55.31/7.50      inference(cnf_transformation,[],[f127]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_59,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | v3_pre_topc(sK8,sK6) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14348,plain,
% 55.31/7.50      ( r1_xboole_0(X1,sK8) != iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top
% 55.31/7.50      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_13422,c_52,c_59]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14349,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X1,sK8) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_14348]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14362,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top
% 55.31/7.50      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1625,c_14349]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_43,negated_conjecture,
% 55.31/7.50      ( ~ v1_tops_1(sK7,sK6) | r1_xboole_0(sK7,sK8) ),
% 55.31/7.50      inference(cnf_transformation,[],[f128]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_60,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14520,plain,
% 55.31/7.50      ( r2_hidden(X0,sK8) != iProver_top
% 55.31/7.50      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_14362,c_60]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14521,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_14520]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_101997,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top ),
% 55.31/7.50      inference(demodulation,[status(thm)],[c_101863,c_14521]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_6268,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r2_hidden(X0,sK8) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1627,c_1664]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_102921,plain,
% 55.31/7.50      ( r2_hidden(X0,sK8) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_101997,c_49,c_52,c_53,c_104,c_107,c_2231,c_2800,
% 55.31/7.50                 c_6268,c_18584,c_24488,c_101590]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_185286,plain,
% 55.31/7.50      ( sP0(X0,sK6,sK8) = iProver_top
% 55.31/7.50      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_35591,c_102921]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_187544,plain,
% 55.31/7.50      ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_4028,c_185286]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_97998,plain,
% 55.31/7.50      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_561]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_103309,plain,
% 55.31/7.50      ( X0 != k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | k1_xboole_0 = X0
% 55.31/7.50      | k1_xboole_0 != k1_setfam_1(k2_tarski(sK7,sK8)) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_97998]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_140877,plain,
% 55.31/7.50      ( sK8 != k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | k1_xboole_0 != k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | k1_xboole_0 = sK8 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_103309]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_101232,plain,
% 55.31/7.50      ( X0 != X1
% 55.31/7.50      | X0 = k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) != X1 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_561]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_105648,plain,
% 55.31/7.50      ( X0 = k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | X0 != k1_xboole_0
% 55.31/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) != k1_xboole_0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_101232]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_140728,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) != k1_xboole_0
% 55.31/7.50      | sK8 = k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | sK8 != k1_xboole_0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_105648]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1630,plain,
% 55.31/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_25761,plain,
% 55.31/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_25746,c_1630]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1,plain,
% 55.31/7.50      ( ~ r1_xboole_0(X0,X1)
% 55.31/7.50      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f131]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1669,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 55.31/7.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_25919,plain,
% 55.31/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 55.31/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_25761,c_1669]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_16417,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) != iProver_top
% 55.31/7.50      | r2_hidden(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 55.31/7.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X3,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_7611,c_1989]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_72156,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | r2_hidden(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 55.31/7.50      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X3,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_16417,c_6366]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_72168,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),k2_pre_topc(X1,X2)) != iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1657,c_72156]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_14042,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_14037]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_78281,plain,
% 55.31/7.50      ( r2_hidden(sK2(X0,X1,u1_struct_0(X1)),k2_pre_topc(X1,X2)) != iProver_top
% 55.31/7.50      | sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_72168,c_14042]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_78282,plain,
% 55.31/7.50      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),k2_pre_topc(X1,X2)) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | r1_xboole_0(X2,sK3(X0,X1,u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_78281]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_78312,plain,
% 55.31/7.50      ( sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_2970,c_78282]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_574,plain,
% 55.31/7.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 55.31/7.50      theory(equality) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_590,plain,
% 55.31/7.50      ( u1_struct_0(sK6) = u1_struct_0(sK6) | sK6 != sK6 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_574]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_595,plain,
% 55.31/7.50      ( sK6 = sK6 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_560]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2202,plain,
% 55.31/7.50      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_7]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2207,plain,
% 55.31/7.50      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2209,plain,
% 55.31/7.50      ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2207]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2603,plain,
% 55.31/7.50      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_560]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2942,plain,
% 55.31/7.50      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2603]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_4217,plain,
% 55.31/7.50      ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_5]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2670,plain,
% 55.31/7.50      ( X0 != X1 | X0 = k2_subset_1(X2) | k2_subset_1(X2) != X1 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_561]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3872,plain,
% 55.31/7.50      ( X0 != X1
% 55.31/7.50      | X0 = k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k2_subset_1(u1_struct_0(sK6)) != X1 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2670]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7559,plain,
% 55.31/7.50      ( X0 != u1_struct_0(sK6)
% 55.31/7.50      | X0 = k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_3872]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_17097,plain,
% 55.31/7.50      ( u1_struct_0(sK6) != u1_struct_0(sK6)
% 55.31/7.50      | u1_struct_0(sK6) = k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_7559]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2277,plain,
% 55.31/7.50      ( m1_subset_1(X0,X1)
% 55.31/7.50      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 55.31/7.50      | X1 != k1_zfmisc_1(X2)
% 55.31/7.50      | X0 != k2_subset_1(X2) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_568]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3319,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.31/7.50      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 55.31/7.50      | X0 != k2_subset_1(X2)
% 55.31/7.50      | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2277]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5774,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 55.31/7.50      | X0 != k2_subset_1(X2)
% 55.31/7.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_3319]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_8929,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 55.31/7.50      | X0 != k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_5774]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_48535,plain,
% 55.31/7.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 55.31/7.50      | u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_8929]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_48544,plain,
% 55.31/7.50      ( u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6))
% 55.31/7.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 55.31/7.50      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_48535]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_48546,plain,
% 55.31/7.50      ( u1_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
% 55.31/7.50      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 55.31/7.50      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_48544]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_99542,plain,
% 55.31/7.50      ( r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_78312,c_52,c_590,c_595,c_2209,c_2942,c_4217,c_17097,
% 55.31/7.50                 c_48546]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_99543,plain,
% 55.31/7.50      ( sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r2_hidden(sK2(X0,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_99542]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_99551,plain,
% 55.31/7.50      ( sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r1_xboole_0(u1_struct_0(sK6),sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_99543,c_1653]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_99556,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 55.31/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 55.31/7.50      | r1_xboole_0(u1_struct_0(sK6),k1_xboole_0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_25919,c_99551]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_27497,plain,
% 55.31/7.50      ( ~ r1_xboole_0(sK7,sK8)
% 55.31/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_1]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_100973,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 55.31/7.50      | r1_xboole_0(u1_struct_0(sK6),k1_xboole_0) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_99556,c_49,c_48,c_43,c_104,c_107,c_2230,c_2800,
% 55.31/7.50                 c_20768,c_27497,c_99722]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_100979,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_100973,c_4027]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_36,plain,
% 55.31/7.50      ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
% 55.31/7.50      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 55.31/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ v2_struct_0(X1)
% 55.31/7.50      | ~ l1_pre_topc(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f109]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1637,plain,
% 55.31/7.50      ( r2_hidden(X0,k2_pre_topc(X1,X2)) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 55.31/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | v2_struct_0(X1) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7398,plain,
% 55.31/7.50      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | v2_struct_0(sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_2970,c_1637]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_19759,plain,
% 55.31/7.50      ( v2_struct_0(sK6) != iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_7398,c_52]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_19760,plain,
% 55.31/7.50      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | v2_struct_0(sK6) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_19759]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5489,plain,
% 55.31/7.50      ( r2_hidden(X0,X1) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,X1) = iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1683,c_1661]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_19769,plain,
% 55.31/7.50      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 55.31/7.50      | v2_struct_0(sK6) != iProver_top ),
% 55.31/7.50      inference(forward_subsumption_resolution,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_19760,c_1683,c_5489]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_19773,plain,
% 55.31/7.50      ( sP0(X0,sK6,X1) = iProver_top | v2_struct_0(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1653,c_19769]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7907,plain,
% 55.31/7.50      ( sP1(k1_xboole_0,X0,X1) = iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1647]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_18917,plain,
% 55.31/7.50      ( sP1(k1_xboole_0,X0,k1_xboole_0) = iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_7907]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_19002,plain,
% 55.31/7.50      ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
% 55.31/7.50      | sP0(k1_xboole_0,X0,k1_xboole_0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_18917,c_1660]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_20514,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 55.31/7.50      | v2_struct_0(sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_19773,c_19002]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2212,plain,
% 55.31/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_10]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2217,plain,
% 55.31/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_2212]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2219,plain,
% 55.31/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2217]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_41,plain,
% 55.31/7.50      ( v4_pre_topc(X0,X1)
% 55.31/7.50      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ l1_pre_topc(X1) ),
% 55.31/7.50      inference(cnf_transformation,[],[f120]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1632,plain,
% 55.31/7.50      ( v4_pre_topc(X0,X1) = iProver_top
% 55.31/7.50      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X1) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5218,plain,
% 55.31/7.50      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 55.31/7.50      | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 55.31/7.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_5212,c_1632]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_5237,plain,
% 55.31/7.50      ( v4_pre_topc(k1_xboole_0,sK6) = iProver_top
% 55.31/7.50      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 55.31/7.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_5218]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_30,plain,
% 55.31/7.50      ( ~ v4_pre_topc(X0,X1)
% 55.31/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.31/7.50      | ~ l1_pre_topc(X1)
% 55.31/7.50      | k2_pre_topc(X1,X0) = X0 ),
% 55.31/7.50      inference(cnf_transformation,[],[f107]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_1643,plain,
% 55.31/7.50      ( k2_pre_topc(X0,X1) = X1
% 55.31/7.50      | v4_pre_topc(X1,X0) != iProver_top
% 55.31/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7407,plain,
% 55.31/7.50      ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
% 55.31/7.50      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 55.31/7.50      | l1_pre_topc(X0) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_1643]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7438,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 55.31/7.50      | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_7407]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_91726,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_20514,c_51,c_52,c_2219,c_3840,c_5237,c_7438]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_7908,plain,
% 55.31/7.50      ( sP1(sK8,sK6,X0) = iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1627,c_1647]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_8503,plain,
% 55.31/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | sP1(sK8,sK6,X0) = iProver_top ),
% 55.31/7.50      inference(global_propositional_subsumption,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_7908,c_52]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_8504,plain,
% 55.31/7.50      ( sP1(sK8,sK6,X0) = iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 55.31/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 55.31/7.50      inference(renaming,[status(thm)],[c_8503]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_8512,plain,
% 55.31/7.50      ( sP1(sK8,sK6,k1_xboole_0) = iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_1663,c_8504]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_9806,plain,
% 55.31/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = sK8
% 55.31/7.50      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 55.31/7.50      inference(superposition,[status(thm)],[c_8512,c_1660]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_91731,plain,
% 55.31/7.50      ( sK8 = k1_xboole_0
% 55.31/7.50      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 55.31/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 55.31/7.50      inference(demodulation,[status(thm)],[c_91726,c_9806]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_2523,plain,
% 55.31/7.50      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_561]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3029,plain,
% 55.31/7.50      ( X0 != k1_xboole_0
% 55.31/7.50      | k1_xboole_0 = X0
% 55.31/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_2523]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_70500,plain,
% 55.31/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) != k1_xboole_0
% 55.31/7.50      | k1_xboole_0 = k1_setfam_1(k2_tarski(sK7,sK8))
% 55.31/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_3029]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_3030,plain,
% 55.31/7.50      ( k1_xboole_0 = k1_xboole_0 ),
% 55.31/7.50      inference(instantiation,[status(thm)],[c_560]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(c_45,negated_conjecture,
% 55.31/7.50      ( ~ v1_tops_1(sK7,sK6) | k1_xboole_0 != sK8 ),
% 55.31/7.50      inference(cnf_transformation,[],[f126]) ).
% 55.31/7.50  
% 55.31/7.50  cnf(contradiction,plain,
% 55.31/7.50      ( $false ),
% 55.31/7.50      inference(minisat,
% 55.31/7.50                [status(thm)],
% 55.31/7.50                [c_187544,c_140877,c_140728,c_101590,c_100979,c_91731,
% 55.31/7.50                 c_70500,c_24488,c_18584,c_3030,c_2800,c_2231,c_2230,
% 55.31/7.50                 c_107,c_104,c_45,c_53,c_48,c_52,c_49]) ).
% 55.31/7.50  
% 55.31/7.50  
% 55.31/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.31/7.50  
% 55.31/7.50  ------                               Statistics
% 55.31/7.50  
% 55.31/7.50  ------ Selected
% 55.31/7.50  
% 55.31/7.50  total_time:                             6.669
% 55.31/7.50  
%------------------------------------------------------------------------------
