%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:51 EST 2020

% Result     : Theorem 27.43s
% Output     : CNFRefutation 27.43s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1477)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f127,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f84,f76])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f112,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f23,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,
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

fof(f70,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f66,f69,f68,f67])).

fof(f115,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f116,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
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

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f52,f55,f54,f53])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_xboole_0(X0,X5)
      | ~ r2_hidden(sK2(X0,X1,X2),X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_xboole_0(X0,sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK7,X3)
      | ~ v3_pre_topc(X3,sK6)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | v1_tops_1(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f70])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X1,X2) = X0
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f31,f45,f44])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f86])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f60,plain,(
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

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f59,f60])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f88,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X0,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f121,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f122,plain,
    ( r1_xboole_0(sK7,sK8)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,
    ( k1_xboole_0 != sK8
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_5,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9066,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_5])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_8528,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8576,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8528,c_12])).

cnf(c_10692,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9066,c_8576])).

cnf(c_40,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_50,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_637,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_50])).

cnf(c_638,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_49,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_68,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_640,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_50,c_49,c_68])).

cnf(c_8503,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_29,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_28,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_623,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_29,c_28])).

cnf(c_928,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_623,c_49])).

cnf(c_929,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_8537,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8503,c_929])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_8515,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X3)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_8516,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14393,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8515,c_8516])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8525,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8525,c_6])).

cnf(c_26090,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14393,c_8544])).

cnf(c_26094,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8537,c_26090])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_8520,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13306,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8515,c_8520])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_8517,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13400,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8515,c_8517])).

cnf(c_47,negated_conjecture,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(sK7,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_8505,plain,
    ( k1_xboole_0 = X0
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_18824,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13400,c_8505])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2)
    | v3_pre_topc(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_8518,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12748,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8515,c_8518])).

cnf(c_19573,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18824,c_12748])).

cnf(c_19577,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_13306,c_19573])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_53,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_101,plain,
    ( l1_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_104,plain,
    ( ~ l1_struct_0(sK6)
    | k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_969,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_49])).

cnf(c_970,plain,
    ( v1_tops_1(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) != k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_8897,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_8898,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8897])).

cnf(c_7580,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9037,plain,
    ( k2_pre_topc(sK6,sK7) != X0
    | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_7580])).

cnf(c_9264,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_9037])).

cnf(c_8504,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k2_pre_topc(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1094,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_49])).

cnf(c_1095,plain,
    ( sP1(X0,sK6,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_1094])).

cnf(c_1162,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
    | X3 != X2
    | X4 != X0
    | k2_pre_topc(X1,X0) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_1095])).

cnf(c_1163,plain,
    ( ~ sP0(X0,sK6,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1162])).

cnf(c_8492,plain,
    ( k2_pre_topc(sK6,X0) = X1
    | sP0(X0,sK6,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_9435,plain,
    ( k2_pre_topc(sK6,sK7) = X0
    | sP0(sK7,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8504,c_8492])).

cnf(c_9770,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_9435])).

cnf(c_82123,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19577,c_49,c_53,c_101,c_104,c_8898,c_9264,c_9770])).

cnf(c_39,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_954,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_49])).

cnf(c_955,plain,
    ( ~ v1_tops_1(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) = k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_8499,plain,
    ( k2_pre_topc(sK6,X0) = k2_struct_0(sK6)
    | v1_tops_1(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_955])).

cnf(c_8612,plain,
    ( k2_pre_topc(sK6,X0) = u1_struct_0(sK6)
    | v1_tops_1(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8499,c_929])).

cnf(c_9163,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8504,c_8612])).

cnf(c_82155,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_82123,c_9163])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_8519,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_82450,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_82155,c_8519])).

cnf(c_7592,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_7608,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7592])).

cnf(c_7579,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7614,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_7579])).

cnf(c_15,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1180,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
    | X3 != X0
    | k2_pre_topc(X1,X0) != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_1095])).

cnf(c_1181,plain,
    ( sP0(X0,sK6,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k2_pre_topc(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_1180])).

cnf(c_8909,plain,
    ( sP0(sK7,sK6,k2_pre_topc(sK6,sK7))
    | ~ m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_8910,plain,
    ( sP0(sK7,sK6,k2_pre_topc(sK6,sK7)) = iProver_top
    | m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8909])).

cnf(c_8948,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8954,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8948])).

cnf(c_9288,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_7579])).

cnf(c_9943,plain,
    ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9214,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK6)
    | k2_struct_0(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_7580])).

cnf(c_9602,plain,
    ( X0 = k2_struct_0(sK6)
    | X0 != u1_struct_0(sK6)
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_9214])).

cnf(c_9952,plain,
    ( k2_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK6) = k2_struct_0(sK6)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_9602])).

cnf(c_9118,plain,
    ( sP0(sK7,sK6,X0)
    | r2_hidden(sK2(sK7,sK6,X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_17381,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6))
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_9118])).

cnf(c_17384,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17381])).

cnf(c_7586,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9007,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_7586])).

cnf(c_9704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_9007])).

cnf(c_11110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_9704])).

cnf(c_28637,plain,
    ( m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,sK7) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_11110])).

cnf(c_28638,plain,
    ( k2_pre_topc(sK6,sK7) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28637])).

cnf(c_9266,plain,
    ( X0 != X1
    | k2_struct_0(sK6) != X1
    | k2_struct_0(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_7580])).

cnf(c_10442,plain,
    ( X0 != u1_struct_0(sK6)
    | k2_struct_0(sK6) = X0
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_9266])).

cnf(c_32641,plain,
    ( k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
    | k2_struct_0(sK6) = k2_pre_topc(sK6,sK7)
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_10442])).

cnf(c_11295,plain,
    ( X0 != X1
    | X0 = k2_subset_1(X2)
    | k2_subset_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_7580])).

cnf(c_14052,plain,
    ( X0 != X1
    | X0 = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_11295])).

cnf(c_19649,plain,
    ( X0 != u1_struct_0(sK6)
    | X0 = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_14052])).

cnf(c_39951,plain,
    ( k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_19649])).

cnf(c_7590,plain,
    ( ~ sP0(X0,X1,X2)
    | sP0(X0,X3,X4)
    | X3 != X1
    | X4 != X2 ),
    theory(equality)).

cnf(c_9141,plain,
    ( ~ sP0(sK7,X0,X1)
    | sP0(sK7,sK6,X2)
    | X2 != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_7590])).

cnf(c_9456,plain,
    ( ~ sP0(sK7,X0,X1)
    | sP0(sK7,sK6,k2_struct_0(sK6))
    | k2_struct_0(sK6) != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_9141])).

cnf(c_57935,plain,
    ( ~ sP0(sK7,X0,k2_pre_topc(sK6,sK7))
    | sP0(sK7,sK6,k2_struct_0(sK6))
    | k2_struct_0(sK6) != k2_pre_topc(sK6,sK7)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_9456])).

cnf(c_57940,plain,
    ( k2_struct_0(sK6) != k2_pre_topc(sK6,sK7)
    | sK6 != X0
    | sP0(sK7,X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | sP0(sK7,sK6,k2_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57935])).

cnf(c_57942,plain,
    ( k2_struct_0(sK6) != k2_pre_topc(sK6,sK7)
    | sK6 != sK6
    | sP0(sK7,sK6,k2_pre_topc(sK6,sK7)) != iProver_top
    | sP0(sK7,sK6,k2_struct_0(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57940])).

cnf(c_28299,plain,
    ( sP0(sK7,sK6,X0)
    | ~ sP0(sK7,sK6,k2_struct_0(sK6))
    | X0 != k2_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_9141])).

cnf(c_59169,plain,
    ( ~ sP0(sK7,sK6,k2_struct_0(sK6))
    | sP0(sK7,sK6,u1_struct_0(sK6))
    | u1_struct_0(sK6) != k2_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_28299])).

cnf(c_59170,plain,
    ( u1_struct_0(sK6) != k2_struct_0(sK6)
    | sK6 != sK6
    | sP0(sK7,sK6,k2_struct_0(sK6)) != iProver_top
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59169])).

cnf(c_103012,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_82450,c_49,c_53,c_101,c_104,c_7608,c_7614,c_8910,c_8954,c_9288,c_9943,c_9952,c_17384,c_28638,c_32641,c_39951,c_57942,c_59170])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8522,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_8526,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11794,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8522,c_8526])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11819,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11794,c_4])).

cnf(c_41,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_31,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_723,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_41,c_31])).

cnf(c_913,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_723,c_49])).

cnf(c_914,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_8501,plain,
    ( k2_pre_topc(sK6,X0) = X0
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_11902,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11819,c_8501])).

cnf(c_8928,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8934,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8928])).

cnf(c_12232,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11902,c_8537,c_8934])).

cnf(c_36,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1002,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_49])).

cnf(c_1003,plain,
    ( ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(X2,X0) ),
    inference(unflattening,[status(thm)],[c_1002])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1021,plain,
    ( ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1003,c_13])).

cnf(c_8496,plain,
    ( v3_pre_topc(X0,sK6) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK6,X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_10506,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8496])).

cnf(c_25259,plain,
    ( r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10506,c_8537])).

cnf(c_25281,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12232,c_25259])).

cnf(c_9404,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7579])).

cnf(c_8979,plain,
    ( r1_xboole_0(k1_xboole_0,X0)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13072,plain,
    ( r1_xboole_0(k1_xboole_0,k2_struct_0(X0))
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(X0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8979])).

cnf(c_13073,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(X0))) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k2_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13072])).

cnf(c_13075,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(sK6))) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k2_struct_0(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13073])).

cnf(c_8980,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_21894,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(X0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8980])).

cnf(c_21895,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(sK6))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21894])).

cnf(c_7583,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9365,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k1_xboole_0,X2)
    | X1 != X2
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7583])).

cnf(c_11055,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | r1_xboole_0(k1_xboole_0,X1)
    | X1 != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9365])).

cnf(c_29456,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6))
    | u1_struct_0(sK6) != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11055])).

cnf(c_59643,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0(sK6))
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6))
    | u1_struct_0(sK6) != k2_struct_0(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_29456])).

cnf(c_59644,plain,
    ( u1_struct_0(sK6) != k2_struct_0(sK6)
    | k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k2_struct_0(sK6)) != iProver_top
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59643])).

cnf(c_68338,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25281,c_49,c_101,c_104,c_7608,c_7614,c_8934,c_9404,c_9952,c_13075,c_21895,c_59644])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8523,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12701,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8522,c_8523])).

cnf(c_68346,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_68338,c_12701])).

cnf(c_103018,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_103012,c_68346])).

cnf(c_46,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_8506,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8510,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | r2_hidden(X4,X2) != iProver_top
    | r2_hidden(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8790,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | r2_hidden(X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8510,c_8523])).

cnf(c_15916,plain,
    ( sP0(X0,sK6,X1) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK8) != iProver_top
    | r1_xboole_0(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8506,c_8790])).

cnf(c_44,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | v3_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_59,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_16524,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | sP0(X0,sK6,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK8) != iProver_top
    | r1_xboole_0(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15916,c_59])).

cnf(c_16525,plain,
    ( sP0(X0,sK6,X1) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK8) != iProver_top
    | r1_xboole_0(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_16524])).

cnf(c_103026,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_103018,c_16525])).

cnf(c_43,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | r1_xboole_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_xboole_0(sK7,sK8)
    | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
    | sK6 != sK6
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_970])).

cnf(c_1476,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_xboole_0(sK7,sK8)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1475])).

cnf(c_1478,plain,
    ( r1_xboole_0(sK7,sK8)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1476,c_48])).

cnf(c_1480,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_12702,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8506,c_8523])).

cnf(c_103079,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103026,c_49,c_53,c_101,c_104,c_1477,c_8898,c_9264,c_9770,c_12702,c_103018])).

cnf(c_103087,plain,
    ( sP0(X0,sK6,sK8) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26094,c_103079])).

cnf(c_105233,plain,
    ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_10692,c_103087])).

cnf(c_9490,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = X0
    | sP0(k1_xboole_0,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8522,c_8492])).

cnf(c_17022,plain,
    ( k1_xboole_0 = X0
    | sP0(k1_xboole_0,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9490,c_12232])).

cnf(c_17030,plain,
    ( sK8 = k1_xboole_0
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8506,c_17022])).

cnf(c_45,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
    | sK6 != sK6
    | sK8 != k1_xboole_0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_970])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | sK8 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1450])).

cnf(c_1453,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | sK8 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1451,c_48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_105233,c_103018,c_17030,c_9770,c_9264,c_8898,c_1453,c_104,c_101,c_53,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:08:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.43/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.43/3.99  
% 27.43/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.43/3.99  
% 27.43/3.99  ------  iProver source info
% 27.43/3.99  
% 27.43/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.43/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.43/3.99  git: non_committed_changes: false
% 27.43/3.99  git: last_make_outside_of_git: false
% 27.43/3.99  
% 27.43/3.99  ------ 
% 27.43/3.99  
% 27.43/3.99  ------ Input Options
% 27.43/3.99  
% 27.43/3.99  --out_options                           all
% 27.43/3.99  --tptp_safe_out                         true
% 27.43/3.99  --problem_path                          ""
% 27.43/3.99  --include_path                          ""
% 27.43/3.99  --clausifier                            res/vclausify_rel
% 27.43/3.99  --clausifier_options                    --mode clausify
% 27.43/3.99  --stdin                                 false
% 27.43/3.99  --stats_out                             all
% 27.43/3.99  
% 27.43/3.99  ------ General Options
% 27.43/3.99  
% 27.43/3.99  --fof                                   false
% 27.43/3.99  --time_out_real                         305.
% 27.43/3.99  --time_out_virtual                      -1.
% 27.43/3.99  --symbol_type_check                     false
% 27.43/3.99  --clausify_out                          false
% 27.43/3.99  --sig_cnt_out                           false
% 27.43/3.99  --trig_cnt_out                          false
% 27.43/3.99  --trig_cnt_out_tolerance                1.
% 27.43/3.99  --trig_cnt_out_sk_spl                   false
% 27.43/3.99  --abstr_cl_out                          false
% 27.43/3.99  
% 27.43/3.99  ------ Global Options
% 27.43/3.99  
% 27.43/3.99  --schedule                              default
% 27.43/3.99  --add_important_lit                     false
% 27.43/3.99  --prop_solver_per_cl                    1000
% 27.43/3.99  --min_unsat_core                        false
% 27.43/3.99  --soft_assumptions                      false
% 27.43/3.99  --soft_lemma_size                       3
% 27.43/3.99  --prop_impl_unit_size                   0
% 27.43/3.99  --prop_impl_unit                        []
% 27.43/3.99  --share_sel_clauses                     true
% 27.43/3.99  --reset_solvers                         false
% 27.43/3.99  --bc_imp_inh                            [conj_cone]
% 27.43/3.99  --conj_cone_tolerance                   3.
% 27.43/3.99  --extra_neg_conj                        none
% 27.43/3.99  --large_theory_mode                     true
% 27.43/3.99  --prolific_symb_bound                   200
% 27.43/3.99  --lt_threshold                          2000
% 27.43/3.99  --clause_weak_htbl                      true
% 27.43/3.99  --gc_record_bc_elim                     false
% 27.43/3.99  
% 27.43/3.99  ------ Preprocessing Options
% 27.43/3.99  
% 27.43/3.99  --preprocessing_flag                    true
% 27.43/3.99  --time_out_prep_mult                    0.1
% 27.43/3.99  --splitting_mode                        input
% 27.43/3.99  --splitting_grd                         true
% 27.43/3.99  --splitting_cvd                         false
% 27.43/3.99  --splitting_cvd_svl                     false
% 27.43/3.99  --splitting_nvd                         32
% 27.43/3.99  --sub_typing                            true
% 27.43/3.99  --prep_gs_sim                           true
% 27.43/3.99  --prep_unflatten                        true
% 27.43/3.99  --prep_res_sim                          true
% 27.43/3.99  --prep_upred                            true
% 27.43/3.99  --prep_sem_filter                       exhaustive
% 27.43/3.99  --prep_sem_filter_out                   false
% 27.43/3.99  --pred_elim                             true
% 27.43/3.99  --res_sim_input                         true
% 27.43/3.99  --eq_ax_congr_red                       true
% 27.43/3.99  --pure_diseq_elim                       true
% 27.43/3.99  --brand_transform                       false
% 27.43/3.99  --non_eq_to_eq                          false
% 27.43/3.99  --prep_def_merge                        true
% 27.43/3.99  --prep_def_merge_prop_impl              false
% 27.43/3.99  --prep_def_merge_mbd                    true
% 27.43/3.99  --prep_def_merge_tr_red                 false
% 27.43/3.99  --prep_def_merge_tr_cl                  false
% 27.43/3.99  --smt_preprocessing                     true
% 27.43/3.99  --smt_ac_axioms                         fast
% 27.43/3.99  --preprocessed_out                      false
% 27.43/3.99  --preprocessed_stats                    false
% 27.43/3.99  
% 27.43/3.99  ------ Abstraction refinement Options
% 27.43/3.99  
% 27.43/3.99  --abstr_ref                             []
% 27.43/3.99  --abstr_ref_prep                        false
% 27.43/3.99  --abstr_ref_until_sat                   false
% 27.43/3.99  --abstr_ref_sig_restrict                funpre
% 27.43/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.43/3.99  --abstr_ref_under                       []
% 27.43/3.99  
% 27.43/3.99  ------ SAT Options
% 27.43/3.99  
% 27.43/3.99  --sat_mode                              false
% 27.43/3.99  --sat_fm_restart_options                ""
% 27.43/3.99  --sat_gr_def                            false
% 27.43/3.99  --sat_epr_types                         true
% 27.43/3.99  --sat_non_cyclic_types                  false
% 27.43/3.99  --sat_finite_models                     false
% 27.43/3.99  --sat_fm_lemmas                         false
% 27.43/3.99  --sat_fm_prep                           false
% 27.43/3.99  --sat_fm_uc_incr                        true
% 27.43/3.99  --sat_out_model                         small
% 27.43/3.99  --sat_out_clauses                       false
% 27.43/3.99  
% 27.43/3.99  ------ QBF Options
% 27.43/3.99  
% 27.43/3.99  --qbf_mode                              false
% 27.43/3.99  --qbf_elim_univ                         false
% 27.43/3.99  --qbf_dom_inst                          none
% 27.43/3.99  --qbf_dom_pre_inst                      false
% 27.43/3.99  --qbf_sk_in                             false
% 27.43/3.99  --qbf_pred_elim                         true
% 27.43/3.99  --qbf_split                             512
% 27.43/3.99  
% 27.43/3.99  ------ BMC1 Options
% 27.43/3.99  
% 27.43/3.99  --bmc1_incremental                      false
% 27.43/3.99  --bmc1_axioms                           reachable_all
% 27.43/3.99  --bmc1_min_bound                        0
% 27.43/3.99  --bmc1_max_bound                        -1
% 27.43/3.99  --bmc1_max_bound_default                -1
% 27.43/3.99  --bmc1_symbol_reachability              true
% 27.43/3.99  --bmc1_property_lemmas                  false
% 27.43/3.99  --bmc1_k_induction                      false
% 27.43/3.99  --bmc1_non_equiv_states                 false
% 27.43/3.99  --bmc1_deadlock                         false
% 27.43/3.99  --bmc1_ucm                              false
% 27.43/3.99  --bmc1_add_unsat_core                   none
% 27.43/3.99  --bmc1_unsat_core_children              false
% 27.43/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.43/3.99  --bmc1_out_stat                         full
% 27.43/3.99  --bmc1_ground_init                      false
% 27.43/3.99  --bmc1_pre_inst_next_state              false
% 27.43/3.99  --bmc1_pre_inst_state                   false
% 27.43/3.99  --bmc1_pre_inst_reach_state             false
% 27.43/3.99  --bmc1_out_unsat_core                   false
% 27.43/3.99  --bmc1_aig_witness_out                  false
% 27.43/3.99  --bmc1_verbose                          false
% 27.43/3.99  --bmc1_dump_clauses_tptp                false
% 27.43/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.43/3.99  --bmc1_dump_file                        -
% 27.43/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.43/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.43/3.99  --bmc1_ucm_extend_mode                  1
% 27.43/3.99  --bmc1_ucm_init_mode                    2
% 27.43/3.99  --bmc1_ucm_cone_mode                    none
% 27.43/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.43/3.99  --bmc1_ucm_relax_model                  4
% 27.43/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.43/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.43/3.99  --bmc1_ucm_layered_model                none
% 27.43/3.99  --bmc1_ucm_max_lemma_size               10
% 27.43/3.99  
% 27.43/3.99  ------ AIG Options
% 27.43/3.99  
% 27.43/3.99  --aig_mode                              false
% 27.43/3.99  
% 27.43/3.99  ------ Instantiation Options
% 27.43/3.99  
% 27.43/3.99  --instantiation_flag                    true
% 27.43/3.99  --inst_sos_flag                         false
% 27.43/3.99  --inst_sos_phase                        true
% 27.43/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.43/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.43/3.99  --inst_lit_sel_side                     num_symb
% 27.43/3.99  --inst_solver_per_active                1400
% 27.43/3.99  --inst_solver_calls_frac                1.
% 27.43/3.99  --inst_passive_queue_type               priority_queues
% 27.43/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.43/3.99  --inst_passive_queues_freq              [25;2]
% 27.43/3.99  --inst_dismatching                      true
% 27.43/3.99  --inst_eager_unprocessed_to_passive     true
% 27.43/3.99  --inst_prop_sim_given                   true
% 27.43/3.99  --inst_prop_sim_new                     false
% 27.43/3.99  --inst_subs_new                         false
% 27.43/3.99  --inst_eq_res_simp                      false
% 27.43/3.99  --inst_subs_given                       false
% 27.43/3.99  --inst_orphan_elimination               true
% 27.43/3.99  --inst_learning_loop_flag               true
% 27.43/3.99  --inst_learning_start                   3000
% 27.43/3.99  --inst_learning_factor                  2
% 27.43/3.99  --inst_start_prop_sim_after_learn       3
% 27.43/3.99  --inst_sel_renew                        solver
% 27.43/3.99  --inst_lit_activity_flag                true
% 27.43/3.99  --inst_restr_to_given                   false
% 27.43/3.99  --inst_activity_threshold               500
% 27.43/3.99  --inst_out_proof                        true
% 27.43/3.99  
% 27.43/3.99  ------ Resolution Options
% 27.43/3.99  
% 27.43/3.99  --resolution_flag                       true
% 27.43/3.99  --res_lit_sel                           adaptive
% 27.43/3.99  --res_lit_sel_side                      none
% 27.43/3.99  --res_ordering                          kbo
% 27.43/3.99  --res_to_prop_solver                    active
% 27.43/3.99  --res_prop_simpl_new                    false
% 27.43/3.99  --res_prop_simpl_given                  true
% 27.43/3.99  --res_passive_queue_type                priority_queues
% 27.43/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.43/3.99  --res_passive_queues_freq               [15;5]
% 27.43/3.99  --res_forward_subs                      full
% 27.43/3.99  --res_backward_subs                     full
% 27.43/3.99  --res_forward_subs_resolution           true
% 27.43/3.99  --res_backward_subs_resolution          true
% 27.43/3.99  --res_orphan_elimination                true
% 27.43/3.99  --res_time_limit                        2.
% 27.43/3.99  --res_out_proof                         true
% 27.43/3.99  
% 27.43/3.99  ------ Superposition Options
% 27.43/3.99  
% 27.43/3.99  --superposition_flag                    true
% 27.43/3.99  --sup_passive_queue_type                priority_queues
% 27.43/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.43/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.43/3.99  --demod_completeness_check              fast
% 27.43/3.99  --demod_use_ground                      true
% 27.43/3.99  --sup_to_prop_solver                    passive
% 27.43/3.99  --sup_prop_simpl_new                    true
% 27.43/3.99  --sup_prop_simpl_given                  true
% 27.43/3.99  --sup_fun_splitting                     false
% 27.43/3.99  --sup_smt_interval                      50000
% 27.43/3.99  
% 27.43/3.99  ------ Superposition Simplification Setup
% 27.43/3.99  
% 27.43/3.99  --sup_indices_passive                   []
% 27.43/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.43/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.43/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.43/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.43/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.43/3.99  --sup_full_bw                           [BwDemod]
% 27.43/3.99  --sup_immed_triv                        [TrivRules]
% 27.43/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.43/3.99  --sup_immed_bw_main                     []
% 27.43/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.43/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.43/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.43/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.43/3.99  
% 27.43/3.99  ------ Combination Options
% 27.43/3.99  
% 27.43/3.99  --comb_res_mult                         3
% 27.43/3.99  --comb_sup_mult                         2
% 27.43/3.99  --comb_inst_mult                        10
% 27.43/3.99  
% 27.43/3.99  ------ Debug Options
% 27.43/3.99  
% 27.43/3.99  --dbg_backtrace                         false
% 27.43/3.99  --dbg_dump_prop_clauses                 false
% 27.43/3.99  --dbg_dump_prop_clauses_file            -
% 27.43/3.99  --dbg_out_stat                          false
% 27.43/3.99  ------ Parsing...
% 27.43/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.43/3.99  
% 27.43/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.43/3.99  
% 27.43/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.43/3.99  
% 27.43/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.43/3.99  ------ Proving...
% 27.43/3.99  ------ Problem Properties 
% 27.43/3.99  
% 27.43/3.99  
% 27.43/3.99  clauses                                 45
% 27.43/3.99  conjectures                             6
% 27.43/3.99  EPR                                     3
% 27.43/3.99  Horn                                    30
% 27.43/3.99  unary                                   11
% 27.43/3.99  binary                                  9
% 27.43/3.99  lits                                    130
% 27.43/3.99  lits eq                                 18
% 27.43/3.99  fd_pure                                 0
% 27.43/3.99  fd_pseudo                               0
% 27.43/3.99  fd_cond                                 1
% 27.43/3.99  fd_pseudo_cond                          1
% 27.43/3.99  AC symbols                              0
% 27.43/3.99  
% 27.43/3.99  ------ Schedule dynamic 5 is on 
% 27.43/3.99  
% 27.43/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.43/3.99  
% 27.43/3.99  
% 27.43/3.99  ------ 
% 27.43/3.99  Current options:
% 27.43/3.99  ------ 
% 27.43/3.99  
% 27.43/3.99  ------ Input Options
% 27.43/3.99  
% 27.43/3.99  --out_options                           all
% 27.43/3.99  --tptp_safe_out                         true
% 27.43/3.99  --problem_path                          ""
% 27.43/3.99  --include_path                          ""
% 27.43/3.99  --clausifier                            res/vclausify_rel
% 27.43/3.99  --clausifier_options                    --mode clausify
% 27.43/3.99  --stdin                                 false
% 27.43/3.99  --stats_out                             all
% 27.43/3.99  
% 27.43/3.99  ------ General Options
% 27.43/3.99  
% 27.43/3.99  --fof                                   false
% 27.43/3.99  --time_out_real                         305.
% 27.43/3.99  --time_out_virtual                      -1.
% 27.43/3.99  --symbol_type_check                     false
% 27.43/3.99  --clausify_out                          false
% 27.43/3.99  --sig_cnt_out                           false
% 27.43/3.99  --trig_cnt_out                          false
% 27.43/3.99  --trig_cnt_out_tolerance                1.
% 27.43/3.99  --trig_cnt_out_sk_spl                   false
% 27.43/3.99  --abstr_cl_out                          false
% 27.43/3.99  
% 27.43/3.99  ------ Global Options
% 27.43/3.99  
% 27.43/3.99  --schedule                              default
% 27.43/3.99  --add_important_lit                     false
% 27.43/3.99  --prop_solver_per_cl                    1000
% 27.43/3.99  --min_unsat_core                        false
% 27.43/3.99  --soft_assumptions                      false
% 27.43/3.99  --soft_lemma_size                       3
% 27.43/3.99  --prop_impl_unit_size                   0
% 27.43/3.99  --prop_impl_unit                        []
% 27.43/3.99  --share_sel_clauses                     true
% 27.43/3.99  --reset_solvers                         false
% 27.43/3.99  --bc_imp_inh                            [conj_cone]
% 27.43/3.99  --conj_cone_tolerance                   3.
% 27.43/3.99  --extra_neg_conj                        none
% 27.43/3.99  --large_theory_mode                     true
% 27.43/3.99  --prolific_symb_bound                   200
% 27.43/3.99  --lt_threshold                          2000
% 27.43/3.99  --clause_weak_htbl                      true
% 27.43/3.99  --gc_record_bc_elim                     false
% 27.43/3.99  
% 27.43/3.99  ------ Preprocessing Options
% 27.43/3.99  
% 27.43/3.99  --preprocessing_flag                    true
% 27.43/3.99  --time_out_prep_mult                    0.1
% 27.43/3.99  --splitting_mode                        input
% 27.43/3.99  --splitting_grd                         true
% 27.43/3.99  --splitting_cvd                         false
% 27.43/3.99  --splitting_cvd_svl                     false
% 27.43/3.99  --splitting_nvd                         32
% 27.43/3.99  --sub_typing                            true
% 27.43/3.99  --prep_gs_sim                           true
% 27.43/3.99  --prep_unflatten                        true
% 27.43/3.99  --prep_res_sim                          true
% 27.43/3.99  --prep_upred                            true
% 27.43/3.99  --prep_sem_filter                       exhaustive
% 27.43/3.99  --prep_sem_filter_out                   false
% 27.43/3.99  --pred_elim                             true
% 27.43/3.99  --res_sim_input                         true
% 27.43/3.99  --eq_ax_congr_red                       true
% 27.43/3.99  --pure_diseq_elim                       true
% 27.43/3.99  --brand_transform                       false
% 27.43/3.99  --non_eq_to_eq                          false
% 27.43/3.99  --prep_def_merge                        true
% 27.43/3.99  --prep_def_merge_prop_impl              false
% 27.43/3.99  --prep_def_merge_mbd                    true
% 27.43/3.99  --prep_def_merge_tr_red                 false
% 27.43/3.99  --prep_def_merge_tr_cl                  false
% 27.43/3.99  --smt_preprocessing                     true
% 27.43/3.99  --smt_ac_axioms                         fast
% 27.43/3.99  --preprocessed_out                      false
% 27.43/3.99  --preprocessed_stats                    false
% 27.43/3.99  
% 27.43/3.99  ------ Abstraction refinement Options
% 27.43/3.99  
% 27.43/3.99  --abstr_ref                             []
% 27.43/3.99  --abstr_ref_prep                        false
% 27.43/3.99  --abstr_ref_until_sat                   false
% 27.43/3.99  --abstr_ref_sig_restrict                funpre
% 27.43/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.43/3.99  --abstr_ref_under                       []
% 27.43/3.99  
% 27.43/3.99  ------ SAT Options
% 27.43/3.99  
% 27.43/3.99  --sat_mode                              false
% 27.43/3.99  --sat_fm_restart_options                ""
% 27.43/3.99  --sat_gr_def                            false
% 27.43/3.99  --sat_epr_types                         true
% 27.43/3.99  --sat_non_cyclic_types                  false
% 27.43/3.99  --sat_finite_models                     false
% 27.43/3.99  --sat_fm_lemmas                         false
% 27.43/3.99  --sat_fm_prep                           false
% 27.43/3.99  --sat_fm_uc_incr                        true
% 27.43/3.99  --sat_out_model                         small
% 27.43/3.99  --sat_out_clauses                       false
% 27.43/3.99  
% 27.43/3.99  ------ QBF Options
% 27.43/3.99  
% 27.43/3.99  --qbf_mode                              false
% 27.43/3.99  --qbf_elim_univ                         false
% 27.43/3.99  --qbf_dom_inst                          none
% 27.43/3.99  --qbf_dom_pre_inst                      false
% 27.43/3.99  --qbf_sk_in                             false
% 27.43/3.99  --qbf_pred_elim                         true
% 27.43/3.99  --qbf_split                             512
% 27.43/3.99  
% 27.43/3.99  ------ BMC1 Options
% 27.43/3.99  
% 27.43/3.99  --bmc1_incremental                      false
% 27.43/3.99  --bmc1_axioms                           reachable_all
% 27.43/3.99  --bmc1_min_bound                        0
% 27.43/3.99  --bmc1_max_bound                        -1
% 27.43/3.99  --bmc1_max_bound_default                -1
% 27.43/3.99  --bmc1_symbol_reachability              true
% 27.43/3.99  --bmc1_property_lemmas                  false
% 27.43/3.99  --bmc1_k_induction                      false
% 27.43/3.99  --bmc1_non_equiv_states                 false
% 27.43/3.99  --bmc1_deadlock                         false
% 27.43/3.99  --bmc1_ucm                              false
% 27.43/3.99  --bmc1_add_unsat_core                   none
% 27.43/3.99  --bmc1_unsat_core_children              false
% 27.43/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.43/3.99  --bmc1_out_stat                         full
% 27.43/3.99  --bmc1_ground_init                      false
% 27.43/3.99  --bmc1_pre_inst_next_state              false
% 27.43/3.99  --bmc1_pre_inst_state                   false
% 27.43/3.99  --bmc1_pre_inst_reach_state             false
% 27.43/3.99  --bmc1_out_unsat_core                   false
% 27.43/3.99  --bmc1_aig_witness_out                  false
% 27.43/3.99  --bmc1_verbose                          false
% 27.43/3.99  --bmc1_dump_clauses_tptp                false
% 27.43/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.43/3.99  --bmc1_dump_file                        -
% 27.43/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.43/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.43/3.99  --bmc1_ucm_extend_mode                  1
% 27.43/3.99  --bmc1_ucm_init_mode                    2
% 27.43/3.99  --bmc1_ucm_cone_mode                    none
% 27.43/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.43/3.99  --bmc1_ucm_relax_model                  4
% 27.43/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.43/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.43/3.99  --bmc1_ucm_layered_model                none
% 27.43/3.99  --bmc1_ucm_max_lemma_size               10
% 27.43/3.99  
% 27.43/3.99  ------ AIG Options
% 27.43/3.99  
% 27.43/3.99  --aig_mode                              false
% 27.43/3.99  
% 27.43/3.99  ------ Instantiation Options
% 27.43/3.99  
% 27.43/3.99  --instantiation_flag                    true
% 27.43/3.99  --inst_sos_flag                         false
% 27.43/3.99  --inst_sos_phase                        true
% 27.43/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.43/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.43/3.99  --inst_lit_sel_side                     none
% 27.43/3.99  --inst_solver_per_active                1400
% 27.43/3.99  --inst_solver_calls_frac                1.
% 27.43/3.99  --inst_passive_queue_type               priority_queues
% 27.43/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.43/3.99  --inst_passive_queues_freq              [25;2]
% 27.43/3.99  --inst_dismatching                      true
% 27.43/3.99  --inst_eager_unprocessed_to_passive     true
% 27.43/3.99  --inst_prop_sim_given                   true
% 27.43/3.99  --inst_prop_sim_new                     false
% 27.43/3.99  --inst_subs_new                         false
% 27.43/3.99  --inst_eq_res_simp                      false
% 27.43/3.99  --inst_subs_given                       false
% 27.43/3.99  --inst_orphan_elimination               true
% 27.43/3.99  --inst_learning_loop_flag               true
% 27.43/3.99  --inst_learning_start                   3000
% 27.43/3.99  --inst_learning_factor                  2
% 27.43/3.99  --inst_start_prop_sim_after_learn       3
% 27.43/3.99  --inst_sel_renew                        solver
% 27.43/3.99  --inst_lit_activity_flag                true
% 27.43/3.99  --inst_restr_to_given                   false
% 27.43/3.99  --inst_activity_threshold               500
% 27.43/3.99  --inst_out_proof                        true
% 27.43/3.99  
% 27.43/3.99  ------ Resolution Options
% 27.43/3.99  
% 27.43/3.99  --resolution_flag                       false
% 27.43/3.99  --res_lit_sel                           adaptive
% 27.43/3.99  --res_lit_sel_side                      none
% 27.43/3.99  --res_ordering                          kbo
% 27.43/3.99  --res_to_prop_solver                    active
% 27.43/3.99  --res_prop_simpl_new                    false
% 27.43/3.99  --res_prop_simpl_given                  true
% 27.43/3.99  --res_passive_queue_type                priority_queues
% 27.43/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.43/3.99  --res_passive_queues_freq               [15;5]
% 27.43/3.99  --res_forward_subs                      full
% 27.43/3.99  --res_backward_subs                     full
% 27.43/3.99  --res_forward_subs_resolution           true
% 27.43/3.99  --res_backward_subs_resolution          true
% 27.43/3.99  --res_orphan_elimination                true
% 27.43/3.99  --res_time_limit                        2.
% 27.43/3.99  --res_out_proof                         true
% 27.43/3.99  
% 27.43/3.99  ------ Superposition Options
% 27.43/3.99  
% 27.43/3.99  --superposition_flag                    true
% 27.43/3.99  --sup_passive_queue_type                priority_queues
% 27.43/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.43/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.43/3.99  --demod_completeness_check              fast
% 27.43/3.99  --demod_use_ground                      true
% 27.43/3.99  --sup_to_prop_solver                    passive
% 27.43/3.99  --sup_prop_simpl_new                    true
% 27.43/3.99  --sup_prop_simpl_given                  true
% 27.43/3.99  --sup_fun_splitting                     false
% 27.43/3.99  --sup_smt_interval                      50000
% 27.43/3.99  
% 27.43/3.99  ------ Superposition Simplification Setup
% 27.43/3.99  
% 27.43/3.99  --sup_indices_passive                   []
% 27.43/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.43/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.43/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.43/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.43/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.43/3.99  --sup_full_bw                           [BwDemod]
% 27.43/3.99  --sup_immed_triv                        [TrivRules]
% 27.43/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.43/3.99  --sup_immed_bw_main                     []
% 27.43/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.43/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.43/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.43/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.43/3.99  
% 27.43/3.99  ------ Combination Options
% 27.43/3.99  
% 27.43/3.99  --comb_res_mult                         3
% 27.43/3.99  --comb_sup_mult                         2
% 27.43/3.99  --comb_inst_mult                        10
% 27.43/3.99  
% 27.43/3.99  ------ Debug Options
% 27.43/3.99  
% 27.43/3.99  --dbg_backtrace                         false
% 27.43/3.99  --dbg_dump_prop_clauses                 false
% 27.43/3.99  --dbg_dump_prop_clauses_file            -
% 27.43/3.99  --dbg_out_stat                          false
% 27.43/3.99  
% 27.43/3.99  
% 27.43/3.99  
% 27.43/3.99  
% 27.43/3.99  ------ Proving...
% 27.43/3.99  
% 27.43/3.99  
% 27.43/3.99  % SZS status Theorem for theBenchmark.p
% 27.43/3.99  
% 27.43/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.43/3.99  
% 27.43/3.99  fof(f13,axiom,(
% 27.43/3.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f84,plain,(
% 27.43/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f13])).
% 27.43/3.99  
% 27.43/3.99  fof(f5,axiom,(
% 27.43/3.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f76,plain,(
% 27.43/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f5])).
% 27.43/3.99  
% 27.43/3.99  fof(f127,plain,(
% 27.43/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.43/3.99    inference(definition_unfolding,[],[f84,f76])).
% 27.43/3.99  
% 27.43/3.99  fof(f6,axiom,(
% 27.43/3.99    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f77,plain,(
% 27.43/3.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f6])).
% 27.43/3.99  
% 27.43/3.99  fof(f1,axiom,(
% 27.43/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f47,plain,(
% 27.43/3.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 27.43/3.99    inference(nnf_transformation,[],[f1])).
% 27.43/3.99  
% 27.43/3.99  fof(f72,plain,(
% 27.43/3.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.43/3.99    inference(cnf_transformation,[],[f47])).
% 27.43/3.99  
% 27.43/3.99  fof(f124,plain,(
% 27.43/3.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.43/3.99    inference(definition_unfolding,[],[f72,f76])).
% 27.43/3.99  
% 27.43/3.99  fof(f21,axiom,(
% 27.43/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f39,plain,(
% 27.43/3.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.43/3.99    inference(ennf_transformation,[],[f21])).
% 27.43/3.99  
% 27.43/3.99  fof(f40,plain,(
% 27.43/3.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f39])).
% 27.43/3.99  
% 27.43/3.99  fof(f112,plain,(
% 27.43/3.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f40])).
% 27.43/3.99  
% 27.43/3.99  fof(f23,conjecture,(
% 27.43/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f24,negated_conjecture,(
% 27.43/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 27.43/3.99    inference(negated_conjecture,[],[f23])).
% 27.43/3.99  
% 27.43/3.99  fof(f42,plain,(
% 27.43/3.99    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 27.43/3.99    inference(ennf_transformation,[],[f24])).
% 27.43/3.99  
% 27.43/3.99  fof(f43,plain,(
% 27.43/3.99    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f42])).
% 27.43/3.99  
% 27.43/3.99  fof(f64,plain,(
% 27.43/3.99    ? [X0] : (? [X1] : (((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.43/3.99    inference(nnf_transformation,[],[f43])).
% 27.43/3.99  
% 27.43/3.99  fof(f65,plain,(
% 27.43/3.99    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f64])).
% 27.43/3.99  
% 27.43/3.99  fof(f66,plain,(
% 27.43/3.99    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.43/3.99    inference(rectify,[],[f65])).
% 27.43/3.99  
% 27.43/3.99  fof(f69,plain,(
% 27.43/3.99    ( ! [X0,X1] : (? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK8) & v3_pre_topc(sK8,X0) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f68,plain,(
% 27.43/3.99    ( ! [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (r1_xboole_0(sK7,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(sK7,X0)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f67,plain,(
% 27.43/3.99    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK6) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(X1,sK6)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f70,plain,(
% 27.43/3.99    (((r1_xboole_0(sK7,sK8) & v3_pre_topc(sK8,sK6) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(sK7,sK6)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 27.43/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f66,f69,f68,f67])).
% 27.43/3.99  
% 27.43/3.99  fof(f115,plain,(
% 27.43/3.99    v2_pre_topc(sK6)),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f116,plain,(
% 27.43/3.99    l1_pre_topc(sK6)),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f17,axiom,(
% 27.43/3.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f33,plain,(
% 27.43/3.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f17])).
% 27.43/3.99  
% 27.43/3.99  fof(f101,plain,(
% 27.43/3.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f33])).
% 27.43/3.99  
% 27.43/3.99  fof(f16,axiom,(
% 27.43/3.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f32,plain,(
% 27.43/3.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f16])).
% 27.43/3.99  
% 27.43/3.99  fof(f100,plain,(
% 27.43/3.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f32])).
% 27.43/3.99  
% 27.43/3.99  fof(f44,plain,(
% 27.43/3.99    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0))))),
% 27.43/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.43/3.99  
% 27.43/3.99  fof(f50,plain,(
% 27.43/3.99    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2))) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 27.43/3.99    inference(nnf_transformation,[],[f44])).
% 27.43/3.99  
% 27.43/3.99  fof(f51,plain,(
% 27.43/3.99    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 27.43/3.99    inference(flattening,[],[f50])).
% 27.43/3.99  
% 27.43/3.99  fof(f52,plain,(
% 27.43/3.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 27.43/3.99    inference(rectify,[],[f51])).
% 27.43/3.99  
% 27.43/3.99  fof(f55,plain,(
% 27.43/3.99    ! [X6,X1,X0] : (? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))))),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f54,plain,(
% 27.43/3.99    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(X3,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f53,plain,(
% 27.43/3.99    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1))) => ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(sK2(X0,X1,X2),X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f56,plain,(
% 27.43/3.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 27.43/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f52,f55,f54,f53])).
% 27.43/3.99  
% 27.43/3.99  fof(f93,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f94,plain,(
% 27.43/3.99    ( ! [X2,X0,X5,X1] : (sP0(X0,X1,X2) | ~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f9,axiom,(
% 27.43/3.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f80,plain,(
% 27.43/3.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f9])).
% 27.43/3.99  
% 27.43/3.99  fof(f7,axiom,(
% 27.43/3.99    ! [X0] : k2_subset_1(X0) = X0),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f78,plain,(
% 27.43/3.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 27.43/3.99    inference(cnf_transformation,[],[f7])).
% 27.43/3.99  
% 27.43/3.99  fof(f98,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_xboole_0(X0,sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f95,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f118,plain,(
% 27.43/3.99    ( ! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | v1_tops_1(sK7,sK6)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f96,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f117,plain,(
% 27.43/3.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f20,axiom,(
% 27.43/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f38,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f20])).
% 27.43/3.99  
% 27.43/3.99  fof(f62,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(nnf_transformation,[],[f38])).
% 27.43/3.99  
% 27.43/3.99  fof(f111,plain,(
% 27.43/3.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f62])).
% 27.43/3.99  
% 27.43/3.99  fof(f45,plain,(
% 27.43/3.99    ! [X2,X0,X1] : ((k2_pre_topc(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 27.43/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 27.43/3.99  
% 27.43/3.99  fof(f48,plain,(
% 27.43/3.99    ! [X2,X0,X1] : (((k2_pre_topc(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_pre_topc(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 27.43/3.99    inference(nnf_transformation,[],[f45])).
% 27.43/3.99  
% 27.43/3.99  fof(f49,plain,(
% 27.43/3.99    ! [X0,X1,X2] : (((k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 27.43/3.99    inference(rectify,[],[f48])).
% 27.43/3.99  
% 27.43/3.99  fof(f87,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f49])).
% 27.43/3.99  
% 27.43/3.99  fof(f15,axiom,(
% 27.43/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f30,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f15])).
% 27.43/3.99  
% 27.43/3.99  fof(f31,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f30])).
% 27.43/3.99  
% 27.43/3.99  fof(f46,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(definition_folding,[],[f31,f45,f44])).
% 27.43/3.99  
% 27.43/3.99  fof(f99,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f46])).
% 27.43/3.99  
% 27.43/3.99  fof(f110,plain,(
% 27.43/3.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f62])).
% 27.43/3.99  
% 27.43/3.99  fof(f97,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f86,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f49])).
% 27.43/3.99  
% 27.43/3.99  fof(f128,plain,(
% 27.43/3.99    ( ! [X2,X1] : (sP0(X2,X1,k2_pre_topc(X1,X2)) | ~sP1(k2_pre_topc(X1,X2),X1,X2)) )),
% 27.43/3.99    inference(equality_resolution,[],[f86])).
% 27.43/3.99  
% 27.43/3.99  fof(f12,axiom,(
% 27.43/3.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f83,plain,(
% 27.43/3.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f12])).
% 27.43/3.99  
% 27.43/3.99  fof(f8,axiom,(
% 27.43/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f25,plain,(
% 27.43/3.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.43/3.99    inference(ennf_transformation,[],[f8])).
% 27.43/3.99  
% 27.43/3.99  fof(f79,plain,(
% 27.43/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f25])).
% 27.43/3.99  
% 27.43/3.99  fof(f4,axiom,(
% 27.43/3.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f75,plain,(
% 27.43/3.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.43/3.99    inference(cnf_transformation,[],[f4])).
% 27.43/3.99  
% 27.43/3.99  fof(f22,axiom,(
% 27.43/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f41,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f22])).
% 27.43/3.99  
% 27.43/3.99  fof(f63,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(nnf_transformation,[],[f41])).
% 27.43/3.99  
% 27.43/3.99  fof(f114,plain,(
% 27.43/3.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f63])).
% 27.43/3.99  
% 27.43/3.99  fof(f18,axiom,(
% 27.43/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f34,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f18])).
% 27.43/3.99  
% 27.43/3.99  fof(f35,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f34])).
% 27.43/3.99  
% 27.43/3.99  fof(f102,plain,(
% 27.43/3.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f35])).
% 27.43/3.99  
% 27.43/3.99  fof(f19,axiom,(
% 27.43/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f36,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(ennf_transformation,[],[f19])).
% 27.43/3.99  
% 27.43/3.99  fof(f37,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f36])).
% 27.43/3.99  
% 27.43/3.99  fof(f57,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(nnf_transformation,[],[f37])).
% 27.43/3.99  
% 27.43/3.99  fof(f58,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(flattening,[],[f57])).
% 27.43/3.99  
% 27.43/3.99  fof(f59,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(rectify,[],[f58])).
% 27.43/3.99  
% 27.43/3.99  fof(f60,plain,(
% 27.43/3.99    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.43/3.99    introduced(choice_axiom,[])).
% 27.43/3.99  
% 27.43/3.99  fof(f61,plain,(
% 27.43/3.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.43/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f59,f60])).
% 27.43/3.99  
% 27.43/3.99  fof(f105,plain,(
% 27.43/3.99    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f61])).
% 27.43/3.99  
% 27.43/3.99  fof(f14,axiom,(
% 27.43/3.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f28,plain,(
% 27.43/3.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 27.43/3.99    inference(ennf_transformation,[],[f14])).
% 27.43/3.99  
% 27.43/3.99  fof(f29,plain,(
% 27.43/3.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.43/3.99    inference(flattening,[],[f28])).
% 27.43/3.99  
% 27.43/3.99  fof(f85,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f29])).
% 27.43/3.99  
% 27.43/3.99  fof(f11,axiom,(
% 27.43/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 27.43/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/3.99  
% 27.43/3.99  fof(f27,plain,(
% 27.43/3.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.43/3.99    inference(ennf_transformation,[],[f11])).
% 27.43/3.99  
% 27.43/3.99  fof(f82,plain,(
% 27.43/3.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.43/3.99    inference(cnf_transformation,[],[f27])).
% 27.43/3.99  
% 27.43/3.99  fof(f119,plain,(
% 27.43/3.99    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_tops_1(sK7,sK6)),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f88,plain,(
% 27.43/3.99    ( ! [X6,X2,X0,X8,X1] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X2) | ~r2_hidden(X6,u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 27.43/3.99    inference(cnf_transformation,[],[f56])).
% 27.43/3.99  
% 27.43/3.99  fof(f121,plain,(
% 27.43/3.99    v3_pre_topc(sK8,sK6) | ~v1_tops_1(sK7,sK6)),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f122,plain,(
% 27.43/3.99    r1_xboole_0(sK7,sK8) | ~v1_tops_1(sK7,sK6)),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  fof(f120,plain,(
% 27.43/3.99    k1_xboole_0 != sK8 | ~v1_tops_1(sK7,sK6)),
% 27.43/3.99    inference(cnf_transformation,[],[f70])).
% 27.43/3.99  
% 27.43/3.99  cnf(c_12,plain,
% 27.43/3.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f127]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_5,plain,
% 27.43/3.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9066,plain,
% 27.43/3.99      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_12,c_5]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1,plain,
% 27.43/3.99      ( r1_xboole_0(X0,X1)
% 27.43/3.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f124]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8528,plain,
% 27.43/3.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 27.43/3.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8576,plain,
% 27.43/3.99      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 27.43/3.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 27.43/3.99      inference(light_normalisation,[status(thm)],[c_8528,c_12]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_10692,plain,
% 27.43/3.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_9066,c_8576]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_40,plain,
% 27.43/3.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 27.43/3.99      | ~ v2_pre_topc(X0)
% 27.43/3.99      | ~ l1_pre_topc(X0) ),
% 27.43/3.99      inference(cnf_transformation,[],[f112]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_50,negated_conjecture,
% 27.43/3.99      ( v2_pre_topc(sK6) ),
% 27.43/3.99      inference(cnf_transformation,[],[f115]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_637,plain,
% 27.43/3.99      ( v3_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK6 != X0 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_40,c_50]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_638,plain,
% 27.43/3.99      ( v3_pre_topc(k2_struct_0(sK6),sK6) | ~ l1_pre_topc(sK6) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_637]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_49,negated_conjecture,
% 27.43/3.99      ( l1_pre_topc(sK6) ),
% 27.43/3.99      inference(cnf_transformation,[],[f116]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_68,plain,
% 27.43/3.99      ( v3_pre_topc(k2_struct_0(sK6),sK6)
% 27.43/3.99      | ~ v2_pre_topc(sK6)
% 27.43/3.99      | ~ l1_pre_topc(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_40]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_640,plain,
% 27.43/3.99      ( v3_pre_topc(k2_struct_0(sK6),sK6) ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_638,c_50,c_49,c_68]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8503,plain,
% 27.43/3.99      ( v3_pre_topc(k2_struct_0(sK6),sK6) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_29,plain,
% 27.43/3.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 27.43/3.99      inference(cnf_transformation,[],[f101]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_28,plain,
% 27.43/3.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 27.43/3.99      inference(cnf_transformation,[],[f100]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_623,plain,
% 27.43/3.99      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 27.43/3.99      inference(resolution,[status(thm)],[c_29,c_28]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_928,plain,
% 27.43/3.99      ( k2_struct_0(X0) = u1_struct_0(X0) | sK6 != X0 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_623,c_49]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_929,plain,
% 27.43/3.99      ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_928]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8537,plain,
% 27.43/3.99      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 27.43/3.99      inference(light_normalisation,[status(thm)],[c_8503,c_929]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_21,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f93]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8515,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_20,plain,
% 27.43/3.99      ( sP0(X0,X1,X2)
% 27.43/3.99      | ~ v3_pre_topc(X3,X1)
% 27.43/3.99      | ~ r2_hidden(sK2(X0,X1,X2),X3)
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2)
% 27.43/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ r1_xboole_0(X0,X3) ),
% 27.43/3.99      inference(cnf_transformation,[],[f94]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8516,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | v3_pre_topc(X3,X1) != iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 27.43/3.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,X3) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_14393,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 27.43/3.99      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8515,c_8516]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8,plain,
% 27.43/3.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8525,plain,
% 27.43/3.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_6,plain,
% 27.43/3.99      ( k2_subset_1(X0) = X0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f78]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8544,plain,
% 27.43/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.43/3.99      inference(light_normalisation,[status(thm)],[c_8525,c_6]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_26090,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 27.43/3.99      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 27.43/3.99      inference(forward_subsumption_resolution,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_14393,c_8544]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_26094,plain,
% 27.43/3.99      ( sP0(X0,sK6,X1) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
% 27.43/3.99      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8537,c_26090]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_16,plain,
% 27.43/3.99      ( sP0(X0,X1,X2)
% 27.43/3.99      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 27.43/3.99      | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f98]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8520,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_13306,plain,
% 27.43/3.99      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 27.43/3.99      | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8515,c_8520]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_19,plain,
% 27.43/3.99      ( sP0(X0,X1,X2)
% 27.43/3.99      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 27.43/3.99      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
% 27.43/3.99      inference(cnf_transformation,[],[f95]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8517,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 27.43/3.99      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_13400,plain,
% 27.43/3.99      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 27.43/3.99      | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8515,c_8517]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_47,negated_conjecture,
% 27.43/3.99      ( v1_tops_1(sK7,sK6)
% 27.43/3.99      | ~ v3_pre_topc(X0,sK6)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ r1_xboole_0(sK7,X0)
% 27.43/3.99      | k1_xboole_0 = X0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f118]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8505,plain,
% 27.43/3.99      ( k1_xboole_0 = X0
% 27.43/3.99      | v1_tops_1(sK7,sK6) = iProver_top
% 27.43/3.99      | v3_pre_topc(X0,sK6) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | r1_xboole_0(sK7,X0) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_18824,plain,
% 27.43/3.99      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 27.43/3.99      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 27.43/3.99      | v1_tops_1(sK7,sK6) = iProver_top
% 27.43/3.99      | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
% 27.43/3.99      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_13400,c_8505]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_18,plain,
% 27.43/3.99      ( sP0(X0,X1,X2)
% 27.43/3.99      | v3_pre_topc(sK3(X0,X1,X2),X1)
% 27.43/3.99      | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
% 27.43/3.99      inference(cnf_transformation,[],[f96]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8518,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_12748,plain,
% 27.43/3.99      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 27.43/3.99      | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8515,c_8518]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_19573,plain,
% 27.43/3.99      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 27.43/3.99      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 27.43/3.99      | v1_tops_1(sK7,sK6) = iProver_top
% 27.43/3.99      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(forward_subsumption_resolution,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_18824,c_12748]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_19577,plain,
% 27.43/3.99      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 27.43/3.99      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 27.43/3.99      | v1_tops_1(sK7,sK6) = iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_13306,c_19573]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_48,negated_conjecture,
% 27.43/3.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(cnf_transformation,[],[f117]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_53,plain,
% 27.43/3.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_101,plain,
% 27.43/3.99      ( l1_struct_0(sK6) | ~ l1_pre_topc(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_29]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_104,plain,
% 27.43/3.99      ( ~ l1_struct_0(sK6) | k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_28]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_38,plain,
% 27.43/3.99      ( v1_tops_1(X0,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ l1_pre_topc(X1)
% 27.43/3.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 27.43/3.99      inference(cnf_transformation,[],[f111]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_969,plain,
% 27.43/3.99      ( v1_tops_1(X0,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 27.43/3.99      | sK6 != X1 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_38,c_49]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_970,plain,
% 27.43/3.99      ( v1_tops_1(X0,sK6)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | k2_pre_topc(sK6,X0) != k2_struct_0(sK6) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_969]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8897,plain,
% 27.43/3.99      ( v1_tops_1(sK7,sK6)
% 27.43/3.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_970]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8898,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 27.43/3.99      | v1_tops_1(sK7,sK6) = iProver_top
% 27.43/3.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_8897]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7580,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9037,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) != X0
% 27.43/3.99      | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 27.43/3.99      | k2_struct_0(sK6) != X0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7580]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9264,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 27.43/3.99      | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
% 27.43/3.99      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9037]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8504,plain,
% 27.43/3.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_14,plain,
% 27.43/3.99      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | k2_pre_topc(X1,X2) = X0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f87]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_27,plain,
% 27.43/3.99      ( sP1(X0,X1,X2)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ l1_pre_topc(X1) ),
% 27.43/3.99      inference(cnf_transformation,[],[f99]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1094,plain,
% 27.43/3.99      ( sP1(X0,X1,X2)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | sK6 != X1 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_27,c_49]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1095,plain,
% 27.43/3.99      ( sP1(X0,sK6,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_1094]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1162,plain,
% 27.43/3.99      ( ~ sP0(X0,X1,X2)
% 27.43/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | X3 != X2
% 27.43/3.99      | X4 != X0
% 27.43/3.99      | k2_pre_topc(X1,X0) = X2
% 27.43/3.99      | sK6 != X1 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_14,c_1095]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1163,plain,
% 27.43/3.99      ( ~ sP0(X0,sK6,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | k2_pre_topc(sK6,X0) = X1 ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_1162]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8492,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,X0) = X1
% 27.43/3.99      | sP0(X0,sK6,X1) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9435,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) = X0
% 27.43/3.99      | sP0(sK7,sK6,X0) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8504,c_8492]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9770,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 27.43/3.99      | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8544,c_9435]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_82123,plain,
% 27.43/3.99      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 27.43/3.99      | v1_tops_1(sK7,sK6) = iProver_top ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_19577,c_49,c_53,c_101,c_104,c_8898,c_9264,c_9770]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_39,plain,
% 27.43/3.99      ( ~ v1_tops_1(X0,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ l1_pre_topc(X1)
% 27.43/3.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 27.43/3.99      inference(cnf_transformation,[],[f110]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_954,plain,
% 27.43/3.99      ( ~ v1_tops_1(X0,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 27.43/3.99      | sK6 != X1 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_39,c_49]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_955,plain,
% 27.43/3.99      ( ~ v1_tops_1(X0,sK6)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | k2_pre_topc(sK6,X0) = k2_struct_0(sK6) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_954]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8499,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,X0) = k2_struct_0(sK6)
% 27.43/3.99      | v1_tops_1(X0,sK6) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_955]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8612,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,X0) = u1_struct_0(sK6)
% 27.43/3.99      | v1_tops_1(X0,sK6) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(light_normalisation,[status(thm)],[c_8499,c_929]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9163,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 27.43/3.99      | v1_tops_1(sK7,sK6) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8504,c_8612]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_82155,plain,
% 27.43/3.99      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 27.43/3.99      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_82123,c_9163]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_17,plain,
% 27.43/3.99      ( sP0(X0,X1,X2)
% 27.43/3.99      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f97]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8519,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 27.43/3.99      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_82450,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 27.43/3.99      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 27.43/3.99      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_82155,c_8519]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7592,plain,
% 27.43/3.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 27.43/3.99      theory(equality) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7608,plain,
% 27.43/3.99      ( u1_struct_0(sK6) = u1_struct_0(sK6) | sK6 != sK6 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7592]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7579,plain,( X0 = X0 ),theory(equality) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7614,plain,
% 27.43/3.99      ( sK6 = sK6 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7579]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_15,plain,
% 27.43/3.99      ( ~ sP1(k2_pre_topc(X0,X1),X0,X1) | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f128]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1180,plain,
% 27.43/3.99      ( sP0(X0,X1,k2_pre_topc(X1,X0))
% 27.43/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | X3 != X0
% 27.43/3.99      | k2_pre_topc(X1,X0) != X2
% 27.43/3.99      | sK6 != X1 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_15,c_1095]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1181,plain,
% 27.43/3.99      ( sP0(X0,sK6,k2_pre_topc(sK6,X0))
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(k2_pre_topc(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_1180]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8909,plain,
% 27.43/3.99      ( sP0(sK7,sK6,k2_pre_topc(sK6,sK7))
% 27.43/3.99      | ~ m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_1181]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8910,plain,
% 27.43/3.99      ( sP0(sK7,sK6,k2_pre_topc(sK6,sK7)) = iProver_top
% 27.43/3.99      | m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_8909]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8948,plain,
% 27.43/3.99      ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_8]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8954,plain,
% 27.43/3.99      ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_8948]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9288,plain,
% 27.43/3.99      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7579]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9943,plain,
% 27.43/3.99      ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_6]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9214,plain,
% 27.43/3.99      ( X0 != X1 | X0 = k2_struct_0(sK6) | k2_struct_0(sK6) != X1 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7580]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9602,plain,
% 27.43/3.99      ( X0 = k2_struct_0(sK6)
% 27.43/3.99      | X0 != u1_struct_0(sK6)
% 27.43/3.99      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9214]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9952,plain,
% 27.43/3.99      ( k2_struct_0(sK6) != u1_struct_0(sK6)
% 27.43/3.99      | u1_struct_0(sK6) = k2_struct_0(sK6)
% 27.43/3.99      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9602]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9118,plain,
% 27.43/3.99      ( sP0(sK7,sK6,X0) | r2_hidden(sK2(sK7,sK6,X0),u1_struct_0(sK6)) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_21]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_17381,plain,
% 27.43/3.99      ( sP0(sK7,sK6,u1_struct_0(sK6))
% 27.43/3.99      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9118]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_17384,plain,
% 27.43/3.99      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_17381]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7586,plain,
% 27.43/3.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.43/3.99      theory(equality) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9007,plain,
% 27.43/3.99      ( m1_subset_1(X0,X1)
% 27.43/3.99      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 27.43/3.99      | X1 != k1_zfmisc_1(X2)
% 27.43/3.99      | X0 != k2_subset_1(X2) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7586]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9704,plain,
% 27.43/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.43/3.99      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 27.43/3.99      | X0 != k2_subset_1(X1)
% 27.43/3.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9007]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11110,plain,
% 27.43/3.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | X0 != k2_subset_1(u1_struct_0(sK6))
% 27.43/3.99      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9704]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_28637,plain,
% 27.43/3.99      ( m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | k2_pre_topc(sK6,sK7) != k2_subset_1(u1_struct_0(sK6))
% 27.43/3.99      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_11110]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_28638,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) != k2_subset_1(u1_struct_0(sK6))
% 27.43/3.99      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 27.43/3.99      | m1_subset_1(k2_pre_topc(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 27.43/3.99      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_28637]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9266,plain,
% 27.43/3.99      ( X0 != X1 | k2_struct_0(sK6) != X1 | k2_struct_0(sK6) = X0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7580]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_10442,plain,
% 27.43/3.99      ( X0 != u1_struct_0(sK6)
% 27.43/3.99      | k2_struct_0(sK6) = X0
% 27.43/3.99      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9266]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_32641,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
% 27.43/3.99      | k2_struct_0(sK6) = k2_pre_topc(sK6,sK7)
% 27.43/3.99      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_10442]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11295,plain,
% 27.43/3.99      ( X0 != X1 | X0 = k2_subset_1(X2) | k2_subset_1(X2) != X1 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7580]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_14052,plain,
% 27.43/3.99      ( X0 != X1
% 27.43/3.99      | X0 = k2_subset_1(u1_struct_0(sK6))
% 27.43/3.99      | k2_subset_1(u1_struct_0(sK6)) != X1 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_11295]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_19649,plain,
% 27.43/3.99      ( X0 != u1_struct_0(sK6)
% 27.43/3.99      | X0 = k2_subset_1(u1_struct_0(sK6))
% 27.43/3.99      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_14052]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_39951,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
% 27.43/3.99      | k2_pre_topc(sK6,sK7) = k2_subset_1(u1_struct_0(sK6))
% 27.43/3.99      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_19649]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7590,plain,
% 27.43/3.99      ( ~ sP0(X0,X1,X2) | sP0(X0,X3,X4) | X3 != X1 | X4 != X2 ),
% 27.43/3.99      theory(equality) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9141,plain,
% 27.43/3.99      ( ~ sP0(sK7,X0,X1) | sP0(sK7,sK6,X2) | X2 != X1 | sK6 != X0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7590]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9456,plain,
% 27.43/3.99      ( ~ sP0(sK7,X0,X1)
% 27.43/3.99      | sP0(sK7,sK6,k2_struct_0(sK6))
% 27.43/3.99      | k2_struct_0(sK6) != X1
% 27.43/3.99      | sK6 != X0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9141]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_57935,plain,
% 27.43/3.99      ( ~ sP0(sK7,X0,k2_pre_topc(sK6,sK7))
% 27.43/3.99      | sP0(sK7,sK6,k2_struct_0(sK6))
% 27.43/3.99      | k2_struct_0(sK6) != k2_pre_topc(sK6,sK7)
% 27.43/3.99      | sK6 != X0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9456]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_57940,plain,
% 27.43/3.99      ( k2_struct_0(sK6) != k2_pre_topc(sK6,sK7)
% 27.43/3.99      | sK6 != X0
% 27.43/3.99      | sP0(sK7,X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 27.43/3.99      | sP0(sK7,sK6,k2_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_57935]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_57942,plain,
% 27.43/3.99      ( k2_struct_0(sK6) != k2_pre_topc(sK6,sK7)
% 27.43/3.99      | sK6 != sK6
% 27.43/3.99      | sP0(sK7,sK6,k2_pre_topc(sK6,sK7)) != iProver_top
% 27.43/3.99      | sP0(sK7,sK6,k2_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_57940]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_28299,plain,
% 27.43/3.99      ( sP0(sK7,sK6,X0)
% 27.43/3.99      | ~ sP0(sK7,sK6,k2_struct_0(sK6))
% 27.43/3.99      | X0 != k2_struct_0(sK6)
% 27.43/3.99      | sK6 != sK6 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9141]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_59169,plain,
% 27.43/3.99      ( ~ sP0(sK7,sK6,k2_struct_0(sK6))
% 27.43/3.99      | sP0(sK7,sK6,u1_struct_0(sK6))
% 27.43/3.99      | u1_struct_0(sK6) != k2_struct_0(sK6)
% 27.43/3.99      | sK6 != sK6 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_28299]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_59170,plain,
% 27.43/3.99      ( u1_struct_0(sK6) != k2_struct_0(sK6)
% 27.43/3.99      | sK6 != sK6
% 27.43/3.99      | sP0(sK7,sK6,k2_struct_0(sK6)) != iProver_top
% 27.43/3.99      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_59169]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_103012,plain,
% 27.43/3.99      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 27.43/3.99      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_82450,c_49,c_53,c_101,c_104,c_7608,c_7614,c_8910,
% 27.43/3.99                 c_8954,c_9288,c_9943,c_9952,c_17384,c_28638,c_32641,
% 27.43/3.99                 c_39951,c_57942,c_59170]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11,plain,
% 27.43/3.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f83]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8522,plain,
% 27.43/3.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7,plain,
% 27.43/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.43/3.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 27.43/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8526,plain,
% 27.43/3.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 27.43/3.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11794,plain,
% 27.43/3.99      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8522,c_8526]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_4,plain,
% 27.43/3.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11819,plain,
% 27.43/3.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 27.43/3.99      inference(light_normalisation,[status(thm)],[c_11794,c_4]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_41,plain,
% 27.43/3.99      ( v4_pre_topc(X0,X1)
% 27.43/3.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ l1_pre_topc(X1) ),
% 27.43/3.99      inference(cnf_transformation,[],[f114]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_31,plain,
% 27.43/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ l1_pre_topc(X1)
% 27.43/3.99      | k2_pre_topc(X1,X0) = X0 ),
% 27.43/3.99      inference(cnf_transformation,[],[f102]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_723,plain,
% 27.43/3.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 27.43/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.43/3.99      | ~ l1_pre_topc(X0)
% 27.43/3.99      | k2_pre_topc(X0,X1) = X1 ),
% 27.43/3.99      inference(resolution,[status(thm)],[c_41,c_31]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_913,plain,
% 27.43/3.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 27.43/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.43/3.99      | k2_pre_topc(X0,X1) = X1
% 27.43/3.99      | sK6 != X0 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_723,c_49]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_914,plain,
% 27.43/3.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6)
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | k2_pre_topc(sK6,X0) = X0 ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_913]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8501,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,X0) = X0
% 27.43/3.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11902,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 27.43/3.99      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 27.43/3.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_11819,c_8501]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8928,plain,
% 27.43/3.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_11]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8934,plain,
% 27.43/3.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_8928]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_12232,plain,
% 27.43/3.99      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_11902,c_8537,c_8934]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_36,plain,
% 27.43/3.99      ( ~ v3_pre_topc(X0,X1)
% 27.43/3.99      | ~ r2_hidden(X2,X0)
% 27.43/3.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 27.43/3.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.43/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ r1_xboole_0(X3,X0)
% 27.43/3.99      | ~ l1_pre_topc(X1) ),
% 27.43/3.99      inference(cnf_transformation,[],[f105]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1002,plain,
% 27.43/3.99      ( ~ v3_pre_topc(X0,X1)
% 27.43/3.99      | ~ r2_hidden(X2,X0)
% 27.43/3.99      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 27.43/3.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.43/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ r1_xboole_0(X3,X0)
% 27.43/3.99      | sK6 != X1 ),
% 27.43/3.99      inference(resolution_lifted,[status(thm)],[c_36,c_49]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1003,plain,
% 27.43/3.99      ( ~ v3_pre_topc(X0,sK6)
% 27.43/3.99      | ~ r2_hidden(X1,X0)
% 27.43/3.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
% 27.43/3.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ r1_xboole_0(X2,X0) ),
% 27.43/3.99      inference(unflattening,[status(thm)],[c_1002]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_13,plain,
% 27.43/3.99      ( ~ r2_hidden(X0,X1)
% 27.43/3.99      | m1_subset_1(X0,X2)
% 27.43/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f85]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_1021,plain,
% 27.43/3.99      ( ~ v3_pre_topc(X0,sK6)
% 27.43/3.99      | ~ r2_hidden(X1,X0)
% 27.43/3.99      | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
% 27.43/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/3.99      | ~ r1_xboole_0(X2,X0) ),
% 27.43/3.99      inference(forward_subsumption_resolution,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_1003,c_13]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8496,plain,
% 27.43/3.99      ( v3_pre_topc(X0,sK6) != iProver_top
% 27.43/3.99      | r2_hidden(X1,X0) != iProver_top
% 27.43/3.99      | r2_hidden(X1,k2_pre_topc(sK6,X2)) != iProver_top
% 27.43/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X2,X0) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_10506,plain,
% 27.43/3.99      ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 27.43/3.99      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 27.43/3.99      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 27.43/3.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8544,c_8496]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_25259,plain,
% 27.43/3.99      ( r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 27.43/3.99      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 27.43/3.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_10506,c_8537]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_25281,plain,
% 27.43/3.99      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 27.43/3.99      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.43/3.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_12232,c_25259]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9404,plain,
% 27.43/3.99      ( k1_xboole_0 = k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7579]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8979,plain,
% 27.43/3.99      ( r1_xboole_0(k1_xboole_0,X0)
% 27.43/3.99      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) != k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_1]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_13072,plain,
% 27.43/3.99      ( r1_xboole_0(k1_xboole_0,k2_struct_0(X0))
% 27.43/3.99      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(X0))) != k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_8979]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_13073,plain,
% 27.43/3.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(X0))) != k1_xboole_0
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,k2_struct_0(X0)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_13072]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_13075,plain,
% 27.43/3.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(sK6))) != k1_xboole_0
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,k2_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_13073]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8980,plain,
% 27.43/3.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_5]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_21894,plain,
% 27.43/3.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(X0))) = k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_8980]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_21895,plain,
% 27.43/3.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_struct_0(sK6))) = k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_21894]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_7583,plain,
% 27.43/3.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.43/3.99      theory(equality) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_9365,plain,
% 27.43/3.99      ( r1_xboole_0(X0,X1)
% 27.43/3.99      | ~ r1_xboole_0(k1_xboole_0,X2)
% 27.43/3.99      | X1 != X2
% 27.43/3.99      | X0 != k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_7583]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_11055,plain,
% 27.43/3.99      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,X1)
% 27.43/3.99      | X1 != X0
% 27.43/3.99      | k1_xboole_0 != k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_9365]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_29456,plain,
% 27.43/3.99      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6))
% 27.43/3.99      | u1_struct_0(sK6) != X0
% 27.43/3.99      | k1_xboole_0 != k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_11055]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_59643,plain,
% 27.43/3.99      ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0(sK6))
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6))
% 27.43/3.99      | u1_struct_0(sK6) != k2_struct_0(sK6)
% 27.43/3.99      | k1_xboole_0 != k1_xboole_0 ),
% 27.43/3.99      inference(instantiation,[status(thm)],[c_29456]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_59644,plain,
% 27.43/3.99      ( u1_struct_0(sK6) != k2_struct_0(sK6)
% 27.43/3.99      | k1_xboole_0 != k1_xboole_0
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,k2_struct_0(sK6)) != iProver_top
% 27.43/3.99      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_59643]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_68338,plain,
% 27.43/3.99      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 27.43/3.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_25281,c_49,c_101,c_104,c_7608,c_7614,c_8934,c_9404,
% 27.43/3.99                 c_9952,c_13075,c_21895,c_59644]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_10,plain,
% 27.43/3.99      ( ~ r2_hidden(X0,X1)
% 27.43/3.99      | r2_hidden(X0,X2)
% 27.43/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 27.43/3.99      inference(cnf_transformation,[],[f82]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8523,plain,
% 27.43/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X0,X2) = iProver_top
% 27.43/3.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_12701,plain,
% 27.43/3.99      ( r2_hidden(X0,X1) = iProver_top
% 27.43/3.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8522,c_8523]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_68346,plain,
% 27.43/3.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.43/3.99      inference(forward_subsumption_resolution,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_68338,c_12701]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_103018,plain,
% 27.43/3.99      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top ),
% 27.43/3.99      inference(forward_subsumption_resolution,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_103012,c_68346]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_46,negated_conjecture,
% 27.43/3.99      ( ~ v1_tops_1(sK7,sK6)
% 27.43/3.99      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 27.43/3.99      inference(cnf_transformation,[],[f119]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8506,plain,
% 27.43/3.99      ( v1_tops_1(sK7,sK6) != iProver_top
% 27.43/3.99      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_26,plain,
% 27.43/3.99      ( ~ sP0(X0,X1,X2)
% 27.43/3.99      | ~ v3_pre_topc(X3,X1)
% 27.43/3.99      | ~ r2_hidden(X4,X3)
% 27.43/3.99      | ~ r2_hidden(X4,X2)
% 27.43/3.99      | ~ r2_hidden(X4,u1_struct_0(X1))
% 27.43/3.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 27.43/3.99      | ~ r1_xboole_0(X0,X3) ),
% 27.43/3.99      inference(cnf_transformation,[],[f88]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8510,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) != iProver_top
% 27.43/3.99      | v3_pre_topc(X3,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X4,X3) != iProver_top
% 27.43/3.99      | r2_hidden(X4,X2) != iProver_top
% 27.43/3.99      | r2_hidden(X4,u1_struct_0(X1)) != iProver_top
% 27.43/3.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,X3) != iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_8790,plain,
% 27.43/3.99      ( sP0(X0,X1,X2) != iProver_top
% 27.43/3.99      | v3_pre_topc(X3,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X4,X3) != iProver_top
% 27.43/3.99      | r2_hidden(X4,X2) != iProver_top
% 27.43/3.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,X3) != iProver_top ),
% 27.43/3.99      inference(forward_subsumption_resolution,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_8510,c_8523]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_15916,plain,
% 27.43/3.99      ( sP0(X0,sK6,X1) != iProver_top
% 27.43/3.99      | v1_tops_1(sK7,sK6) != iProver_top
% 27.43/3.99      | v3_pre_topc(sK8,sK6) != iProver_top
% 27.43/3.99      | r2_hidden(X2,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X2,sK8) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,sK8) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_8506,c_8790]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_44,negated_conjecture,
% 27.43/3.99      ( ~ v1_tops_1(sK7,sK6) | v3_pre_topc(sK8,sK6) ),
% 27.43/3.99      inference(cnf_transformation,[],[f121]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_59,plain,
% 27.43/3.99      ( v1_tops_1(sK7,sK6) != iProver_top
% 27.43/3.99      | v3_pre_topc(sK8,sK6) = iProver_top ),
% 27.43/3.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_16524,plain,
% 27.43/3.99      ( v1_tops_1(sK7,sK6) != iProver_top
% 27.43/3.99      | sP0(X0,sK6,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X2,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X2,sK8) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,sK8) != iProver_top ),
% 27.43/3.99      inference(global_propositional_subsumption,
% 27.43/3.99                [status(thm)],
% 27.43/3.99                [c_15916,c_59]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_16525,plain,
% 27.43/3.99      ( sP0(X0,sK6,X1) != iProver_top
% 27.43/3.99      | v1_tops_1(sK7,sK6) != iProver_top
% 27.43/3.99      | r2_hidden(X2,X1) != iProver_top
% 27.43/3.99      | r2_hidden(X2,sK8) != iProver_top
% 27.43/3.99      | r1_xboole_0(X0,sK8) != iProver_top ),
% 27.43/3.99      inference(renaming,[status(thm)],[c_16524]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_103026,plain,
% 27.43/3.99      ( v1_tops_1(sK7,sK6) != iProver_top
% 27.43/3.99      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 27.43/3.99      | r2_hidden(X0,sK8) != iProver_top
% 27.43/3.99      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 27.43/3.99      inference(superposition,[status(thm)],[c_103018,c_16525]) ).
% 27.43/3.99  
% 27.43/3.99  cnf(c_43,negated_conjecture,
% 27.43/4.00      ( ~ v1_tops_1(sK7,sK6) | r1_xboole_0(sK7,sK8) ),
% 27.43/4.00      inference(cnf_transformation,[],[f122]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1475,plain,
% 27.43/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/4.00      | r1_xboole_0(sK7,sK8)
% 27.43/4.00      | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
% 27.43/4.00      | sK6 != sK6
% 27.43/4.00      | sK7 != X0 ),
% 27.43/4.00      inference(resolution_lifted,[status(thm)],[c_43,c_970]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1476,plain,
% 27.43/4.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/4.00      | r1_xboole_0(sK7,sK8)
% 27.43/4.00      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 27.43/4.00      inference(unflattening,[status(thm)],[c_1475]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1478,plain,
% 27.43/4.00      ( r1_xboole_0(sK7,sK8) | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 27.43/4.00      inference(global_propositional_subsumption,
% 27.43/4.00                [status(thm)],
% 27.43/4.00                [c_1476,c_48]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1480,plain,
% 27.43/4.00      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 27.43/4.00      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 27.43/4.00      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_12702,plain,
% 27.43/4.00      ( v1_tops_1(sK7,sK6) != iProver_top
% 27.43/4.00      | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 27.43/4.00      | r2_hidden(X0,sK8) != iProver_top ),
% 27.43/4.00      inference(superposition,[status(thm)],[c_8506,c_8523]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_103079,plain,
% 27.43/4.00      ( r2_hidden(X0,sK8) != iProver_top ),
% 27.43/4.00      inference(global_propositional_subsumption,
% 27.43/4.00                [status(thm)],
% 27.43/4.00                [c_103026,c_49,c_53,c_101,c_104,c_1477,c_8898,c_9264,
% 27.43/4.00                 c_9770,c_12702,c_103018]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_103087,plain,
% 27.43/4.00      ( sP0(X0,sK6,sK8) = iProver_top
% 27.43/4.00      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 27.43/4.00      inference(superposition,[status(thm)],[c_26094,c_103079]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_105233,plain,
% 27.43/4.00      ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
% 27.43/4.00      inference(superposition,[status(thm)],[c_10692,c_103087]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_9490,plain,
% 27.43/4.00      ( k2_pre_topc(sK6,k1_xboole_0) = X0
% 27.43/4.00      | sP0(k1_xboole_0,sK6,X0) != iProver_top
% 27.43/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/4.00      inference(superposition,[status(thm)],[c_8522,c_8492]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_17022,plain,
% 27.43/4.00      ( k1_xboole_0 = X0
% 27.43/4.00      | sP0(k1_xboole_0,sK6,X0) != iProver_top
% 27.43/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 27.43/4.00      inference(demodulation,[status(thm)],[c_9490,c_12232]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_17030,plain,
% 27.43/4.00      ( sK8 = k1_xboole_0
% 27.43/4.00      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 27.43/4.00      | v1_tops_1(sK7,sK6) != iProver_top ),
% 27.43/4.00      inference(superposition,[status(thm)],[c_8506,c_17022]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_45,negated_conjecture,
% 27.43/4.00      ( ~ v1_tops_1(sK7,sK6) | k1_xboole_0 != sK8 ),
% 27.43/4.00      inference(cnf_transformation,[],[f120]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1450,plain,
% 27.43/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/4.00      | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
% 27.43/4.00      | sK6 != sK6
% 27.43/4.00      | sK8 != k1_xboole_0
% 27.43/4.00      | sK7 != X0 ),
% 27.43/4.00      inference(resolution_lifted,[status(thm)],[c_45,c_970]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1451,plain,
% 27.43/4.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 27.43/4.00      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 27.43/4.00      | sK8 != k1_xboole_0 ),
% 27.43/4.00      inference(unflattening,[status(thm)],[c_1450]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(c_1453,plain,
% 27.43/4.00      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) | sK8 != k1_xboole_0 ),
% 27.43/4.00      inference(global_propositional_subsumption,
% 27.43/4.00                [status(thm)],
% 27.43/4.00                [c_1451,c_48]) ).
% 27.43/4.00  
% 27.43/4.00  cnf(contradiction,plain,
% 27.43/4.00      ( $false ),
% 27.43/4.00      inference(minisat,
% 27.43/4.00                [status(thm)],
% 27.43/4.00                [c_105233,c_103018,c_17030,c_9770,c_9264,c_8898,c_1453,
% 27.43/4.00                 c_104,c_101,c_53,c_49]) ).
% 27.43/4.00  
% 27.43/4.00  
% 27.43/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.43/4.00  
% 27.43/4.00  ------                               Statistics
% 27.43/4.00  
% 27.43/4.00  ------ General
% 27.43/4.00  
% 27.43/4.00  abstr_ref_over_cycles:                  0
% 27.43/4.00  abstr_ref_under_cycles:                 0
% 27.43/4.00  gc_basic_clause_elim:                   0
% 27.43/4.00  forced_gc_time:                         0
% 27.43/4.00  parsing_time:                           0.014
% 27.43/4.00  unif_index_cands_time:                  0.
% 27.43/4.00  unif_index_add_time:                    0.
% 27.43/4.00  orderings_time:                         0.
% 27.43/4.00  out_proof_time:                         0.027
% 27.43/4.00  total_time:                             3.19
% 27.43/4.00  num_of_symbols:                         61
% 27.43/4.00  num_of_terms:                           55615
% 27.43/4.00  
% 27.43/4.00  ------ Preprocessing
% 27.43/4.00  
% 27.43/4.00  num_of_splits:                          0
% 27.43/4.00  num_of_split_atoms:                     0
% 27.43/4.00  num_of_reused_defs:                     0
% 27.43/4.00  num_eq_ax_congr_red:                    61
% 27.43/4.00  num_of_sem_filtered_clauses:            1
% 27.43/4.00  num_of_subtypes:                        0
% 27.43/4.00  monotx_restored_types:                  0
% 27.43/4.00  sat_num_of_epr_types:                   0
% 27.43/4.00  sat_num_of_non_cyclic_types:            0
% 27.43/4.00  sat_guarded_non_collapsed_types:        0
% 27.43/4.00  num_pure_diseq_elim:                    0
% 27.43/4.00  simp_replaced_by:                       0
% 27.43/4.00  res_preprocessed:                       223
% 27.43/4.00  prep_upred:                             0
% 27.43/4.00  prep_unflattend:                        285
% 27.43/4.00  smt_new_axioms:                         0
% 27.43/4.00  pred_elim_cands:                        7
% 27.43/4.00  pred_elim:                              5
% 27.43/4.00  pred_elim_cl:                           6
% 27.43/4.00  pred_elim_cycles:                       17
% 27.43/4.00  merged_defs:                            8
% 27.43/4.00  merged_defs_ncl:                        0
% 27.43/4.00  bin_hyper_res:                          8
% 27.43/4.00  prep_cycles:                            4
% 27.43/4.00  pred_elim_time:                         0.112
% 27.43/4.00  splitting_time:                         0.
% 27.43/4.00  sem_filter_time:                        0.
% 27.43/4.00  monotx_time:                            0.
% 27.43/4.00  subtype_inf_time:                       0.
% 27.43/4.00  
% 27.43/4.00  ------ Problem properties
% 27.43/4.00  
% 27.43/4.00  clauses:                                45
% 27.43/4.00  conjectures:                            6
% 27.43/4.00  epr:                                    3
% 27.43/4.00  horn:                                   30
% 27.43/4.00  ground:                                 7
% 27.43/4.00  unary:                                  11
% 27.43/4.00  binary:                                 9
% 27.43/4.00  lits:                                   130
% 27.43/4.00  lits_eq:                                18
% 27.43/4.00  fd_pure:                                0
% 27.43/4.00  fd_pseudo:                              0
% 27.43/4.00  fd_cond:                                1
% 27.43/4.00  fd_pseudo_cond:                         1
% 27.43/4.00  ac_symbols:                             0
% 27.43/4.00  
% 27.43/4.00  ------ Propositional Solver
% 27.43/4.00  
% 27.43/4.00  prop_solver_calls:                      42
% 27.43/4.00  prop_fast_solver_calls:                 8224
% 27.43/4.00  smt_solver_calls:                       0
% 27.43/4.00  smt_fast_solver_calls:                  0
% 27.43/4.00  prop_num_of_clauses:                    31216
% 27.43/4.00  prop_preprocess_simplified:             59886
% 27.43/4.00  prop_fo_subsumed:                       378
% 27.43/4.00  prop_solver_time:                       0.
% 27.43/4.00  smt_solver_time:                        0.
% 27.43/4.00  smt_fast_solver_time:                   0.
% 27.43/4.00  prop_fast_solver_time:                  0.
% 27.43/4.00  prop_unsat_core_time:                   0.003
% 27.43/4.00  
% 27.43/4.00  ------ QBF
% 27.43/4.00  
% 27.43/4.00  qbf_q_res:                              0
% 27.43/4.00  qbf_num_tautologies:                    0
% 27.43/4.00  qbf_prep_cycles:                        0
% 27.43/4.00  
% 27.43/4.00  ------ BMC1
% 27.43/4.00  
% 27.43/4.00  bmc1_current_bound:                     -1
% 27.43/4.00  bmc1_last_solved_bound:                 -1
% 27.43/4.00  bmc1_unsat_core_size:                   -1
% 27.43/4.00  bmc1_unsat_core_parents_size:           -1
% 27.43/4.00  bmc1_merge_next_fun:                    0
% 27.43/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.43/4.00  
% 27.43/4.00  ------ Instantiation
% 27.43/4.00  
% 27.43/4.00  inst_num_of_clauses:                    2521
% 27.43/4.00  inst_num_in_passive:                    1367
% 27.43/4.00  inst_num_in_active:                     3040
% 27.43/4.00  inst_num_in_unprocessed:                231
% 27.43/4.00  inst_num_of_loops:                      4039
% 27.43/4.00  inst_num_of_learning_restarts:          1
% 27.43/4.00  inst_num_moves_active_passive:          994
% 27.43/4.00  inst_lit_activity:                      0
% 27.43/4.00  inst_lit_activity_moves:                3
% 27.43/4.00  inst_num_tautologies:                   0
% 27.43/4.00  inst_num_prop_implied:                  0
% 27.43/4.00  inst_num_existing_simplified:           0
% 27.43/4.00  inst_num_eq_res_simplified:             0
% 27.43/4.00  inst_num_child_elim:                    0
% 27.43/4.00  inst_num_of_dismatching_blockings:      4833
% 27.43/4.00  inst_num_of_non_proper_insts:           9080
% 27.43/4.00  inst_num_of_duplicates:                 0
% 27.43/4.00  inst_inst_num_from_inst_to_res:         0
% 27.43/4.00  inst_dismatching_checking_time:         0.
% 27.43/4.00  
% 27.43/4.00  ------ Resolution
% 27.43/4.00  
% 27.43/4.00  res_num_of_clauses:                     63
% 27.43/4.00  res_num_in_passive:                     63
% 27.43/4.00  res_num_in_active:                      0
% 27.43/4.00  res_num_of_loops:                       227
% 27.43/4.00  res_forward_subset_subsumed:            310
% 27.43/4.00  res_backward_subset_subsumed:           2
% 27.43/4.00  res_forward_subsumed:                   2
% 27.43/4.00  res_backward_subsumed:                  0
% 27.43/4.00  res_forward_subsumption_resolution:     28
% 27.43/4.00  res_backward_subsumption_resolution:    0
% 27.43/4.00  res_clause_to_clause_subsumption:       15146
% 27.43/4.00  res_orphan_elimination:                 0
% 27.43/4.00  res_tautology_del:                      465
% 27.43/4.00  res_num_eq_res_simplified:              0
% 27.43/4.00  res_num_sel_changes:                    0
% 27.43/4.00  res_moves_from_active_to_pass:          0
% 27.43/4.00  
% 27.43/4.00  ------ Superposition
% 27.43/4.00  
% 27.43/4.00  sup_time_total:                         0.
% 27.43/4.00  sup_time_generating:                    0.
% 27.43/4.00  sup_time_sim_full:                      0.
% 27.43/4.00  sup_time_sim_immed:                     0.
% 27.43/4.00  
% 27.43/4.00  sup_num_of_clauses:                     1447
% 27.43/4.00  sup_num_in_active:                      513
% 27.43/4.00  sup_num_in_passive:                     934
% 27.43/4.00  sup_num_of_loops:                       807
% 27.43/4.00  sup_fw_superposition:                   2135
% 27.43/4.00  sup_bw_superposition:                   2943
% 27.43/4.00  sup_immediate_simplified:               2065
% 27.43/4.00  sup_given_eliminated:                   6
% 27.43/4.00  comparisons_done:                       0
% 27.43/4.00  comparisons_avoided:                    453
% 27.43/4.00  
% 27.43/4.00  ------ Simplifications
% 27.43/4.00  
% 27.43/4.00  
% 27.43/4.00  sim_fw_subset_subsumed:                 219
% 27.43/4.00  sim_bw_subset_subsumed:                 240
% 27.43/4.00  sim_fw_subsumed:                        479
% 27.43/4.00  sim_bw_subsumed:                        68
% 27.43/4.00  sim_fw_subsumption_res:                 115
% 27.43/4.00  sim_bw_subsumption_res:                 3
% 27.43/4.00  sim_tautology_del:                      353
% 27.43/4.00  sim_eq_tautology_del:                   412
% 27.43/4.00  sim_eq_res_simp:                        1
% 27.43/4.00  sim_fw_demodulated:                     1356
% 27.43/4.00  sim_bw_demodulated:                     197
% 27.43/4.00  sim_light_normalised:                   152
% 27.43/4.00  sim_joinable_taut:                      0
% 27.43/4.00  sim_joinable_simp:                      0
% 27.43/4.00  sim_ac_normalised:                      0
% 27.43/4.00  sim_smt_subsumption:                    0
% 27.43/4.00  
%------------------------------------------------------------------------------
