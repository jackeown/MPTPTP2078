%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:51 EST 2020

% Result     : Theorem 54.70s
% Output     : CNFRefutation 54.70s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2055)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f119,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f68,f79,f79])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f64,plain,
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

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f63,f66,f65,f64])).

fof(f111,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f96,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f95,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f107,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f41,plain,(
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

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f49,f52,f51,f50])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X2,X0,X5,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_xboole_0(X0,X5)
      | ~ r2_hidden(sK2(X0,X1,X2),X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f114,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_xboole_0(X0,sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK7,X3)
      | ~ v3_pre_topc(X3,sK6)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | v1_tops_1(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f67])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f28,f42,f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X1,X2) = X0
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
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

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f116,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f117,plain,
    ( r1_xboole_0(sK7,sK8)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f125,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f16,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f118,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f75,f118])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f123,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f73,f118])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f115,plain,
    ( k1_xboole_0 != sK8
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2161,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1549,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2826,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2161,c_1549])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1507,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_26,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1527,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2632,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1527])).

cnf(c_25,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1528,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2727,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_2632,c_1528])).

cnf(c_37,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1516,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3303,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1516])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_48,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_49,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3306,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_48,c_49])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1535,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X3)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1536,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8179,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1536])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_517,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5758,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_525,c_517])).

cnf(c_518,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4000,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_518,c_517])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4104,plain,
    ( X0 = k2_subset_1(X0) ),
    inference(resolution,[status(thm)],[c_4000,c_5])).

cnf(c_15854,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_5758,c_4104])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_15854,c_7])).

cnf(c_12794,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
    inference(resolution,[status(thm)],[c_17,c_18])).

cnf(c_16245,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16239,c_12794])).

cnf(c_16246,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16245])).

cnf(c_23743,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8179,c_16246])).

cnf(c_23744,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23743])).

cnf(c_23751,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3306,c_23744])).

cnf(c_43,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1510,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1545,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3942,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1545])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1540,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4604,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1540])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1537,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5486,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1537])).

cnf(c_44,negated_conjecture,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(sK7,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1509,plain,
    ( k1_xboole_0 = X0
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12521,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_1509])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2)
    | v3_pre_topc(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1538,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4574,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1538])).

cnf(c_12754,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12521,c_4574])).

cnf(c_12758,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4604,c_12754])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_98,plain,
    ( l1_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_101,plain,
    ( ~ l1_struct_0(sK6)
    | k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2049,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2054,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2049])).

cnf(c_2056,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_35,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2077,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2078,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2068,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2328,plain,
    ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2068])).

cnf(c_2331,plain,
    ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2328])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k2_pre_topc(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2561,plain,
    ( ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | ~ sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,sK7) = k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2567,plain,
    ( k2_pre_topc(sK6,sK7) = k2_subset_1(u1_struct_0(sK6))
    | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top
    | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2561])).

cnf(c_3893,plain,
    ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2947,plain,
    ( X0 != X1
    | k2_struct_0(X2) != X1
    | k2_struct_0(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_4906,plain,
    ( X0 != u1_struct_0(X1)
    | k2_struct_0(X1) = X0
    | k2_struct_0(X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2947])).

cnf(c_10613,plain,
    ( k2_struct_0(sK6) != u1_struct_0(sK6)
    | k2_struct_0(sK6) = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4906])).

cnf(c_527,plain,
    ( ~ sP0(X0,X1,X2)
    | sP0(X0,X1,X3)
    | X3 != X2 ),
    theory(equality)).

cnf(c_3844,plain,
    ( ~ sP0(sK7,sK6,X0)
    | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
    | k2_subset_1(u1_struct_0(sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_13542,plain,
    ( ~ sP0(sK7,sK6,u1_struct_0(sK6))
    | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3844])).

cnf(c_13543,plain,
    ( k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top
    | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13542])).

cnf(c_2231,plain,
    ( k2_pre_topc(sK6,sK7) != X0
    | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_2935,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) != k2_subset_1(X0)
    | k2_struct_0(sK6) != k2_subset_1(X0) ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_17575,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) != k2_subset_1(u1_struct_0(sK6))
    | k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2935])).

cnf(c_24731,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12758,c_46,c_49,c_50,c_98,c_101,c_2056,c_2078,c_2331,c_2567,c_3893,c_10613,c_13543,c_17575])).

cnf(c_1508,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_36,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1517,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3639,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1517])).

cnf(c_3650,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3639,c_2727])).

cnf(c_4337,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3650,c_49])).

cnf(c_4338,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4337])).

cnf(c_24743,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_24731,c_4338])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1539,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_26598,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24743,c_1539])).

cnf(c_5939,plain,
    ( sP0(X0,X1,u1_struct_0(X1))
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6454,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6))
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5939])).

cnf(c_6456,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6454])).

cnf(c_1546,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1562,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1546,c_5])).

cnf(c_1529,plain,
    ( sP1(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5584,plain,
    ( sP1(u1_struct_0(X0),X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1529])).

cnf(c_14660,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_5584])).

cnf(c_14988,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14660,c_49])).

cnf(c_1542,plain,
    ( k2_pre_topc(X0,X1) = X2
    | sP1(X2,X0,X1) != iProver_top
    | sP0(X1,X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14993,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14988,c_1542])).

cnf(c_27897,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26598,c_6456,c_14993])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1544,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3941,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_1545])).

cnf(c_27905,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27897,c_3941])).

cnf(c_34,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1519,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_171182,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_27905,c_1519])).

cnf(c_14994,plain,
    ( ~ sP0(sK7,sK6,u1_struct_0(sK6))
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14993])).

cnf(c_26604,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v3_pre_topc(k1_xboole_0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_24743,c_4574])).

cnf(c_26740,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6))
    | v3_pre_topc(k1_xboole_0,sK6)
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26604])).

cnf(c_33,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1520,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1543,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1854,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1520,c_1543])).

cnf(c_10731,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k2_pre_topc(X0,X2)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_1854])).

cnf(c_2825,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1549])).

cnf(c_36250,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10731,c_2825,c_3941])).

cnf(c_36258,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_36250])).

cnf(c_171235,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27905,c_36258])).

cnf(c_171791,plain,
    ( ~ v3_pre_topc(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_171235])).

cnf(c_171793,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK6)
    | ~ l1_pre_topc(sK6)
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_171791])).

cnf(c_171829,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_171182,c_46,c_14994,c_26740,c_171793])).

cnf(c_174342,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_171829,c_1519])).

cnf(c_174474,plain,
    ( v2_struct_0(sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_174342,c_49,c_50])).

cnf(c_174475,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_174474])).

cnf(c_3910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1543])).

cnf(c_174483,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_174475,c_3910])).

cnf(c_174489,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3942,c_174483])).

cnf(c_528,plain,
    ( ~ sP1(X0,X1,X2)
    | sP1(X3,X1,X2)
    | X3 != X0 ),
    theory(equality)).

cnf(c_2562,plain,
    ( sP1(X0,sK6,sK7)
    | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | X0 != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_17561,plain,
    ( sP1(k2_struct_0(sK6),sK6,sK7)
    | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_17562,plain,
    ( k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
    | sP1(k2_struct_0(sK6),sK6,sK7) = iProver_top
    | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17561])).

cnf(c_30400,plain,
    ( ~ sP1(k2_struct_0(sK6),sK6,sK7)
    | ~ sP0(sK7,sK6,k2_struct_0(sK6))
    | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_30406,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | sP1(k2_struct_0(sK6),sK6,sK7) != iProver_top
    | sP0(sK7,sK6,k2_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30400])).

cnf(c_6901,plain,
    ( sP0(sK7,sK6,X0)
    | ~ sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
    | X0 != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_42142,plain,
    ( sP0(sK7,sK6,k2_struct_0(sK6))
    | ~ sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
    | k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6901])).

cnf(c_42143,plain,
    ( k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
    | sP0(sK7,sK6,k2_struct_0(sK6)) = iProver_top
    | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42142])).

cnf(c_10733,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1854])).

cnf(c_41,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | v3_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_56,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_11902,plain,
    ( r1_xboole_0(X1,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10733,c_49,c_56])).

cnf(c_11903,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_11902])).

cnf(c_11916,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_11903])).

cnf(c_40,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | r1_xboole_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_57,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_12053,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11916,c_57])).

cnf(c_12054,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_12053])).

cnf(c_172189,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_171829,c_12054])).

cnf(c_12,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1541,plain,
    ( sP1(k2_pre_topc(X0,X1),X0,X1) != iProver_top
    | sP0(X1,X0,k2_pre_topc(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_174345,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) != iProver_top
    | sP0(sK7,sK6,k2_pre_topc(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_171829,c_1541])).

cnf(c_174359,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) != iProver_top
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_174345,c_171829])).

cnf(c_95526,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK6)),sK6)
    | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
    | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_44,c_7])).

cnf(c_2651,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK6)),sK6)
    | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
    | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_44,c_7])).

cnf(c_65,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_550,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_2437,plain,
    ( X0 != X1
    | X0 = k2_struct_0(X2)
    | k2_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_2944,plain,
    ( X0 = k2_struct_0(X1)
    | X0 != u1_struct_0(X1)
    | k2_struct_0(X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_4896,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_subset_1(u1_struct_0(X0)) = k2_struct_0(X0)
    | k2_subset_1(u1_struct_0(X0)) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2944])).

cnf(c_4898,plain,
    ( k2_struct_0(sK6) != u1_struct_0(sK6)
    | k2_subset_1(u1_struct_0(sK6)) = k2_struct_0(sK6)
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4896])).

cnf(c_529,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2125,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k2_struct_0(X2),X2)
    | X1 != X2
    | X0 != k2_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_10537,plain,
    ( ~ v3_pre_topc(k2_struct_0(X0),X0)
    | v3_pre_topc(k2_subset_1(u1_struct_0(X0)),X1)
    | X1 != X0
    | k2_subset_1(u1_struct_0(X0)) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_10539,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK6),sK6)
    | v3_pre_topc(k2_subset_1(u1_struct_0(sK6)),sK6)
    | k2_subset_1(u1_struct_0(sK6)) != k2_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_10537])).

cnf(c_72116,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
    | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2651,c_47,c_46,c_65,c_98,c_101,c_550,c_3893,c_4898,c_10539])).

cnf(c_95658,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
    | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_95526,c_47,c_46,c_65,c_98,c_101,c_550,c_2651,c_3893,c_4898,c_10539])).

cnf(c_100450,plain,
    ( m1_subset_1(X0,k2_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_525,c_25])).

cnf(c_165444,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),u1_struct_0(X0))
    | m1_subset_1(k1_xboole_0,k2_struct_0(X0))
    | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
    | ~ l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_95658,c_100450])).

cnf(c_174430,plain,
    ( v1_tops_1(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165444,c_46,c_49,c_45,c_50,c_98,c_101,c_2056,c_2077,c_2331,c_3893,c_10613,c_13543,c_14660,c_17562,c_30406,c_42143,c_174359])).

cnf(c_174441,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_174430,c_43])).

cnf(c_174540,plain,
    ( r2_hidden(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK8) ),
    inference(resolution,[status(thm)],[c_174441,c_8])).

cnf(c_174545,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174540])).

cnf(c_175217,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_174489,c_46,c_49,c_50,c_98,c_101,c_2056,c_2078,c_2331,c_3893,c_10613,c_13543,c_14660,c_17562,c_30406,c_42143,c_172189,c_174359,c_174545])).

cnf(c_175225,plain,
    ( sP0(X0,sK6,sK8) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23751,c_175217])).

cnf(c_179538,plain,
    ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_175225])).

cnf(c_95699,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_96283,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_95699])).

cnf(c_146237,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_96283])).

cnf(c_1513,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_24745,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_24731,c_1513])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1548,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_24836,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24745,c_1548])).

cnf(c_28,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1525,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12515,plain,
    ( k2_pre_topc(X0,sK3(X1,X0,u1_struct_0(X0))) = sK3(X1,X0,u1_struct_0(X0))
    | sP0(X1,X0,u1_struct_0(X0)) = iProver_top
    | v4_pre_topc(sK3(X1,X0,u1_struct_0(X0)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_1525])).

cnf(c_25267,plain,
    ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK3(sK7,sK6,u1_struct_0(sK6))
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24836,c_12515])).

cnf(c_2059,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2064,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2059])).

cnf(c_2066,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1547,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3614,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1544,c_1547])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1565,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_3])).

cnf(c_3627,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3614,c_3,c_1565])).

cnf(c_38,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1515,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3759,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3627,c_1515])).

cnf(c_3778,plain,
    ( v4_pre_topc(k1_xboole_0,sK6) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_5582,plain,
    ( sP1(sK8,sK6,X0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1529])).

cnf(c_6216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | sP1(sK8,sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5582,c_49])).

cnf(c_6217,plain,
    ( sP1(sK8,sK6,X0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6216])).

cnf(c_12519,plain,
    ( sP1(sK8,sK6,sK3(X0,sK6,u1_struct_0(sK6))) = iProver_top
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_6217])).

cnf(c_14122,plain,
    ( k2_pre_topc(sK6,sK3(X0,sK6,u1_struct_0(sK6))) = sK8
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | sP0(sK3(X0,sK6,u1_struct_0(sK6)),sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12519,c_1542])).

cnf(c_25258,plain,
    ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK8
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24836,c_14122])).

cnf(c_30439,plain,
    ( ~ r1_xboole_0(sK7,sK8)
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_30440,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30439])).

cnf(c_47448,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25258,c_57,c_30440])).

cnf(c_49004,plain,
    ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
    | k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK3(sK7,sK6,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25267,c_47,c_46,c_49,c_45,c_50,c_98,c_101,c_2055,c_2065,c_2078,c_2328,c_3304,c_3779,c_3893,c_10613,c_13542,c_17561,c_25408,c_30400,c_42142,c_47448])).

cnf(c_49005,plain,
    ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK3(sK7,sK6,u1_struct_0(sK6))
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_49004])).

cnf(c_49009,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k2_pre_topc(sK6,k1_xboole_0)
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24836,c_49005])).

cnf(c_49645,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49009,c_24836])).

cnf(c_4797,plain,
    ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_1525])).

cnf(c_4828,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4797])).

cnf(c_49976,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49645,c_48,c_49,c_2066,c_3303,c_3778,c_4828])).

cnf(c_6225,plain,
    ( sP1(sK8,sK6,k1_xboole_0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_6217])).

cnf(c_7203,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = sK8
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6225,c_1542])).

cnf(c_49982,plain,
    ( sK8 = k1_xboole_0
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49976,c_7203])).

cnf(c_2371,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_42,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_179538,c_174359,c_146237,c_49982,c_42143,c_30406,c_17562,c_14660,c_13543,c_10613,c_3893,c_2371,c_2331,c_2078,c_2077,c_2056,c_101,c_98,c_42,c_50,c_45,c_49,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 54.70/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.70/7.49  
% 54.70/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.70/7.49  
% 54.70/7.49  ------  iProver source info
% 54.70/7.49  
% 54.70/7.49  git: date: 2020-06-30 10:37:57 +0100
% 54.70/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.70/7.49  git: non_committed_changes: false
% 54.70/7.49  git: last_make_outside_of_git: false
% 54.70/7.49  
% 54.70/7.49  ------ 
% 54.70/7.49  ------ Parsing...
% 54.70/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.70/7.49  
% 54.70/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 54.70/7.49  
% 54.70/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.70/7.49  
% 54.70/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.70/7.49  ------ Proving...
% 54.70/7.49  ------ Problem Properties 
% 54.70/7.49  
% 54.70/7.49  
% 54.70/7.49  clauses                                 48
% 54.70/7.49  conjectures                             8
% 54.70/7.49  EPR                                     6
% 54.70/7.49  Horn                                    33
% 54.70/7.49  unary                                   9
% 54.70/7.49  binary                                  11
% 54.70/7.49  lits                                    155
% 54.70/7.49  lits eq                                 15
% 54.70/7.49  fd_pure                                 0
% 54.70/7.49  fd_pseudo                               0
% 54.70/7.49  fd_cond                                 1
% 54.70/7.49  fd_pseudo_cond                          1
% 54.70/7.49  AC symbols                              0
% 54.70/7.49  
% 54.70/7.49  ------ Input Options Time Limit: Unbounded
% 54.70/7.49  
% 54.70/7.49  
% 54.70/7.49  ------ 
% 54.70/7.49  Current options:
% 54.70/7.49  ------ 
% 54.70/7.49  
% 54.70/7.49  
% 54.70/7.49  
% 54.70/7.49  
% 54.70/7.49  ------ Proving...
% 54.70/7.49  
% 54.70/7.49  
% 54.70/7.49  % SZS status Theorem for theBenchmark.p
% 54.70/7.49  
% 54.70/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 54.70/7.49  
% 54.70/7.49  fof(f4,axiom,(
% 54.70/7.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f72,plain,(
% 54.70/7.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 54.70/7.49    inference(cnf_transformation,[],[f4])).
% 54.70/7.49  
% 54.70/7.49  fof(f11,axiom,(
% 54.70/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f79,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f11])).
% 54.70/7.49  
% 54.70/7.49  fof(f122,plain,(
% 54.70/7.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 54.70/7.49    inference(definition_unfolding,[],[f72,f79])).
% 54.70/7.49  
% 54.70/7.49  fof(f1,axiom,(
% 54.70/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f68,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f1])).
% 54.70/7.49  
% 54.70/7.49  fof(f119,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 54.70/7.49    inference(definition_unfolding,[],[f68,f79,f79])).
% 54.70/7.49  
% 54.70/7.49  fof(f2,axiom,(
% 54.70/7.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f44,plain,(
% 54.70/7.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 54.70/7.49    inference(nnf_transformation,[],[f2])).
% 54.70/7.49  
% 54.70/7.49  fof(f70,plain,(
% 54.70/7.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 54.70/7.49    inference(cnf_transformation,[],[f44])).
% 54.70/7.49  
% 54.70/7.49  fof(f120,plain,(
% 54.70/7.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 54.70/7.49    inference(definition_unfolding,[],[f70,f79])).
% 54.70/7.49  
% 54.70/7.49  fof(f21,conjecture,(
% 54.70/7.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f22,negated_conjecture,(
% 54.70/7.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 54.70/7.49    inference(negated_conjecture,[],[f21])).
% 54.70/7.49  
% 54.70/7.49  fof(f39,plain,(
% 54.70/7.49    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 54.70/7.49    inference(ennf_transformation,[],[f22])).
% 54.70/7.49  
% 54.70/7.49  fof(f40,plain,(
% 54.70/7.49    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f39])).
% 54.70/7.49  
% 54.70/7.49  fof(f61,plain,(
% 54.70/7.49    ? [X0] : (? [X1] : (((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.70/7.49    inference(nnf_transformation,[],[f40])).
% 54.70/7.49  
% 54.70/7.49  fof(f62,plain,(
% 54.70/7.49    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f61])).
% 54.70/7.49  
% 54.70/7.49  fof(f63,plain,(
% 54.70/7.49    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.70/7.49    inference(rectify,[],[f62])).
% 54.70/7.49  
% 54.70/7.49  fof(f66,plain,(
% 54.70/7.49    ( ! [X0,X1] : (? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK8) & v3_pre_topc(sK8,X0) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f65,plain,(
% 54.70/7.49    ( ! [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (r1_xboole_0(sK7,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(sK7,X0)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f64,plain,(
% 54.70/7.49    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK6) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(X1,sK6)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f67,plain,(
% 54.70/7.49    (((r1_xboole_0(sK7,sK8) & v3_pre_topc(sK8,sK6) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(sK7,sK6)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 54.70/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f63,f66,f65,f64])).
% 54.70/7.49  
% 54.70/7.49  fof(f111,plain,(
% 54.70/7.49    l1_pre_topc(sK6)),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f15,axiom,(
% 54.70/7.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f30,plain,(
% 54.70/7.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f15])).
% 54.70/7.49  
% 54.70/7.49  fof(f96,plain,(
% 54.70/7.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f30])).
% 54.70/7.49  
% 54.70/7.49  fof(f14,axiom,(
% 54.70/7.49    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f29,plain,(
% 54.70/7.49    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f14])).
% 54.70/7.49  
% 54.70/7.49  fof(f95,plain,(
% 54.70/7.49    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f29])).
% 54.70/7.49  
% 54.70/7.49  fof(f19,axiom,(
% 54.70/7.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f36,plain,(
% 54.70/7.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 54.70/7.49    inference(ennf_transformation,[],[f19])).
% 54.70/7.49  
% 54.70/7.49  fof(f37,plain,(
% 54.70/7.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f36])).
% 54.70/7.49  
% 54.70/7.49  fof(f107,plain,(
% 54.70/7.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f37])).
% 54.70/7.49  
% 54.70/7.49  fof(f110,plain,(
% 54.70/7.49    v2_pre_topc(sK6)),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f41,plain,(
% 54.70/7.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0))))),
% 54.70/7.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 54.70/7.49  
% 54.70/7.49  fof(f47,plain,(
% 54.70/7.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2))) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 54.70/7.49    inference(nnf_transformation,[],[f41])).
% 54.70/7.49  
% 54.70/7.49  fof(f48,plain,(
% 54.70/7.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 54.70/7.49    inference(flattening,[],[f47])).
% 54.70/7.49  
% 54.70/7.49  fof(f49,plain,(
% 54.70/7.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 54.70/7.49    inference(rectify,[],[f48])).
% 54.70/7.49  
% 54.70/7.49  fof(f52,plain,(
% 54.70/7.49    ! [X6,X1,X0] : (? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))))),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f51,plain,(
% 54.70/7.49    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(X3,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f50,plain,(
% 54.70/7.49    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1))) => ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(sK2(X0,X1,X2),X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f53,plain,(
% 54.70/7.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 54.70/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f49,f52,f51,f50])).
% 54.70/7.49  
% 54.70/7.49  fof(f88,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f53])).
% 54.70/7.49  
% 54.70/7.49  fof(f89,plain,(
% 54.70/7.49    ( ! [X2,X0,X5,X1] : (sP0(X0,X1,X2) | ~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f53])).
% 54.70/7.49  
% 54.70/7.49  fof(f6,axiom,(
% 54.70/7.49    ! [X0] : k2_subset_1(X0) = X0),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f74,plain,(
% 54.70/7.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 54.70/7.49    inference(cnf_transformation,[],[f6])).
% 54.70/7.49  
% 54.70/7.49  fof(f8,axiom,(
% 54.70/7.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f76,plain,(
% 54.70/7.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f8])).
% 54.70/7.49  
% 54.70/7.49  fof(f114,plain,(
% 54.70/7.49    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_tops_1(sK7,sK6)),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f9,axiom,(
% 54.70/7.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f24,plain,(
% 54.70/7.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.70/7.49    inference(ennf_transformation,[],[f9])).
% 54.70/7.49  
% 54.70/7.49  fof(f77,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f24])).
% 54.70/7.49  
% 54.70/7.49  fof(f93,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_xboole_0(X0,sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f53])).
% 54.70/7.49  
% 54.70/7.49  fof(f90,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f53])).
% 54.70/7.49  
% 54.70/7.49  fof(f113,plain,(
% 54.70/7.49    ( ! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | v1_tops_1(sK7,sK6)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f91,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f53])).
% 54.70/7.49  
% 54.70/7.49  fof(f112,plain,(
% 54.70/7.49    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f18,axiom,(
% 54.70/7.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f35,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f18])).
% 54.70/7.49  
% 54.70/7.49  fof(f59,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(nnf_transformation,[],[f35])).
% 54.70/7.49  
% 54.70/7.49  fof(f106,plain,(
% 54.70/7.49    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f59])).
% 54.70/7.49  
% 54.70/7.49  fof(f13,axiom,(
% 54.70/7.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f27,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f13])).
% 54.70/7.49  
% 54.70/7.49  fof(f28,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f27])).
% 54.70/7.49  
% 54.70/7.49  fof(f42,plain,(
% 54.70/7.49    ! [X2,X0,X1] : ((k2_pre_topc(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 54.70/7.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 54.70/7.49  
% 54.70/7.49  fof(f43,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(definition_folding,[],[f28,f42,f41])).
% 54.70/7.49  
% 54.70/7.49  fof(f94,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f43])).
% 54.70/7.49  
% 54.70/7.49  fof(f45,plain,(
% 54.70/7.49    ! [X2,X0,X1] : (((k2_pre_topc(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_pre_topc(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 54.70/7.49    inference(nnf_transformation,[],[f42])).
% 54.70/7.49  
% 54.70/7.49  fof(f46,plain,(
% 54.70/7.49    ! [X0,X1,X2] : (((k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 54.70/7.49    inference(rectify,[],[f45])).
% 54.70/7.49  
% 54.70/7.49  fof(f82,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f46])).
% 54.70/7.49  
% 54.70/7.49  fof(f105,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f59])).
% 54.70/7.49  
% 54.70/7.49  fof(f92,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f53])).
% 54.70/7.49  
% 54.70/7.49  fof(f10,axiom,(
% 54.70/7.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f78,plain,(
% 54.70/7.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f10])).
% 54.70/7.49  
% 54.70/7.49  fof(f17,axiom,(
% 54.70/7.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f33,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f17])).
% 54.70/7.49  
% 54.70/7.49  fof(f34,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f33])).
% 54.70/7.49  
% 54.70/7.49  fof(f54,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(nnf_transformation,[],[f34])).
% 54.70/7.49  
% 54.70/7.49  fof(f55,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f54])).
% 54.70/7.49  
% 54.70/7.49  fof(f56,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(rectify,[],[f55])).
% 54.70/7.49  
% 54.70/7.49  fof(f57,plain,(
% 54.70/7.49    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 54.70/7.49    introduced(choice_axiom,[])).
% 54.70/7.49  
% 54.70/7.49  fof(f58,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).
% 54.70/7.49  
% 54.70/7.49  fof(f99,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (~v2_struct_0(X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f58])).
% 54.70/7.49  
% 54.70/7.49  fof(f100,plain,(
% 54.70/7.49    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f58])).
% 54.70/7.49  
% 54.70/7.49  fof(f12,axiom,(
% 54.70/7.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f25,plain,(
% 54.70/7.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 54.70/7.49    inference(ennf_transformation,[],[f12])).
% 54.70/7.49  
% 54.70/7.49  fof(f26,plain,(
% 54.70/7.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 54.70/7.49    inference(flattening,[],[f25])).
% 54.70/7.49  
% 54.70/7.49  fof(f80,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f26])).
% 54.70/7.49  
% 54.70/7.49  fof(f116,plain,(
% 54.70/7.49    v3_pre_topc(sK8,sK6) | ~v1_tops_1(sK7,sK6)),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f117,plain,(
% 54.70/7.49    r1_xboole_0(sK7,sK8) | ~v1_tops_1(sK7,sK6)),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  fof(f81,plain,(
% 54.70/7.49    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f46])).
% 54.70/7.49  
% 54.70/7.49  fof(f125,plain,(
% 54.70/7.49    ( ! [X2,X1] : (sP0(X2,X1,k2_pre_topc(X1,X2)) | ~sP1(k2_pre_topc(X1,X2),X1,X2)) )),
% 54.70/7.49    inference(equality_resolution,[],[f81])).
% 54.70/7.49  
% 54.70/7.49  fof(f69,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f44])).
% 54.70/7.49  
% 54.70/7.49  fof(f121,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 54.70/7.49    inference(definition_unfolding,[],[f69,f79])).
% 54.70/7.49  
% 54.70/7.49  fof(f16,axiom,(
% 54.70/7.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f31,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f16])).
% 54.70/7.49  
% 54.70/7.49  fof(f32,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(flattening,[],[f31])).
% 54.70/7.49  
% 54.70/7.49  fof(f97,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f32])).
% 54.70/7.49  
% 54.70/7.49  fof(f7,axiom,(
% 54.70/7.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f23,plain,(
% 54.70/7.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.70/7.49    inference(ennf_transformation,[],[f7])).
% 54.70/7.49  
% 54.70/7.49  fof(f75,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f23])).
% 54.70/7.49  
% 54.70/7.49  fof(f3,axiom,(
% 54.70/7.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f71,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.70/7.49    inference(cnf_transformation,[],[f3])).
% 54.70/7.49  
% 54.70/7.49  fof(f118,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 54.70/7.49    inference(definition_unfolding,[],[f71,f79])).
% 54.70/7.49  
% 54.70/7.49  fof(f124,plain,(
% 54.70/7.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.70/7.49    inference(definition_unfolding,[],[f75,f118])).
% 54.70/7.49  
% 54.70/7.49  fof(f5,axiom,(
% 54.70/7.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f73,plain,(
% 54.70/7.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 54.70/7.49    inference(cnf_transformation,[],[f5])).
% 54.70/7.49  
% 54.70/7.49  fof(f123,plain,(
% 54.70/7.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 54.70/7.49    inference(definition_unfolding,[],[f73,f118])).
% 54.70/7.49  
% 54.70/7.49  fof(f20,axiom,(
% 54.70/7.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 54.70/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.70/7.49  
% 54.70/7.49  fof(f38,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(ennf_transformation,[],[f20])).
% 54.70/7.49  
% 54.70/7.49  fof(f60,plain,(
% 54.70/7.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.70/7.49    inference(nnf_transformation,[],[f38])).
% 54.70/7.49  
% 54.70/7.49  fof(f109,plain,(
% 54.70/7.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 54.70/7.49    inference(cnf_transformation,[],[f60])).
% 54.70/7.49  
% 54.70/7.49  fof(f115,plain,(
% 54.70/7.49    k1_xboole_0 != sK8 | ~v1_tops_1(sK7,sK6)),
% 54.70/7.49    inference(cnf_transformation,[],[f67])).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3,plain,
% 54.70/7.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 54.70/7.49      inference(cnf_transformation,[],[f122]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_0,plain,
% 54.70/7.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f119]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2161,plain,
% 54.70/7.49      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1,plain,
% 54.70/7.49      ( r1_xboole_0(X0,X1)
% 54.70/7.49      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 54.70/7.49      inference(cnf_transformation,[],[f120]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1549,plain,
% 54.70/7.49      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 54.70/7.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2826,plain,
% 54.70/7.49      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_2161,c_1549]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_46,negated_conjecture,
% 54.70/7.49      ( l1_pre_topc(sK6) ),
% 54.70/7.49      inference(cnf_transformation,[],[f111]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1507,plain,
% 54.70/7.49      ( l1_pre_topc(sK6) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_26,plain,
% 54.70/7.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 54.70/7.49      inference(cnf_transformation,[],[f96]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1527,plain,
% 54.70/7.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2632,plain,
% 54.70/7.49      ( l1_struct_0(sK6) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1507,c_1527]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_25,plain,
% 54.70/7.49      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 54.70/7.49      inference(cnf_transformation,[],[f95]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1528,plain,
% 54.70/7.49      ( k2_struct_0(X0) = u1_struct_0(X0)
% 54.70/7.49      | l1_struct_0(X0) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2727,plain,
% 54.70/7.49      ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_2632,c_1528]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_37,plain,
% 54.70/7.49      ( v3_pre_topc(k2_struct_0(X0),X0)
% 54.70/7.49      | ~ v2_pre_topc(X0)
% 54.70/7.49      | ~ l1_pre_topc(X0) ),
% 54.70/7.49      inference(cnf_transformation,[],[f107]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1516,plain,
% 54.70/7.49      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 54.70/7.49      | v2_pre_topc(X0) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3303,plain,
% 54.70/7.49      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
% 54.70/7.49      | v2_pre_topc(sK6) != iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_2727,c_1516]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_47,negated_conjecture,
% 54.70/7.49      ( v2_pre_topc(sK6) ),
% 54.70/7.49      inference(cnf_transformation,[],[f110]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_48,plain,
% 54.70/7.49      ( v2_pre_topc(sK6) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_49,plain,
% 54.70/7.49      ( l1_pre_topc(sK6) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3306,plain,
% 54.70/7.49      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_3303,c_48,c_49]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_18,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f88]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1535,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_17,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | ~ v3_pre_topc(X3,X1)
% 54.70/7.49      | ~ r2_hidden(sK2(X0,X1,X2),X3)
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 54.70/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ r1_xboole_0(X0,X3) ),
% 54.70/7.49      inference(cnf_transformation,[],[f89]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1536,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | v3_pre_topc(X3,X1) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 54.70/7.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | r1_xboole_0(X0,X3) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_8179,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 54.70/7.49      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1535,c_1536]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_525,plain,
% 54.70/7.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 54.70/7.49      theory(equality) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_517,plain,( X0 = X0 ),theory(equality) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_5758,plain,
% 54.70/7.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 54.70/7.49      inference(resolution,[status(thm)],[c_525,c_517]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_518,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4000,plain,
% 54.70/7.49      ( X0 != X1 | X1 = X0 ),
% 54.70/7.49      inference(resolution,[status(thm)],[c_518,c_517]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_5,plain,
% 54.70/7.49      ( k2_subset_1(X0) = X0 ),
% 54.70/7.49      inference(cnf_transformation,[],[f74]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4104,plain,
% 54.70/7.49      ( X0 = k2_subset_1(X0) ),
% 54.70/7.49      inference(resolution,[status(thm)],[c_4000,c_5]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_15854,plain,
% 54.70/7.49      ( m1_subset_1(X0,X1) | ~ m1_subset_1(k2_subset_1(X0),X1) ),
% 54.70/7.49      inference(resolution,[status(thm)],[c_5758,c_4104]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_7,plain,
% 54.70/7.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f76]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_16239,plain,
% 54.70/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 54.70/7.49      inference(resolution,[status(thm)],[c_15854,c_7]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_12794,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | ~ v3_pre_topc(u1_struct_0(X1),X1)
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 54.70/7.49      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
% 54.70/7.49      inference(resolution,[status(thm)],[c_17,c_18]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_16245,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | ~ v3_pre_topc(u1_struct_0(X1),X1)
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 54.70/7.49      | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
% 54.70/7.49      inference(backward_subsumption_resolution,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_16239,c_12794]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_16246,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 54.70/7.49      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_16245]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_23743,plain,
% 54.70/7.49      ( r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 54.70/7.49      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 54.70/7.49      | sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_8179,c_16246]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_23744,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 54.70/7.49      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 54.70/7.49      inference(renaming,[status(thm)],[c_23743]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_23751,plain,
% 54.70/7.49      ( sP0(X0,sK6,X1) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
% 54.70/7.49      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_3306,c_23744]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_43,negated_conjecture,
% 54.70/7.49      ( ~ v1_tops_1(sK7,sK6)
% 54.70/7.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 54.70/7.49      inference(cnf_transformation,[],[f114]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1510,plain,
% 54.70/7.49      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_8,plain,
% 54.70/7.49      ( ~ r2_hidden(X0,X1)
% 54.70/7.49      | r2_hidden(X0,X2)
% 54.70/7.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f77]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1545,plain,
% 54.70/7.49      ( r2_hidden(X0,X1) != iProver_top
% 54.70/7.49      | r2_hidden(X0,X2) = iProver_top
% 54.70/7.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3942,plain,
% 54.70/7.49      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | r2_hidden(X0,sK8) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1510,c_1545]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_13,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 54.70/7.49      | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f93]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1540,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 54.70/7.49      | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4604,plain,
% 54.70/7.49      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 54.70/7.49      | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1535,c_1540]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_16,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 54.70/7.49      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
% 54.70/7.49      inference(cnf_transformation,[],[f90]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1537,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 54.70/7.49      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_5486,plain,
% 54.70/7.49      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 54.70/7.49      | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1535,c_1537]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_44,negated_conjecture,
% 54.70/7.49      ( v1_tops_1(sK7,sK6)
% 54.70/7.49      | ~ v3_pre_topc(X0,sK6)
% 54.70/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 54.70/7.49      | ~ r1_xboole_0(sK7,X0)
% 54.70/7.49      | k1_xboole_0 = X0 ),
% 54.70/7.49      inference(cnf_transformation,[],[f113]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1509,plain,
% 54.70/7.49      ( k1_xboole_0 = X0
% 54.70/7.49      | v1_tops_1(sK7,sK6) = iProver_top
% 54.70/7.49      | v3_pre_topc(X0,sK6) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.49      | r1_xboole_0(sK7,X0) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_12521,plain,
% 54.70/7.49      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.49      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | v1_tops_1(sK7,sK6) = iProver_top
% 54.70/7.49      | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
% 54.70/7.49      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_5486,c_1509]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_15,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | v3_pre_topc(sK3(X0,X1,X2),X1)
% 54.70/7.49      | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
% 54.70/7.49      inference(cnf_transformation,[],[f91]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1538,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4574,plain,
% 54.70/7.49      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 54.70/7.49      | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1535,c_1538]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_12754,plain,
% 54.70/7.49      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.49      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | v1_tops_1(sK7,sK6) = iProver_top
% 54.70/7.49      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 54.70/7.49      inference(forward_subsumption_resolution,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_12521,c_4574]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_12758,plain,
% 54.70/7.49      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.49      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | v1_tops_1(sK7,sK6) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_4604,c_12754]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_45,negated_conjecture,
% 54.70/7.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 54.70/7.49      inference(cnf_transformation,[],[f112]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_50,plain,
% 54.70/7.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_98,plain,
% 54.70/7.49      ( l1_struct_0(sK6) | ~ l1_pre_topc(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_26]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_101,plain,
% 54.70/7.49      ( ~ l1_struct_0(sK6) | k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_25]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2049,plain,
% 54.70/7.49      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_7]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2054,plain,
% 54.70/7.49      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_2049]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2056,plain,
% 54.70/7.49      ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_2054]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_35,plain,
% 54.70/7.49      ( v1_tops_1(X0,X1)
% 54.70/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ l1_pre_topc(X1)
% 54.70/7.49      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 54.70/7.49      inference(cnf_transformation,[],[f106]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2077,plain,
% 54.70/7.49      ( v1_tops_1(sK7,sK6)
% 54.70/7.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 54.70/7.49      | ~ l1_pre_topc(sK6)
% 54.70/7.49      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_35]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2078,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 54.70/7.49      | v1_tops_1(sK7,sK6) = iProver_top
% 54.70/7.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_24,plain,
% 54.70/7.49      ( sP1(X0,X1,X2)
% 54.70/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ l1_pre_topc(X1) ),
% 54.70/7.49      inference(cnf_transformation,[],[f94]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2068,plain,
% 54.70/7.49      ( sP1(X0,sK6,sK7)
% 54.70/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 54.70/7.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 54.70/7.49      | ~ l1_pre_topc(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_24]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2328,plain,
% 54.70/7.49      ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 54.70/7.49      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 54.70/7.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 54.70/7.49      | ~ l1_pre_topc(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_2068]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2331,plain,
% 54.70/7.49      ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) = iProver_top
% 54.70/7.49      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_2328]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_11,plain,
% 54.70/7.49      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | k2_pre_topc(X1,X2) = X0 ),
% 54.70/7.49      inference(cnf_transformation,[],[f82]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2561,plain,
% 54.70/7.49      ( ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 54.70/7.49      | ~ sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_11]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2567,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = k2_subset_1(u1_struct_0(sK6))
% 54.70/7.49      | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top
% 54.70/7.49      | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6))) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_2561]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3893,plain,
% 54.70/7.49      ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_5]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2947,plain,
% 54.70/7.49      ( X0 != X1 | k2_struct_0(X2) != X1 | k2_struct_0(X2) = X0 ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_518]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4906,plain,
% 54.70/7.49      ( X0 != u1_struct_0(X1)
% 54.70/7.49      | k2_struct_0(X1) = X0
% 54.70/7.49      | k2_struct_0(X1) != u1_struct_0(X1) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_2947]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_10613,plain,
% 54.70/7.49      ( k2_struct_0(sK6) != u1_struct_0(sK6)
% 54.70/7.49      | k2_struct_0(sK6) = k2_subset_1(u1_struct_0(sK6))
% 54.70/7.49      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_4906]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_527,plain,
% 54.70/7.49      ( ~ sP0(X0,X1,X2) | sP0(X0,X1,X3) | X3 != X2 ),
% 54.70/7.49      theory(equality) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3844,plain,
% 54.70/7.49      ( ~ sP0(sK7,sK6,X0)
% 54.70/7.49      | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.49      | k2_subset_1(u1_struct_0(sK6)) != X0 ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_527]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_13542,plain,
% 54.70/7.49      ( ~ sP0(sK7,sK6,u1_struct_0(sK6))
% 54.70/7.49      | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.49      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_3844]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_13543,plain,
% 54.70/7.49      ( k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6)
% 54.70/7.49      | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6))) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_13542]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2231,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) != X0
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 54.70/7.49      | k2_struct_0(sK6) != X0 ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_518]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2935,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 54.70/7.49      | k2_pre_topc(sK6,sK7) != k2_subset_1(X0)
% 54.70/7.49      | k2_struct_0(sK6) != k2_subset_1(X0) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_2231]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_17575,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 54.70/7.49      | k2_pre_topc(sK6,sK7) != k2_subset_1(u1_struct_0(sK6))
% 54.70/7.49      | k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_2935]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_24731,plain,
% 54.70/7.49      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.49      | v1_tops_1(sK7,sK6) = iProver_top ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_12758,c_46,c_49,c_50,c_98,c_101,c_2056,c_2078,c_2331,
% 54.70/7.49                 c_2567,c_3893,c_10613,c_13543,c_17575]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1508,plain,
% 54.70/7.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_36,plain,
% 54.70/7.49      ( ~ v1_tops_1(X0,X1)
% 54.70/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ l1_pre_topc(X1)
% 54.70/7.49      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 54.70/7.49      inference(cnf_transformation,[],[f105]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1517,plain,
% 54.70/7.49      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 54.70/7.49      | v1_tops_1(X1,X0) != iProver_top
% 54.70/7.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3639,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 54.70/7.49      | v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1508,c_1517]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3650,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(light_normalisation,[status(thm)],[c_3639,c_2727]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4337,plain,
% 54.70/7.49      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_3650,c_49]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_4338,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.49      inference(renaming,[status(thm)],[c_4337]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_24743,plain,
% 54.70/7.49      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_24731,c_4338]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_14,plain,
% 54.70/7.49      ( sP0(X0,X1,X2)
% 54.70/7.49      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f92]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1539,plain,
% 54.70/7.49      ( sP0(X0,X1,X2) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_26598,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_24743,c_1539]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_5939,plain,
% 54.70/7.49      ( sP0(X0,X1,u1_struct_0(X1))
% 54.70/7.49      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_18]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_6454,plain,
% 54.70/7.49      ( sP0(sK7,sK6,u1_struct_0(sK6))
% 54.70/7.49      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_5939]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_6456,plain,
% 54.70/7.49      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_6454]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1546,plain,
% 54.70/7.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1562,plain,
% 54.70/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 54.70/7.49      inference(light_normalisation,[status(thm)],[c_1546,c_5]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1529,plain,
% 54.70/7.49      ( sP1(X0,X1,X2) = iProver_top
% 54.70/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | l1_pre_topc(X1) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_5584,plain,
% 54.70/7.49      ( sP1(u1_struct_0(X0),X0,X1) = iProver_top
% 54.70/7.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1562,c_1529]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_14660,plain,
% 54.70/7.49      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1508,c_5584]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_14988,plain,
% 54.70/7.49      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_14660,c_49]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1542,plain,
% 54.70/7.49      ( k2_pre_topc(X0,X1) = X2
% 54.70/7.49      | sP1(X2,X0,X1) != iProver_top
% 54.70/7.49      | sP0(X1,X0,X2) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_14993,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_14988,c_1542]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_27897,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_26598,c_6456,c_14993]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_9,plain,
% 54.70/7.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f78]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1544,plain,
% 54.70/7.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3941,plain,
% 54.70/7.49      ( r2_hidden(X0,X1) = iProver_top
% 54.70/7.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1544,c_1545]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_27905,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),X0) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_27897,c_3941]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_34,plain,
% 54.70/7.49      ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
% 54.70/7.49      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 54.70/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ v2_struct_0(X1)
% 54.70/7.49      | ~ l1_pre_topc(X1) ),
% 54.70/7.49      inference(cnf_transformation,[],[f99]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1519,plain,
% 54.70/7.49      ( r2_hidden(X0,k2_pre_topc(X1,X2)) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 54.70/7.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | v2_struct_0(X1) != iProver_top
% 54.70/7.49      | l1_pre_topc(X1) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_171182,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | m1_subset_1(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(X1)) != iProver_top
% 54.70/7.49      | v2_struct_0(X1) != iProver_top
% 54.70/7.49      | l1_pre_topc(X1) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_27905,c_1519]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_14994,plain,
% 54.70/7.49      ( ~ sP0(sK7,sK6,u1_struct_0(sK6))
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_14993]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_26604,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.49      | v3_pre_topc(k1_xboole_0,sK6) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_24743,c_4574]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_26740,plain,
% 54.70/7.49      ( sP0(sK7,sK6,u1_struct_0(sK6))
% 54.70/7.49      | v3_pre_topc(k1_xboole_0,sK6)
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_26604]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_33,plain,
% 54.70/7.49      ( ~ v3_pre_topc(X0,X1)
% 54.70/7.49      | ~ r2_hidden(X2,X0)
% 54.70/7.49      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 54.70/7.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 54.70/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.49      | ~ r1_xboole_0(X3,X0)
% 54.70/7.49      | ~ l1_pre_topc(X1) ),
% 54.70/7.49      inference(cnf_transformation,[],[f100]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1520,plain,
% 54.70/7.49      ( v3_pre_topc(X0,X1) != iProver_top
% 54.70/7.49      | r2_hidden(X2,X0) != iProver_top
% 54.70/7.49      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 54.70/7.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | r1_xboole_0(X3,X0) != iProver_top
% 54.70/7.49      | l1_pre_topc(X1) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_10,plain,
% 54.70/7.49      ( ~ r2_hidden(X0,X1)
% 54.70/7.49      | m1_subset_1(X0,X2)
% 54.70/7.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 54.70/7.49      inference(cnf_transformation,[],[f80]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1543,plain,
% 54.70/7.49      ( r2_hidden(X0,X1) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,X2) = iProver_top
% 54.70/7.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_1854,plain,
% 54.70/7.49      ( v3_pre_topc(X0,X1) != iProver_top
% 54.70/7.49      | r2_hidden(X2,X0) != iProver_top
% 54.70/7.49      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.49      | r1_xboole_0(X3,X0) != iProver_top
% 54.70/7.49      | l1_pre_topc(X1) != iProver_top ),
% 54.70/7.49      inference(forward_subsumption_resolution,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_1520,c_1543]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_10731,plain,
% 54.70/7.49      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 54.70/7.49      | r2_hidden(X1,k2_pre_topc(X0,X2)) != iProver_top
% 54.70/7.49      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 54.70/7.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 54.70/7.49      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1544,c_1854]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2825,plain,
% 54.70/7.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_3,c_1549]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_36250,plain,
% 54.70/7.49      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 54.70/7.49      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 54.70/7.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(forward_subsumption_resolution,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_10731,c_2825,c_3941]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_36258,plain,
% 54.70/7.49      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 54.70/7.49      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1562,c_36250]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_171235,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 54.70/7.49      | v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 54.70/7.49      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_27905,c_36258]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_171791,plain,
% 54.70/7.49      ( ~ v3_pre_topc(k1_xboole_0,X0)
% 54.70/7.49      | ~ l1_pre_topc(X0)
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_171235]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_171793,plain,
% 54.70/7.49      ( ~ v3_pre_topc(k1_xboole_0,sK6)
% 54.70/7.49      | ~ l1_pre_topc(sK6)
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_171791]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_171829,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_171182,c_46,c_14994,c_26740,c_171793]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_174342,plain,
% 54.70/7.49      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.49      | v2_struct_0(sK6) != iProver_top
% 54.70/7.49      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_171829,c_1519]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_174474,plain,
% 54.70/7.49      ( v2_struct_0(sK6) != iProver_top
% 54.70/7.49      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 54.70/7.49      inference(global_propositional_subsumption,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_174342,c_49,c_50]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_174475,plain,
% 54.70/7.49      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | v2_struct_0(sK6) != iProver_top ),
% 54.70/7.49      inference(renaming,[status(thm)],[c_174474]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_3910,plain,
% 54.70/7.49      ( r2_hidden(X0,X1) != iProver_top
% 54.70/7.49      | m1_subset_1(X0,X1) = iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_1562,c_1543]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_174483,plain,
% 54.70/7.49      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.49      | v2_struct_0(sK6) != iProver_top ),
% 54.70/7.49      inference(forward_subsumption_resolution,
% 54.70/7.49                [status(thm)],
% 54.70/7.49                [c_174475,c_3910]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_174489,plain,
% 54.70/7.49      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | r2_hidden(X0,sK8) != iProver_top
% 54.70/7.49      | v2_struct_0(sK6) != iProver_top ),
% 54.70/7.49      inference(superposition,[status(thm)],[c_3942,c_174483]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_528,plain,
% 54.70/7.49      ( ~ sP1(X0,X1,X2) | sP1(X3,X1,X2) | X3 != X0 ),
% 54.70/7.49      theory(equality) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_2562,plain,
% 54.70/7.49      ( sP1(X0,sK6,sK7)
% 54.70/7.49      | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 54.70/7.49      | X0 != k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_528]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_17561,plain,
% 54.70/7.49      ( sP1(k2_struct_0(sK6),sK6,sK7)
% 54.70/7.49      | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 54.70/7.49      | k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_2562]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_17562,plain,
% 54.70/7.49      ( k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
% 54.70/7.49      | sP1(k2_struct_0(sK6),sK6,sK7) = iProver_top
% 54.70/7.49      | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_17561]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_30400,plain,
% 54.70/7.49      ( ~ sP1(k2_struct_0(sK6),sK6,sK7)
% 54.70/7.49      | ~ sP0(sK7,sK6,k2_struct_0(sK6))
% 54.70/7.49      | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_11]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_30406,plain,
% 54.70/7.49      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 54.70/7.49      | sP1(k2_struct_0(sK6),sK6,sK7) != iProver_top
% 54.70/7.49      | sP0(sK7,sK6,k2_struct_0(sK6)) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_30400]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_6901,plain,
% 54.70/7.49      ( sP0(sK7,sK6,X0)
% 54.70/7.49      | ~ sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.49      | X0 != k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_527]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_42142,plain,
% 54.70/7.49      ( sP0(sK7,sK6,k2_struct_0(sK6))
% 54.70/7.49      | ~ sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.49      | k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.49      inference(instantiation,[status(thm)],[c_6901]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_42143,plain,
% 54.70/7.49      ( k2_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
% 54.70/7.49      | sP0(sK7,sK6,k2_struct_0(sK6)) = iProver_top
% 54.70/7.49      | sP0(sK7,sK6,k2_subset_1(u1_struct_0(sK6))) != iProver_top ),
% 54.70/7.49      inference(predicate_to_equality,[status(thm)],[c_42142]) ).
% 54.70/7.49  
% 54.70/7.49  cnf(c_10733,plain,
% 54.70/7.49      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.49      | v3_pre_topc(sK8,sK6) != iProver_top
% 54.70/7.49      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 54.70/7.49      | r2_hidden(X0,sK8) != iProver_top
% 54.70/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.50      | r1_xboole_0(X1,sK8) != iProver_top
% 54.70/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_1510,c_1854]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_41,negated_conjecture,
% 54.70/7.50      ( ~ v1_tops_1(sK7,sK6) | v3_pre_topc(sK8,sK6) ),
% 54.70/7.50      inference(cnf_transformation,[],[f116]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_56,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | v3_pre_topc(sK8,sK6) = iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_11902,plain,
% 54.70/7.50      ( r1_xboole_0(X1,sK8) != iProver_top
% 54.70/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.50      | r2_hidden(X0,sK8) != iProver_top
% 54.70/7.50      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_10733,c_49,c_56]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_11903,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 54.70/7.50      | r2_hidden(X0,sK8) != iProver_top
% 54.70/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.50      | r1_xboole_0(X1,sK8) != iProver_top ),
% 54.70/7.50      inference(renaming,[status(thm)],[c_11902]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_11916,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 54.70/7.50      | r2_hidden(X0,sK8) != iProver_top
% 54.70/7.50      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_1508,c_11903]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_40,negated_conjecture,
% 54.70/7.50      ( ~ v1_tops_1(sK7,sK6) | r1_xboole_0(sK7,sK8) ),
% 54.70/7.50      inference(cnf_transformation,[],[f117]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_57,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_12053,plain,
% 54.70/7.50      ( r2_hidden(X0,sK8) != iProver_top
% 54.70/7.50      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_11916,c_57]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_12054,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 54.70/7.50      | r2_hidden(X0,sK8) != iProver_top ),
% 54.70/7.50      inference(renaming,[status(thm)],[c_12053]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_172189,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 54.70/7.50      | r2_hidden(X0,sK8) != iProver_top ),
% 54.70/7.50      inference(demodulation,[status(thm)],[c_171829,c_12054]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_12,plain,
% 54.70/7.50      ( ~ sP1(k2_pre_topc(X0,X1),X0,X1) | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
% 54.70/7.50      inference(cnf_transformation,[],[f125]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1541,plain,
% 54.70/7.50      ( sP1(k2_pre_topc(X0,X1),X0,X1) != iProver_top
% 54.70/7.50      | sP0(X1,X0,k2_pre_topc(X0,X1)) = iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_174345,plain,
% 54.70/7.50      ( sP1(u1_struct_0(sK6),sK6,sK7) != iProver_top
% 54.70/7.50      | sP0(sK7,sK6,k2_pre_topc(sK6,sK7)) = iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_171829,c_1541]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_174359,plain,
% 54.70/7.50      ( sP1(u1_struct_0(sK6),sK6,sK7) != iProver_top
% 54.70/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top ),
% 54.70/7.50      inference(light_normalisation,[status(thm)],[c_174345,c_171829]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_95526,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6)
% 54.70/7.50      | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK6)),sK6)
% 54.70/7.50      | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.50      | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.50      inference(resolution,[status(thm)],[c_44,c_7]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2651,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6)
% 54.70/7.50      | ~ v3_pre_topc(k2_subset_1(u1_struct_0(sK6)),sK6)
% 54.70/7.50      | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.50      | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.50      inference(resolution,[status(thm)],[c_44,c_7]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_65,plain,
% 54.70/7.50      ( v3_pre_topc(k2_struct_0(sK6),sK6)
% 54.70/7.50      | ~ v2_pre_topc(sK6)
% 54.70/7.50      | ~ l1_pre_topc(sK6) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_37]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_550,plain,
% 54.70/7.50      ( sK6 = sK6 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_517]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2437,plain,
% 54.70/7.50      ( X0 != X1 | X0 = k2_struct_0(X2) | k2_struct_0(X2) != X1 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_518]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2944,plain,
% 54.70/7.50      ( X0 = k2_struct_0(X1)
% 54.70/7.50      | X0 != u1_struct_0(X1)
% 54.70/7.50      | k2_struct_0(X1) != u1_struct_0(X1) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_2437]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_4896,plain,
% 54.70/7.50      ( k2_struct_0(X0) != u1_struct_0(X0)
% 54.70/7.50      | k2_subset_1(u1_struct_0(X0)) = k2_struct_0(X0)
% 54.70/7.50      | k2_subset_1(u1_struct_0(X0)) != u1_struct_0(X0) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_2944]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_4898,plain,
% 54.70/7.50      ( k2_struct_0(sK6) != u1_struct_0(sK6)
% 54.70/7.50      | k2_subset_1(u1_struct_0(sK6)) = k2_struct_0(sK6)
% 54.70/7.50      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_4896]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_529,plain,
% 54.70/7.50      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 54.70/7.50      theory(equality) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2125,plain,
% 54.70/7.50      ( v3_pre_topc(X0,X1)
% 54.70/7.50      | ~ v3_pre_topc(k2_struct_0(X2),X2)
% 54.70/7.50      | X1 != X2
% 54.70/7.50      | X0 != k2_struct_0(X2) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_529]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_10537,plain,
% 54.70/7.50      ( ~ v3_pre_topc(k2_struct_0(X0),X0)
% 54.70/7.50      | v3_pre_topc(k2_subset_1(u1_struct_0(X0)),X1)
% 54.70/7.50      | X1 != X0
% 54.70/7.50      | k2_subset_1(u1_struct_0(X0)) != k2_struct_0(X0) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_2125]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_10539,plain,
% 54.70/7.50      ( ~ v3_pre_topc(k2_struct_0(sK6),sK6)
% 54.70/7.50      | v3_pre_topc(k2_subset_1(u1_struct_0(sK6)),sK6)
% 54.70/7.50      | k2_subset_1(u1_struct_0(sK6)) != k2_struct_0(sK6)
% 54.70/7.50      | sK6 != sK6 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_10537]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_72116,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6)
% 54.70/7.50      | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.50      | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_2651,c_47,c_46,c_65,c_98,c_101,c_550,c_3893,c_4898,
% 54.70/7.50                 c_10539]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_95658,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6)
% 54.70/7.50      | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.50      | k1_xboole_0 = k2_subset_1(u1_struct_0(sK6)) ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_95526,c_47,c_46,c_65,c_98,c_101,c_550,c_2651,c_3893,
% 54.70/7.50                 c_4898,c_10539]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_100450,plain,
% 54.70/7.50      ( m1_subset_1(X0,k2_struct_0(X1))
% 54.70/7.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 54.70/7.50      | ~ l1_struct_0(X1)
% 54.70/7.50      | X0 != X2 ),
% 54.70/7.50      inference(resolution,[status(thm)],[c_525,c_25]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_165444,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6)
% 54.70/7.50      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),u1_struct_0(X0))
% 54.70/7.50      | m1_subset_1(k1_xboole_0,k2_struct_0(X0))
% 54.70/7.50      | ~ r1_xboole_0(sK7,k2_subset_1(u1_struct_0(sK6)))
% 54.70/7.50      | ~ l1_struct_0(X0) ),
% 54.70/7.50      inference(resolution,[status(thm)],[c_95658,c_100450]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_174430,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_165444,c_46,c_49,c_45,c_50,c_98,c_101,c_2056,c_2077,
% 54.70/7.50                 c_2331,c_3893,c_10613,c_13543,c_14660,c_17562,c_30406,
% 54.70/7.50                 c_42143,c_174359]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_174441,plain,
% 54.70/7.50      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 54.70/7.50      inference(backward_subsumption_resolution,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_174430,c_43]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_174540,plain,
% 54.70/7.50      ( r2_hidden(X0,u1_struct_0(sK6)) | ~ r2_hidden(X0,sK8) ),
% 54.70/7.50      inference(resolution,[status(thm)],[c_174441,c_8]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_174545,plain,
% 54.70/7.50      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 54.70/7.50      | r2_hidden(X0,sK8) != iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_174540]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_175217,plain,
% 54.70/7.50      ( r2_hidden(X0,sK8) != iProver_top ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_174489,c_46,c_49,c_50,c_98,c_101,c_2056,c_2078,c_2331,
% 54.70/7.50                 c_3893,c_10613,c_13543,c_14660,c_17562,c_30406,c_42143,
% 54.70/7.50                 c_172189,c_174359,c_174545]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_175225,plain,
% 54.70/7.50      ( sP0(X0,sK6,sK8) = iProver_top
% 54.70/7.50      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_23751,c_175217]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_179538,plain,
% 54.70/7.50      ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_2826,c_175225]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_95699,plain,
% 54.70/7.50      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_518]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_96283,plain,
% 54.70/7.50      ( X0 != k1_xboole_0
% 54.70/7.50      | k1_xboole_0 = X0
% 54.70/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_95699]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_146237,plain,
% 54.70/7.50      ( sK8 != k1_xboole_0
% 54.70/7.50      | k1_xboole_0 = sK8
% 54.70/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_96283]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1513,plain,
% 54.70/7.50      ( v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_24745,plain,
% 54.70/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.50      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_24731,c_1513]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2,plain,
% 54.70/7.50      ( ~ r1_xboole_0(X0,X1)
% 54.70/7.50      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 54.70/7.50      inference(cnf_transformation,[],[f121]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1548,plain,
% 54.70/7.50      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 54.70/7.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_24836,plain,
% 54.70/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_24745,c_1548]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_28,plain,
% 54.70/7.50      ( ~ v4_pre_topc(X0,X1)
% 54.70/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.50      | ~ l1_pre_topc(X1)
% 54.70/7.50      | k2_pre_topc(X1,X0) = X0 ),
% 54.70/7.50      inference(cnf_transformation,[],[f97]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1525,plain,
% 54.70/7.50      ( k2_pre_topc(X0,X1) = X1
% 54.70/7.50      | v4_pre_topc(X1,X0) != iProver_top
% 54.70/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 54.70/7.50      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_12515,plain,
% 54.70/7.50      ( k2_pre_topc(X0,sK3(X1,X0,u1_struct_0(X0))) = sK3(X1,X0,u1_struct_0(X0))
% 54.70/7.50      | sP0(X1,X0,u1_struct_0(X0)) = iProver_top
% 54.70/7.50      | v4_pre_topc(sK3(X1,X0,u1_struct_0(X0)),X0) != iProver_top
% 54.70/7.50      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_5486,c_1525]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_25267,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK3(sK7,sK6,u1_struct_0(sK6))
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 54.70/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.50      | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
% 54.70/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_24836,c_12515]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2059,plain,
% 54.70/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_9]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2064,plain,
% 54.70/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_2059]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2066,plain,
% 54.70/7.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_2064]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_6,plain,
% 54.70/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.70/7.50      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 54.70/7.50      inference(cnf_transformation,[],[f124]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1547,plain,
% 54.70/7.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 54.70/7.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_3614,plain,
% 54.70/7.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_1544,c_1547]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_4,plain,
% 54.70/7.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 54.70/7.50      inference(cnf_transformation,[],[f123]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1565,plain,
% 54.70/7.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 54.70/7.50      inference(light_normalisation,[status(thm)],[c_4,c_3]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_3627,plain,
% 54.70/7.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 54.70/7.50      inference(light_normalisation,[status(thm)],[c_3614,c_3,c_1565]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_38,plain,
% 54.70/7.50      ( v4_pre_topc(X0,X1)
% 54.70/7.50      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 54.70/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.70/7.50      | ~ l1_pre_topc(X1) ),
% 54.70/7.50      inference(cnf_transformation,[],[f109]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_1515,plain,
% 54.70/7.50      ( v4_pre_topc(X0,X1) = iProver_top
% 54.70/7.50      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 54.70/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 54.70/7.50      | l1_pre_topc(X1) != iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_3759,plain,
% 54.70/7.50      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 54.70/7.50      | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 54.70/7.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 54.70/7.50      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_3627,c_1515]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_3778,plain,
% 54.70/7.50      ( v4_pre_topc(k1_xboole_0,sK6) = iProver_top
% 54.70/7.50      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 54.70/7.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_3759]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_5582,plain,
% 54.70/7.50      ( sP1(sK8,sK6,X0) = iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_1510,c_1529]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_6216,plain,
% 54.70/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | sP1(sK8,sK6,X0) = iProver_top ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_5582,c_49]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_6217,plain,
% 54.70/7.50      ( sP1(sK8,sK6,X0) = iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top
% 54.70/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 54.70/7.50      inference(renaming,[status(thm)],[c_6216]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_12519,plain,
% 54.70/7.50      ( sP1(sK8,sK6,sK3(X0,sK6,u1_struct_0(sK6))) = iProver_top
% 54.70/7.50      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_5486,c_6217]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_14122,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,sK3(X0,sK6,u1_struct_0(sK6))) = sK8
% 54.70/7.50      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.50      | sP0(sK3(X0,sK6,u1_struct_0(sK6)),sK6,sK8) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_12519,c_1542]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_25258,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK8
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 54.70/7.50      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 54.70/7.50      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_24836,c_14122]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_30439,plain,
% 54.70/7.50      ( ~ r1_xboole_0(sK7,sK8)
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_2]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_30440,plain,
% 54.70/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 54.70/7.50      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 54.70/7.50      inference(predicate_to_equality,[status(thm)],[c_30439]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_47448,plain,
% 54.70/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_25258,c_57,c_30440]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_49004,plain,
% 54.70/7.50      ( k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0
% 54.70/7.50      | k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK3(sK7,sK6,u1_struct_0(sK6)) ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_25267,c_47,c_46,c_49,c_45,c_50,c_98,c_101,c_2055,
% 54.70/7.50                 c_2065,c_2078,c_2328,c_3304,c_3779,c_3893,c_10613,
% 54.70/7.50                 c_13542,c_17561,c_25408,c_30400,c_42142,c_47448]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_49005,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = sK3(sK7,sK6,u1_struct_0(sK6))
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 54.70/7.50      inference(renaming,[status(thm)],[c_49004]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_49009,plain,
% 54.70/7.50      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k2_pre_topc(sK6,k1_xboole_0)
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_24836,c_49005]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_49645,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 54.70/7.50      | k1_setfam_1(k2_tarski(sK7,sK8)) = k1_xboole_0 ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_49009,c_24836]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_4797,plain,
% 54.70/7.50      ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
% 54.70/7.50      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 54.70/7.50      | l1_pre_topc(X0) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_1544,c_1525]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_4828,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 54.70/7.50      | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
% 54.70/7.50      | l1_pre_topc(sK6) != iProver_top ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_4797]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_49976,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 54.70/7.50      inference(global_propositional_subsumption,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_49645,c_48,c_49,c_2066,c_3303,c_3778,c_4828]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_6225,plain,
% 54.70/7.50      ( sP1(sK8,sK6,k1_xboole_0) = iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_1544,c_6217]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_7203,plain,
% 54.70/7.50      ( k2_pre_topc(sK6,k1_xboole_0) = sK8
% 54.70/7.50      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(superposition,[status(thm)],[c_6225,c_1542]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_49982,plain,
% 54.70/7.50      ( sK8 = k1_xboole_0
% 54.70/7.50      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 54.70/7.50      | v1_tops_1(sK7,sK6) != iProver_top ),
% 54.70/7.50      inference(demodulation,[status(thm)],[c_49976,c_7203]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_2371,plain,
% 54.70/7.50      ( k1_xboole_0 = k1_xboole_0 ),
% 54.70/7.50      inference(instantiation,[status(thm)],[c_517]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(c_42,negated_conjecture,
% 54.70/7.50      ( ~ v1_tops_1(sK7,sK6) | k1_xboole_0 != sK8 ),
% 54.70/7.50      inference(cnf_transformation,[],[f115]) ).
% 54.70/7.50  
% 54.70/7.50  cnf(contradiction,plain,
% 54.70/7.50      ( $false ),
% 54.70/7.50      inference(minisat,
% 54.70/7.50                [status(thm)],
% 54.70/7.50                [c_179538,c_174359,c_146237,c_49982,c_42143,c_30406,
% 54.70/7.50                 c_17562,c_14660,c_13543,c_10613,c_3893,c_2371,c_2331,
% 54.70/7.50                 c_2078,c_2077,c_2056,c_101,c_98,c_42,c_50,c_45,c_49,
% 54.70/7.50                 c_46]) ).
% 54.70/7.50  
% 54.70/7.50  
% 54.70/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 54.70/7.50  
% 54.70/7.50  ------                               Statistics
% 54.70/7.50  
% 54.70/7.50  ------ Selected
% 54.70/7.50  
% 54.70/7.50  total_time:                             6.741
% 54.70/7.50  
%------------------------------------------------------------------------------
