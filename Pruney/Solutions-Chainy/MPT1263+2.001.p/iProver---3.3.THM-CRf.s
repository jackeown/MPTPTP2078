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
% DateTime   : Thu Dec  3 12:14:51 EST 2020

% Result     : Theorem 15.84s
% Output     : CNFRefutation 15.84s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1469)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f119,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f69,f74,f74])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f72,f74])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f108,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f68,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f64,f67,f66,f65])).

fof(f111,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f97,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f96,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f50,f53,f52,f51])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ! [X2,X0,X5,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_xboole_0(X0,X5)
      | ~ r2_hidden(sK2(X0,X1,X2),X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f115,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_xboole_0(X0,sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f114,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK7,X3)
      | ~ v3_pre_topc(X3,sK6)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | v1_tops_1(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f113,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f68])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X1,X2) = X0
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f29,f43,f42])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f55])).

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
    inference(rectify,[],[f56])).

fof(f58,plain,(
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

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f118,plain,
    ( r1_xboole_0(sK7,sK8)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f116,plain,
    ( k1_xboole_0 != sK8
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_8994,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_8521,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_9652,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8994,c_8521])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_8504,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10152,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9652,c_8504])).

cnf(c_38,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_629,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_48])).

cnf(c_630,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_66,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_632,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_48,c_47,c_66])).

cnf(c_8479,plain,
    ( v3_pre_topc(k2_struct_0(sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_27,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_615,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_27,c_26])).

cnf(c_920,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_615,c_47])).

cnf(c_921,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_8511,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8479,c_921])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8491,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X3)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_8492,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14472,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8491,c_8492])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8501,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8518,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8501,c_5])).

cnf(c_70054,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14472,c_8518])).

cnf(c_70058,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8511,c_70054])).

cnf(c_44,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_8482,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_8499,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11925,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8482,c_8499])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_8496,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12526,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8491,c_8496])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8493,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13155,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8491,c_8493])).

cnf(c_45,negated_conjecture,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(sK7,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_8481,plain,
    ( k1_xboole_0 = X0
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_46504,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13155,c_8481])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | v3_pre_topc(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_8494,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12496,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8491,c_8494])).

cnf(c_48879,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_46504,c_12496])).

cnf(c_48883,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12526,c_48879])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_51,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_99,plain,
    ( l1_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_102,plain,
    ( ~ l1_struct_0(sK6)
    | k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_961,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_47])).

cnf(c_962,plain,
    ( v1_tops_1(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) != k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_8861,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_8862,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8861])).

cnf(c_7568,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8997,plain,
    ( k2_pre_topc(sK6,sK7) != X0
    | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_7568])).

cnf(c_9230,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_8997])).

cnf(c_8480,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_12,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k2_pre_topc(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1086,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_47])).

cnf(c_1087,plain,
    ( sP1(X0,sK6,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_1086])).

cnf(c_1154,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
    | X3 != X2
    | X4 != X0
    | k2_pre_topc(X1,X0) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_1087])).

cnf(c_1155,plain,
    ( ~ sP0(X0,sK6,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1154])).

cnf(c_8468,plain,
    ( k2_pre_topc(sK6,X0) = X1
    | sP0(X0,sK6,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_9409,plain,
    ( k2_pre_topc(sK6,sK7) = X0
    | sP0(sK7,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8480,c_8468])).

cnf(c_9752,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8518,c_9409])).

cnf(c_54144,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48883,c_47,c_51,c_99,c_102,c_8862,c_9230,c_9752])).

cnf(c_37,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_946,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_47])).

cnf(c_947,plain,
    ( ~ v1_tops_1(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) = k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_8475,plain,
    ( k2_pre_topc(sK6,X0) = k2_struct_0(sK6)
    | v1_tops_1(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_8581,plain,
    ( k2_pre_topc(sK6,X0) = u1_struct_0(sK6)
    | v1_tops_1(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8475,c_921])).

cnf(c_9170,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8480,c_8581])).

cnf(c_54163,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_54144,c_9170])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_8495,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_55101,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_54163,c_8495])).

cnf(c_9056,plain,
    ( sP0(sK7,sK6,X0)
    | r2_hidden(sK2(sK7,sK6,X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_17349,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6))
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_9056])).

cnf(c_17352,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17349])).

cnf(c_62271,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55101,c_9752,c_17352])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8498,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8502,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10780,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8498,c_8502])).

cnf(c_10805,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10780,c_4])).

cnf(c_39,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_29,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_715,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_39,c_29])).

cnf(c_905,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_715,c_47])).

cnf(c_906,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_8477,plain,
    ( k2_pre_topc(sK6,X0) = X0
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_10814,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10805,c_8477])).

cnf(c_8892,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8898,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8892])).

cnf(c_11618,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10814,c_8511,c_8898])).

cnf(c_34,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_994,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_47])).

cnf(c_995,plain,
    ( ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(X2,X0) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1013,plain,
    ( ~ v3_pre_topc(X0,sK6)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_995,c_11])).

cnf(c_8472,plain,
    ( v3_pre_topc(X0,sK6) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK6,X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_10635,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8518,c_8472])).

cnf(c_32414,plain,
    ( r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10635,c_8511])).

cnf(c_32437,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11618,c_32414])).

cnf(c_53770,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32437,c_8898])).

cnf(c_53771,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_53770])).

cnf(c_11924,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8498,c_8499])).

cnf(c_53779,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_53771,c_10152,c_11924])).

cnf(c_62277,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_62271,c_53779])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_976,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_47])).

cnf(c_977,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK6,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_8473,plain,
    ( r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_62795,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_62277,c_8473])).

cnf(c_67846,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62795,c_51])).

cnf(c_67847,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_67846])).

cnf(c_8497,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_11818,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8518,c_8497])).

cnf(c_67855,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67847,c_11818])).

cnf(c_67861,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11925,c_67855])).

cnf(c_41,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | r1_xboole_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_xboole_0(sK7,sK8)
    | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
    | sK6 != sK6
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_962])).

cnf(c_1468,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_xboole_0(sK7,sK8)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1467])).

cnf(c_1470,plain,
    ( r1_xboole_0(sK7,sK8)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_46])).

cnf(c_1472,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_8474,plain,
    ( k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
    | v1_tops_1(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_8574,plain,
    ( k2_pre_topc(sK6,X0) != u1_struct_0(sK6)
    | v1_tops_1(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8474,c_921])).

cnf(c_62783,plain,
    ( v1_tops_1(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_62277,c_8574])).

cnf(c_10632,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8482,c_8472])).

cnf(c_55,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_42,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | v3_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2753,plain,
    ( ~ v1_tops_1(sK7,sK6)
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_pre_topc(sK6,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(X2,X1)
    | sK6 != sK6
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1013])).

cnf(c_2754,plain,
    ( ~ v1_tops_1(sK7,sK6)
    | ~ r2_hidden(X0,k2_pre_topc(sK6,X1))
    | ~ r2_hidden(X0,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(X1,sK8) ),
    inference(unflattening,[status(thm)],[c_2753])).

cnf(c_2755,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2754])).

cnf(c_11381,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10632,c_55,c_2755])).

cnf(c_62793,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_62277,c_11381])).

cnf(c_62950,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_62783,c_62793])).

cnf(c_68327,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_67861,c_47,c_51,c_99,c_102,c_1469,c_8862,c_9230,c_11925,c_62277,c_62950])).

cnf(c_70842,plain,
    ( sP0(X0,sK6,sK8) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70058,c_68327])).

cnf(c_71513,plain,
    ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_10152,c_70842])).

cnf(c_9501,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = X0
    | sP0(k1_xboole_0,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8498,c_8468])).

cnf(c_17765,plain,
    ( k1_xboole_0 = X0
    | sP0(k1_xboole_0,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9501,c_11618])).

cnf(c_17773,plain,
    ( sK8 = k1_xboole_0
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8482,c_17765])).

cnf(c_43,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
    | sK6 != sK6
    | sK8 != k1_xboole_0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_962])).

cnf(c_1443,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | sK8 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1442])).

cnf(c_1445,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | sK8 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1443,c_46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71513,c_62277,c_17773,c_9230,c_8862,c_1445,c_102,c_99,c_51,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.84/2.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.84/2.52  
% 15.84/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.84/2.52  
% 15.84/2.52  ------  iProver source info
% 15.84/2.52  
% 15.84/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.84/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.84/2.52  git: non_committed_changes: false
% 15.84/2.52  git: last_make_outside_of_git: false
% 15.84/2.52  
% 15.84/2.52  ------ 
% 15.84/2.52  
% 15.84/2.52  ------ Input Options
% 15.84/2.52  
% 15.84/2.52  --out_options                           all
% 15.84/2.52  --tptp_safe_out                         true
% 15.84/2.52  --problem_path                          ""
% 15.84/2.52  --include_path                          ""
% 15.84/2.52  --clausifier                            res/vclausify_rel
% 15.84/2.52  --clausifier_options                    --mode clausify
% 15.84/2.52  --stdin                                 false
% 15.84/2.52  --stats_out                             all
% 15.84/2.52  
% 15.84/2.52  ------ General Options
% 15.84/2.52  
% 15.84/2.52  --fof                                   false
% 15.84/2.52  --time_out_real                         305.
% 15.84/2.52  --time_out_virtual                      -1.
% 15.84/2.52  --symbol_type_check                     false
% 15.84/2.52  --clausify_out                          false
% 15.84/2.52  --sig_cnt_out                           false
% 15.84/2.52  --trig_cnt_out                          false
% 15.84/2.52  --trig_cnt_out_tolerance                1.
% 15.84/2.52  --trig_cnt_out_sk_spl                   false
% 15.84/2.52  --abstr_cl_out                          false
% 15.84/2.52  
% 15.84/2.52  ------ Global Options
% 15.84/2.52  
% 15.84/2.52  --schedule                              default
% 15.84/2.52  --add_important_lit                     false
% 15.84/2.52  --prop_solver_per_cl                    1000
% 15.84/2.52  --min_unsat_core                        false
% 15.84/2.52  --soft_assumptions                      false
% 15.84/2.52  --soft_lemma_size                       3
% 15.84/2.52  --prop_impl_unit_size                   0
% 15.84/2.52  --prop_impl_unit                        []
% 15.84/2.52  --share_sel_clauses                     true
% 15.84/2.52  --reset_solvers                         false
% 15.84/2.52  --bc_imp_inh                            [conj_cone]
% 15.84/2.52  --conj_cone_tolerance                   3.
% 15.84/2.52  --extra_neg_conj                        none
% 15.84/2.52  --large_theory_mode                     true
% 15.84/2.52  --prolific_symb_bound                   200
% 15.84/2.52  --lt_threshold                          2000
% 15.84/2.52  --clause_weak_htbl                      true
% 15.84/2.52  --gc_record_bc_elim                     false
% 15.84/2.52  
% 15.84/2.52  ------ Preprocessing Options
% 15.84/2.52  
% 15.84/2.52  --preprocessing_flag                    true
% 15.84/2.52  --time_out_prep_mult                    0.1
% 15.84/2.52  --splitting_mode                        input
% 15.84/2.52  --splitting_grd                         true
% 15.84/2.52  --splitting_cvd                         false
% 15.84/2.52  --splitting_cvd_svl                     false
% 15.84/2.52  --splitting_nvd                         32
% 15.84/2.52  --sub_typing                            true
% 15.84/2.52  --prep_gs_sim                           true
% 15.84/2.52  --prep_unflatten                        true
% 15.84/2.52  --prep_res_sim                          true
% 15.84/2.52  --prep_upred                            true
% 15.84/2.52  --prep_sem_filter                       exhaustive
% 15.84/2.52  --prep_sem_filter_out                   false
% 15.84/2.52  --pred_elim                             true
% 15.84/2.52  --res_sim_input                         true
% 15.84/2.52  --eq_ax_congr_red                       true
% 15.84/2.52  --pure_diseq_elim                       true
% 15.84/2.52  --brand_transform                       false
% 15.84/2.52  --non_eq_to_eq                          false
% 15.84/2.52  --prep_def_merge                        true
% 15.84/2.52  --prep_def_merge_prop_impl              false
% 15.84/2.52  --prep_def_merge_mbd                    true
% 15.84/2.52  --prep_def_merge_tr_red                 false
% 15.84/2.52  --prep_def_merge_tr_cl                  false
% 15.84/2.52  --smt_preprocessing                     true
% 15.84/2.52  --smt_ac_axioms                         fast
% 15.84/2.52  --preprocessed_out                      false
% 15.84/2.52  --preprocessed_stats                    false
% 15.84/2.52  
% 15.84/2.52  ------ Abstraction refinement Options
% 15.84/2.52  
% 15.84/2.52  --abstr_ref                             []
% 15.84/2.52  --abstr_ref_prep                        false
% 15.84/2.52  --abstr_ref_until_sat                   false
% 15.84/2.52  --abstr_ref_sig_restrict                funpre
% 15.84/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.84/2.52  --abstr_ref_under                       []
% 15.84/2.52  
% 15.84/2.52  ------ SAT Options
% 15.84/2.52  
% 15.84/2.52  --sat_mode                              false
% 15.84/2.52  --sat_fm_restart_options                ""
% 15.84/2.52  --sat_gr_def                            false
% 15.84/2.52  --sat_epr_types                         true
% 15.84/2.52  --sat_non_cyclic_types                  false
% 15.84/2.52  --sat_finite_models                     false
% 15.84/2.52  --sat_fm_lemmas                         false
% 15.84/2.52  --sat_fm_prep                           false
% 15.84/2.52  --sat_fm_uc_incr                        true
% 15.84/2.52  --sat_out_model                         small
% 15.84/2.52  --sat_out_clauses                       false
% 15.84/2.52  
% 15.84/2.52  ------ QBF Options
% 15.84/2.52  
% 15.84/2.52  --qbf_mode                              false
% 15.84/2.52  --qbf_elim_univ                         false
% 15.84/2.52  --qbf_dom_inst                          none
% 15.84/2.52  --qbf_dom_pre_inst                      false
% 15.84/2.52  --qbf_sk_in                             false
% 15.84/2.52  --qbf_pred_elim                         true
% 15.84/2.52  --qbf_split                             512
% 15.84/2.52  
% 15.84/2.52  ------ BMC1 Options
% 15.84/2.52  
% 15.84/2.52  --bmc1_incremental                      false
% 15.84/2.52  --bmc1_axioms                           reachable_all
% 15.84/2.52  --bmc1_min_bound                        0
% 15.84/2.52  --bmc1_max_bound                        -1
% 15.84/2.52  --bmc1_max_bound_default                -1
% 15.84/2.52  --bmc1_symbol_reachability              true
% 15.84/2.52  --bmc1_property_lemmas                  false
% 15.84/2.52  --bmc1_k_induction                      false
% 15.84/2.52  --bmc1_non_equiv_states                 false
% 15.84/2.52  --bmc1_deadlock                         false
% 15.84/2.52  --bmc1_ucm                              false
% 15.84/2.52  --bmc1_add_unsat_core                   none
% 15.84/2.52  --bmc1_unsat_core_children              false
% 15.84/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.84/2.52  --bmc1_out_stat                         full
% 15.84/2.52  --bmc1_ground_init                      false
% 15.84/2.52  --bmc1_pre_inst_next_state              false
% 15.84/2.52  --bmc1_pre_inst_state                   false
% 15.84/2.52  --bmc1_pre_inst_reach_state             false
% 15.84/2.52  --bmc1_out_unsat_core                   false
% 15.84/2.52  --bmc1_aig_witness_out                  false
% 15.84/2.52  --bmc1_verbose                          false
% 15.84/2.52  --bmc1_dump_clauses_tptp                false
% 15.84/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.84/2.52  --bmc1_dump_file                        -
% 15.84/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.84/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.84/2.52  --bmc1_ucm_extend_mode                  1
% 15.84/2.52  --bmc1_ucm_init_mode                    2
% 15.84/2.52  --bmc1_ucm_cone_mode                    none
% 15.84/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.84/2.52  --bmc1_ucm_relax_model                  4
% 15.84/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.84/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.84/2.52  --bmc1_ucm_layered_model                none
% 15.84/2.52  --bmc1_ucm_max_lemma_size               10
% 15.84/2.52  
% 15.84/2.52  ------ AIG Options
% 15.84/2.52  
% 15.84/2.52  --aig_mode                              false
% 15.84/2.52  
% 15.84/2.52  ------ Instantiation Options
% 15.84/2.52  
% 15.84/2.52  --instantiation_flag                    true
% 15.84/2.52  --inst_sos_flag                         false
% 15.84/2.52  --inst_sos_phase                        true
% 15.84/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.84/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.84/2.52  --inst_lit_sel_side                     num_symb
% 15.84/2.52  --inst_solver_per_active                1400
% 15.84/2.52  --inst_solver_calls_frac                1.
% 15.84/2.52  --inst_passive_queue_type               priority_queues
% 15.84/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.84/2.52  --inst_passive_queues_freq              [25;2]
% 15.84/2.52  --inst_dismatching                      true
% 15.84/2.52  --inst_eager_unprocessed_to_passive     true
% 15.84/2.52  --inst_prop_sim_given                   true
% 15.84/2.52  --inst_prop_sim_new                     false
% 15.84/2.52  --inst_subs_new                         false
% 15.84/2.52  --inst_eq_res_simp                      false
% 15.84/2.52  --inst_subs_given                       false
% 15.84/2.52  --inst_orphan_elimination               true
% 15.84/2.52  --inst_learning_loop_flag               true
% 15.84/2.52  --inst_learning_start                   3000
% 15.84/2.52  --inst_learning_factor                  2
% 15.84/2.52  --inst_start_prop_sim_after_learn       3
% 15.84/2.52  --inst_sel_renew                        solver
% 15.84/2.52  --inst_lit_activity_flag                true
% 15.84/2.52  --inst_restr_to_given                   false
% 15.84/2.52  --inst_activity_threshold               500
% 15.84/2.52  --inst_out_proof                        true
% 15.84/2.52  
% 15.84/2.52  ------ Resolution Options
% 15.84/2.52  
% 15.84/2.52  --resolution_flag                       true
% 15.84/2.52  --res_lit_sel                           adaptive
% 15.84/2.52  --res_lit_sel_side                      none
% 15.84/2.52  --res_ordering                          kbo
% 15.84/2.52  --res_to_prop_solver                    active
% 15.84/2.52  --res_prop_simpl_new                    false
% 15.84/2.52  --res_prop_simpl_given                  true
% 15.84/2.52  --res_passive_queue_type                priority_queues
% 15.84/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.84/2.52  --res_passive_queues_freq               [15;5]
% 15.84/2.52  --res_forward_subs                      full
% 15.84/2.52  --res_backward_subs                     full
% 15.84/2.52  --res_forward_subs_resolution           true
% 15.84/2.52  --res_backward_subs_resolution          true
% 15.84/2.52  --res_orphan_elimination                true
% 15.84/2.52  --res_time_limit                        2.
% 15.84/2.52  --res_out_proof                         true
% 15.84/2.52  
% 15.84/2.52  ------ Superposition Options
% 15.84/2.52  
% 15.84/2.52  --superposition_flag                    true
% 15.84/2.52  --sup_passive_queue_type                priority_queues
% 15.84/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.84/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.84/2.52  --demod_completeness_check              fast
% 15.84/2.52  --demod_use_ground                      true
% 15.84/2.52  --sup_to_prop_solver                    passive
% 15.84/2.52  --sup_prop_simpl_new                    true
% 15.84/2.52  --sup_prop_simpl_given                  true
% 15.84/2.52  --sup_fun_splitting                     false
% 15.84/2.52  --sup_smt_interval                      50000
% 15.84/2.52  
% 15.84/2.52  ------ Superposition Simplification Setup
% 15.84/2.52  
% 15.84/2.52  --sup_indices_passive                   []
% 15.84/2.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.84/2.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.84/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.84/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.84/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.84/2.52  --sup_full_bw                           [BwDemod]
% 15.84/2.52  --sup_immed_triv                        [TrivRules]
% 15.84/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.84/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.84/2.52  --sup_immed_bw_main                     []
% 15.84/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.84/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.84/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.84/2.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.84/2.52  
% 15.84/2.52  ------ Combination Options
% 15.84/2.52  
% 15.84/2.52  --comb_res_mult                         3
% 15.84/2.52  --comb_sup_mult                         2
% 15.84/2.52  --comb_inst_mult                        10
% 15.84/2.52  
% 15.84/2.52  ------ Debug Options
% 15.84/2.52  
% 15.84/2.52  --dbg_backtrace                         false
% 15.84/2.52  --dbg_dump_prop_clauses                 false
% 15.84/2.52  --dbg_dump_prop_clauses_file            -
% 15.84/2.52  --dbg_out_stat                          false
% 15.84/2.52  ------ Parsing...
% 15.84/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.84/2.52  
% 15.84/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.84/2.52  
% 15.84/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.84/2.52  
% 15.84/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.84/2.52  ------ Proving...
% 15.84/2.52  ------ Problem Properties 
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  clauses                                 43
% 15.84/2.52  conjectures                             6
% 15.84/2.52  EPR                                     3
% 15.84/2.52  Horn                                    28
% 15.84/2.52  unary                                   9
% 15.84/2.52  binary                                  9
% 15.84/2.52  lits                                    128
% 15.84/2.52  lits eq                                 16
% 15.84/2.52  fd_pure                                 0
% 15.84/2.52  fd_pseudo                               0
% 15.84/2.52  fd_cond                                 1
% 15.84/2.52  fd_pseudo_cond                          1
% 15.84/2.52  AC symbols                              0
% 15.84/2.52  
% 15.84/2.52  ------ Schedule dynamic 5 is on 
% 15.84/2.52  
% 15.84/2.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  ------ 
% 15.84/2.52  Current options:
% 15.84/2.52  ------ 
% 15.84/2.52  
% 15.84/2.52  ------ Input Options
% 15.84/2.52  
% 15.84/2.52  --out_options                           all
% 15.84/2.52  --tptp_safe_out                         true
% 15.84/2.52  --problem_path                          ""
% 15.84/2.52  --include_path                          ""
% 15.84/2.52  --clausifier                            res/vclausify_rel
% 15.84/2.52  --clausifier_options                    --mode clausify
% 15.84/2.52  --stdin                                 false
% 15.84/2.52  --stats_out                             all
% 15.84/2.52  
% 15.84/2.52  ------ General Options
% 15.84/2.52  
% 15.84/2.52  --fof                                   false
% 15.84/2.52  --time_out_real                         305.
% 15.84/2.52  --time_out_virtual                      -1.
% 15.84/2.52  --symbol_type_check                     false
% 15.84/2.52  --clausify_out                          false
% 15.84/2.52  --sig_cnt_out                           false
% 15.84/2.52  --trig_cnt_out                          false
% 15.84/2.52  --trig_cnt_out_tolerance                1.
% 15.84/2.52  --trig_cnt_out_sk_spl                   false
% 15.84/2.52  --abstr_cl_out                          false
% 15.84/2.52  
% 15.84/2.52  ------ Global Options
% 15.84/2.52  
% 15.84/2.52  --schedule                              default
% 15.84/2.52  --add_important_lit                     false
% 15.84/2.52  --prop_solver_per_cl                    1000
% 15.84/2.52  --min_unsat_core                        false
% 15.84/2.52  --soft_assumptions                      false
% 15.84/2.52  --soft_lemma_size                       3
% 15.84/2.52  --prop_impl_unit_size                   0
% 15.84/2.52  --prop_impl_unit                        []
% 15.84/2.52  --share_sel_clauses                     true
% 15.84/2.52  --reset_solvers                         false
% 15.84/2.52  --bc_imp_inh                            [conj_cone]
% 15.84/2.52  --conj_cone_tolerance                   3.
% 15.84/2.52  --extra_neg_conj                        none
% 15.84/2.52  --large_theory_mode                     true
% 15.84/2.52  --prolific_symb_bound                   200
% 15.84/2.52  --lt_threshold                          2000
% 15.84/2.52  --clause_weak_htbl                      true
% 15.84/2.52  --gc_record_bc_elim                     false
% 15.84/2.52  
% 15.84/2.52  ------ Preprocessing Options
% 15.84/2.52  
% 15.84/2.52  --preprocessing_flag                    true
% 15.84/2.52  --time_out_prep_mult                    0.1
% 15.84/2.52  --splitting_mode                        input
% 15.84/2.52  --splitting_grd                         true
% 15.84/2.52  --splitting_cvd                         false
% 15.84/2.52  --splitting_cvd_svl                     false
% 15.84/2.52  --splitting_nvd                         32
% 15.84/2.52  --sub_typing                            true
% 15.84/2.52  --prep_gs_sim                           true
% 15.84/2.52  --prep_unflatten                        true
% 15.84/2.52  --prep_res_sim                          true
% 15.84/2.52  --prep_upred                            true
% 15.84/2.52  --prep_sem_filter                       exhaustive
% 15.84/2.52  --prep_sem_filter_out                   false
% 15.84/2.52  --pred_elim                             true
% 15.84/2.52  --res_sim_input                         true
% 15.84/2.52  --eq_ax_congr_red                       true
% 15.84/2.52  --pure_diseq_elim                       true
% 15.84/2.52  --brand_transform                       false
% 15.84/2.52  --non_eq_to_eq                          false
% 15.84/2.52  --prep_def_merge                        true
% 15.84/2.52  --prep_def_merge_prop_impl              false
% 15.84/2.52  --prep_def_merge_mbd                    true
% 15.84/2.52  --prep_def_merge_tr_red                 false
% 15.84/2.52  --prep_def_merge_tr_cl                  false
% 15.84/2.52  --smt_preprocessing                     true
% 15.84/2.52  --smt_ac_axioms                         fast
% 15.84/2.52  --preprocessed_out                      false
% 15.84/2.52  --preprocessed_stats                    false
% 15.84/2.52  
% 15.84/2.52  ------ Abstraction refinement Options
% 15.84/2.52  
% 15.84/2.52  --abstr_ref                             []
% 15.84/2.52  --abstr_ref_prep                        false
% 15.84/2.52  --abstr_ref_until_sat                   false
% 15.84/2.52  --abstr_ref_sig_restrict                funpre
% 15.84/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.84/2.52  --abstr_ref_under                       []
% 15.84/2.52  
% 15.84/2.52  ------ SAT Options
% 15.84/2.52  
% 15.84/2.52  --sat_mode                              false
% 15.84/2.52  --sat_fm_restart_options                ""
% 15.84/2.52  --sat_gr_def                            false
% 15.84/2.52  --sat_epr_types                         true
% 15.84/2.52  --sat_non_cyclic_types                  false
% 15.84/2.52  --sat_finite_models                     false
% 15.84/2.52  --sat_fm_lemmas                         false
% 15.84/2.52  --sat_fm_prep                           false
% 15.84/2.52  --sat_fm_uc_incr                        true
% 15.84/2.52  --sat_out_model                         small
% 15.84/2.52  --sat_out_clauses                       false
% 15.84/2.52  
% 15.84/2.52  ------ QBF Options
% 15.84/2.52  
% 15.84/2.52  --qbf_mode                              false
% 15.84/2.52  --qbf_elim_univ                         false
% 15.84/2.52  --qbf_dom_inst                          none
% 15.84/2.52  --qbf_dom_pre_inst                      false
% 15.84/2.52  --qbf_sk_in                             false
% 15.84/2.52  --qbf_pred_elim                         true
% 15.84/2.52  --qbf_split                             512
% 15.84/2.52  
% 15.84/2.52  ------ BMC1 Options
% 15.84/2.52  
% 15.84/2.52  --bmc1_incremental                      false
% 15.84/2.52  --bmc1_axioms                           reachable_all
% 15.84/2.52  --bmc1_min_bound                        0
% 15.84/2.52  --bmc1_max_bound                        -1
% 15.84/2.52  --bmc1_max_bound_default                -1
% 15.84/2.52  --bmc1_symbol_reachability              true
% 15.84/2.52  --bmc1_property_lemmas                  false
% 15.84/2.52  --bmc1_k_induction                      false
% 15.84/2.52  --bmc1_non_equiv_states                 false
% 15.84/2.52  --bmc1_deadlock                         false
% 15.84/2.52  --bmc1_ucm                              false
% 15.84/2.52  --bmc1_add_unsat_core                   none
% 15.84/2.52  --bmc1_unsat_core_children              false
% 15.84/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.84/2.52  --bmc1_out_stat                         full
% 15.84/2.52  --bmc1_ground_init                      false
% 15.84/2.52  --bmc1_pre_inst_next_state              false
% 15.84/2.52  --bmc1_pre_inst_state                   false
% 15.84/2.52  --bmc1_pre_inst_reach_state             false
% 15.84/2.52  --bmc1_out_unsat_core                   false
% 15.84/2.52  --bmc1_aig_witness_out                  false
% 15.84/2.52  --bmc1_verbose                          false
% 15.84/2.52  --bmc1_dump_clauses_tptp                false
% 15.84/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.84/2.52  --bmc1_dump_file                        -
% 15.84/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.84/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.84/2.52  --bmc1_ucm_extend_mode                  1
% 15.84/2.52  --bmc1_ucm_init_mode                    2
% 15.84/2.52  --bmc1_ucm_cone_mode                    none
% 15.84/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.84/2.52  --bmc1_ucm_relax_model                  4
% 15.84/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.84/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.84/2.52  --bmc1_ucm_layered_model                none
% 15.84/2.52  --bmc1_ucm_max_lemma_size               10
% 15.84/2.52  
% 15.84/2.52  ------ AIG Options
% 15.84/2.52  
% 15.84/2.52  --aig_mode                              false
% 15.84/2.52  
% 15.84/2.52  ------ Instantiation Options
% 15.84/2.52  
% 15.84/2.52  --instantiation_flag                    true
% 15.84/2.52  --inst_sos_flag                         false
% 15.84/2.52  --inst_sos_phase                        true
% 15.84/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.84/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.84/2.52  --inst_lit_sel_side                     none
% 15.84/2.52  --inst_solver_per_active                1400
% 15.84/2.52  --inst_solver_calls_frac                1.
% 15.84/2.52  --inst_passive_queue_type               priority_queues
% 15.84/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.84/2.52  --inst_passive_queues_freq              [25;2]
% 15.84/2.52  --inst_dismatching                      true
% 15.84/2.52  --inst_eager_unprocessed_to_passive     true
% 15.84/2.52  --inst_prop_sim_given                   true
% 15.84/2.52  --inst_prop_sim_new                     false
% 15.84/2.52  --inst_subs_new                         false
% 15.84/2.52  --inst_eq_res_simp                      false
% 15.84/2.52  --inst_subs_given                       false
% 15.84/2.52  --inst_orphan_elimination               true
% 15.84/2.52  --inst_learning_loop_flag               true
% 15.84/2.52  --inst_learning_start                   3000
% 15.84/2.52  --inst_learning_factor                  2
% 15.84/2.52  --inst_start_prop_sim_after_learn       3
% 15.84/2.52  --inst_sel_renew                        solver
% 15.84/2.52  --inst_lit_activity_flag                true
% 15.84/2.52  --inst_restr_to_given                   false
% 15.84/2.52  --inst_activity_threshold               500
% 15.84/2.52  --inst_out_proof                        true
% 15.84/2.52  
% 15.84/2.52  ------ Resolution Options
% 15.84/2.52  
% 15.84/2.52  --resolution_flag                       false
% 15.84/2.52  --res_lit_sel                           adaptive
% 15.84/2.52  --res_lit_sel_side                      none
% 15.84/2.52  --res_ordering                          kbo
% 15.84/2.52  --res_to_prop_solver                    active
% 15.84/2.52  --res_prop_simpl_new                    false
% 15.84/2.52  --res_prop_simpl_given                  true
% 15.84/2.52  --res_passive_queue_type                priority_queues
% 15.84/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.84/2.52  --res_passive_queues_freq               [15;5]
% 15.84/2.52  --res_forward_subs                      full
% 15.84/2.52  --res_backward_subs                     full
% 15.84/2.52  --res_forward_subs_resolution           true
% 15.84/2.52  --res_backward_subs_resolution          true
% 15.84/2.52  --res_orphan_elimination                true
% 15.84/2.52  --res_time_limit                        2.
% 15.84/2.52  --res_out_proof                         true
% 15.84/2.52  
% 15.84/2.52  ------ Superposition Options
% 15.84/2.52  
% 15.84/2.52  --superposition_flag                    true
% 15.84/2.52  --sup_passive_queue_type                priority_queues
% 15.84/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.84/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.84/2.52  --demod_completeness_check              fast
% 15.84/2.52  --demod_use_ground                      true
% 15.84/2.52  --sup_to_prop_solver                    passive
% 15.84/2.52  --sup_prop_simpl_new                    true
% 15.84/2.52  --sup_prop_simpl_given                  true
% 15.84/2.52  --sup_fun_splitting                     false
% 15.84/2.52  --sup_smt_interval                      50000
% 15.84/2.52  
% 15.84/2.52  ------ Superposition Simplification Setup
% 15.84/2.52  
% 15.84/2.52  --sup_indices_passive                   []
% 15.84/2.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.84/2.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.84/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.84/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.84/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.84/2.52  --sup_full_bw                           [BwDemod]
% 15.84/2.52  --sup_immed_triv                        [TrivRules]
% 15.84/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.84/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.84/2.52  --sup_immed_bw_main                     []
% 15.84/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.84/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.84/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.84/2.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.84/2.52  
% 15.84/2.52  ------ Combination Options
% 15.84/2.52  
% 15.84/2.52  --comb_res_mult                         3
% 15.84/2.52  --comb_sup_mult                         2
% 15.84/2.52  --comb_inst_mult                        10
% 15.84/2.52  
% 15.84/2.52  ------ Debug Options
% 15.84/2.52  
% 15.84/2.52  --dbg_backtrace                         false
% 15.84/2.52  --dbg_dump_prop_clauses                 false
% 15.84/2.52  --dbg_dump_prop_clauses_file            -
% 15.84/2.52  --dbg_out_stat                          false
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  ------ Proving...
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  % SZS status Theorem for theBenchmark.p
% 15.84/2.52  
% 15.84/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.84/2.52  
% 15.84/2.52  fof(f4,axiom,(
% 15.84/2.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f73,plain,(
% 15.84/2.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.84/2.52    inference(cnf_transformation,[],[f4])).
% 15.84/2.52  
% 15.84/2.52  fof(f1,axiom,(
% 15.84/2.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f69,plain,(
% 15.84/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f1])).
% 15.84/2.52  
% 15.84/2.52  fof(f5,axiom,(
% 15.84/2.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f74,plain,(
% 15.84/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.84/2.52    inference(cnf_transformation,[],[f5])).
% 15.84/2.52  
% 15.84/2.52  fof(f119,plain,(
% 15.84/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.84/2.52    inference(definition_unfolding,[],[f69,f74,f74])).
% 15.84/2.52  
% 15.84/2.52  fof(f3,axiom,(
% 15.84/2.52    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f72,plain,(
% 15.84/2.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.84/2.52    inference(cnf_transformation,[],[f3])).
% 15.84/2.52  
% 15.84/2.52  fof(f122,plain,(
% 15.84/2.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 15.84/2.52    inference(definition_unfolding,[],[f72,f74])).
% 15.84/2.52  
% 15.84/2.52  fof(f2,axiom,(
% 15.84/2.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f45,plain,(
% 15.84/2.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.84/2.52    inference(nnf_transformation,[],[f2])).
% 15.84/2.52  
% 15.84/2.52  fof(f71,plain,(
% 15.84/2.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.84/2.52    inference(cnf_transformation,[],[f45])).
% 15.84/2.52  
% 15.84/2.52  fof(f120,plain,(
% 15.84/2.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.84/2.52    inference(definition_unfolding,[],[f71,f74])).
% 15.84/2.52  
% 15.84/2.52  fof(f19,axiom,(
% 15.84/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f37,plain,(
% 15.84/2.52    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.84/2.52    inference(ennf_transformation,[],[f19])).
% 15.84/2.52  
% 15.84/2.52  fof(f38,plain,(
% 15.84/2.52    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f37])).
% 15.84/2.52  
% 15.84/2.52  fof(f108,plain,(
% 15.84/2.52    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f38])).
% 15.84/2.52  
% 15.84/2.52  fof(f21,conjecture,(
% 15.84/2.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f22,negated_conjecture,(
% 15.84/2.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 15.84/2.52    inference(negated_conjecture,[],[f21])).
% 15.84/2.52  
% 15.84/2.52  fof(f40,plain,(
% 15.84/2.52    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.84/2.52    inference(ennf_transformation,[],[f22])).
% 15.84/2.52  
% 15.84/2.52  fof(f41,plain,(
% 15.84/2.52    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f40])).
% 15.84/2.52  
% 15.84/2.52  fof(f62,plain,(
% 15.84/2.52    ? [X0] : (? [X1] : (((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.84/2.52    inference(nnf_transformation,[],[f41])).
% 15.84/2.52  
% 15.84/2.52  fof(f63,plain,(
% 15.84/2.52    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f62])).
% 15.84/2.52  
% 15.84/2.52  fof(f64,plain,(
% 15.84/2.52    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.84/2.52    inference(rectify,[],[f63])).
% 15.84/2.52  
% 15.84/2.52  fof(f67,plain,(
% 15.84/2.52    ( ! [X0,X1] : (? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK8) & v3_pre_topc(sK8,X0) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f66,plain,(
% 15.84/2.52    ( ! [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (r1_xboole_0(sK7,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(sK7,X0)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f65,plain,(
% 15.84/2.52    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK6) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(X1,sK6)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f68,plain,(
% 15.84/2.52    (((r1_xboole_0(sK7,sK8) & v3_pre_topc(sK8,sK6) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(sK7,sK6)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 15.84/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f64,f67,f66,f65])).
% 15.84/2.52  
% 15.84/2.52  fof(f111,plain,(
% 15.84/2.52    v2_pre_topc(sK6)),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f112,plain,(
% 15.84/2.52    l1_pre_topc(sK6)),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f15,axiom,(
% 15.84/2.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f31,plain,(
% 15.84/2.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f15])).
% 15.84/2.52  
% 15.84/2.52  fof(f97,plain,(
% 15.84/2.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f31])).
% 15.84/2.52  
% 15.84/2.52  fof(f14,axiom,(
% 15.84/2.52    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f30,plain,(
% 15.84/2.52    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f14])).
% 15.84/2.52  
% 15.84/2.52  fof(f96,plain,(
% 15.84/2.52    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f30])).
% 15.84/2.52  
% 15.84/2.52  fof(f42,plain,(
% 15.84/2.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0))))),
% 15.84/2.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 15.84/2.52  
% 15.84/2.52  fof(f48,plain,(
% 15.84/2.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2))) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 15.84/2.52    inference(nnf_transformation,[],[f42])).
% 15.84/2.52  
% 15.84/2.52  fof(f49,plain,(
% 15.84/2.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 15.84/2.52    inference(flattening,[],[f48])).
% 15.84/2.52  
% 15.84/2.52  fof(f50,plain,(
% 15.84/2.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 15.84/2.52    inference(rectify,[],[f49])).
% 15.84/2.52  
% 15.84/2.52  fof(f53,plain,(
% 15.84/2.52    ! [X6,X1,X0] : (? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))))),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f52,plain,(
% 15.84/2.52    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(X3,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f51,plain,(
% 15.84/2.52    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1))) => ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(sK2(X0,X1,X2),X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f54,plain,(
% 15.84/2.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 15.84/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f50,f53,f52,f51])).
% 15.84/2.52  
% 15.84/2.52  fof(f89,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))) )),
% 15.84/2.52    inference(cnf_transformation,[],[f54])).
% 15.84/2.52  
% 15.84/2.52  fof(f90,plain,(
% 15.84/2.52    ( ! [X2,X0,X5,X1] : (sP0(X0,X1,X2) | ~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f54])).
% 15.84/2.52  
% 15.84/2.52  fof(f8,axiom,(
% 15.84/2.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f77,plain,(
% 15.84/2.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.84/2.52    inference(cnf_transformation,[],[f8])).
% 15.84/2.52  
% 15.84/2.52  fof(f6,axiom,(
% 15.84/2.52    ! [X0] : k2_subset_1(X0) = X0),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f75,plain,(
% 15.84/2.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.84/2.52    inference(cnf_transformation,[],[f6])).
% 15.84/2.52  
% 15.84/2.52  fof(f115,plain,(
% 15.84/2.52    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_tops_1(sK7,sK6)),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f10,axiom,(
% 15.84/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f25,plain,(
% 15.84/2.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.84/2.52    inference(ennf_transformation,[],[f10])).
% 15.84/2.52  
% 15.84/2.52  fof(f79,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.84/2.52    inference(cnf_transformation,[],[f25])).
% 15.84/2.52  
% 15.84/2.52  fof(f94,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_xboole_0(X0,sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f54])).
% 15.84/2.52  
% 15.84/2.52  fof(f91,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f54])).
% 15.84/2.52  
% 15.84/2.52  fof(f114,plain,(
% 15.84/2.52    ( ! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | v1_tops_1(sK7,sK6)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f92,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f54])).
% 15.84/2.52  
% 15.84/2.52  fof(f113,plain,(
% 15.84/2.52    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f18,axiom,(
% 15.84/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f36,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f18])).
% 15.84/2.52  
% 15.84/2.52  fof(f60,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(nnf_transformation,[],[f36])).
% 15.84/2.52  
% 15.84/2.52  fof(f107,plain,(
% 15.84/2.52    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f60])).
% 15.84/2.52  
% 15.84/2.52  fof(f43,plain,(
% 15.84/2.52    ! [X2,X0,X1] : ((k2_pre_topc(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 15.84/2.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 15.84/2.52  
% 15.84/2.52  fof(f46,plain,(
% 15.84/2.52    ! [X2,X0,X1] : (((k2_pre_topc(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_pre_topc(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 15.84/2.52    inference(nnf_transformation,[],[f43])).
% 15.84/2.52  
% 15.84/2.52  fof(f47,plain,(
% 15.84/2.52    ! [X0,X1,X2] : (((k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 15.84/2.52    inference(rectify,[],[f46])).
% 15.84/2.52  
% 15.84/2.52  fof(f83,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f47])).
% 15.84/2.52  
% 15.84/2.52  fof(f13,axiom,(
% 15.84/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f28,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f13])).
% 15.84/2.52  
% 15.84/2.52  fof(f29,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f28])).
% 15.84/2.52  
% 15.84/2.52  fof(f44,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(definition_folding,[],[f29,f43,f42])).
% 15.84/2.52  
% 15.84/2.52  fof(f95,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f44])).
% 15.84/2.52  
% 15.84/2.52  fof(f106,plain,(
% 15.84/2.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f60])).
% 15.84/2.52  
% 15.84/2.52  fof(f93,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f54])).
% 15.84/2.52  
% 15.84/2.52  fof(f11,axiom,(
% 15.84/2.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f80,plain,(
% 15.84/2.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.84/2.52    inference(cnf_transformation,[],[f11])).
% 15.84/2.52  
% 15.84/2.52  fof(f7,axiom,(
% 15.84/2.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f23,plain,(
% 15.84/2.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.84/2.52    inference(ennf_transformation,[],[f7])).
% 15.84/2.52  
% 15.84/2.52  fof(f76,plain,(
% 15.84/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.84/2.52    inference(cnf_transformation,[],[f23])).
% 15.84/2.52  
% 15.84/2.52  fof(f20,axiom,(
% 15.84/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f39,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f20])).
% 15.84/2.52  
% 15.84/2.52  fof(f61,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(nnf_transformation,[],[f39])).
% 15.84/2.52  
% 15.84/2.52  fof(f110,plain,(
% 15.84/2.52    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f61])).
% 15.84/2.52  
% 15.84/2.52  fof(f16,axiom,(
% 15.84/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f32,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f16])).
% 15.84/2.52  
% 15.84/2.52  fof(f33,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f32])).
% 15.84/2.52  
% 15.84/2.52  fof(f98,plain,(
% 15.84/2.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f33])).
% 15.84/2.52  
% 15.84/2.52  fof(f17,axiom,(
% 15.84/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f34,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(ennf_transformation,[],[f17])).
% 15.84/2.52  
% 15.84/2.52  fof(f35,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f34])).
% 15.84/2.52  
% 15.84/2.52  fof(f55,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(nnf_transformation,[],[f35])).
% 15.84/2.52  
% 15.84/2.52  fof(f56,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(flattening,[],[f55])).
% 15.84/2.52  
% 15.84/2.52  fof(f57,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(rectify,[],[f56])).
% 15.84/2.52  
% 15.84/2.52  fof(f58,plain,(
% 15.84/2.52    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.84/2.52    introduced(choice_axiom,[])).
% 15.84/2.52  
% 15.84/2.52  fof(f59,plain,(
% 15.84/2.52    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.84/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).
% 15.84/2.52  
% 15.84/2.52  fof(f101,plain,(
% 15.84/2.52    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f59])).
% 15.84/2.52  
% 15.84/2.52  fof(f12,axiom,(
% 15.84/2.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 15.84/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.84/2.52  
% 15.84/2.52  fof(f26,plain,(
% 15.84/2.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 15.84/2.52    inference(ennf_transformation,[],[f12])).
% 15.84/2.52  
% 15.84/2.52  fof(f27,plain,(
% 15.84/2.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.84/2.52    inference(flattening,[],[f26])).
% 15.84/2.52  
% 15.84/2.52  fof(f81,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f27])).
% 15.84/2.52  
% 15.84/2.52  fof(f100,plain,(
% 15.84/2.52    ( ! [X2,X0,X1] : (~v2_struct_0(X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.84/2.52    inference(cnf_transformation,[],[f59])).
% 15.84/2.52  
% 15.84/2.52  fof(f118,plain,(
% 15.84/2.52    r1_xboole_0(sK7,sK8) | ~v1_tops_1(sK7,sK6)),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f117,plain,(
% 15.84/2.52    v3_pre_topc(sK8,sK6) | ~v1_tops_1(sK7,sK6)),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  fof(f116,plain,(
% 15.84/2.52    k1_xboole_0 != sK8 | ~v1_tops_1(sK7,sK6)),
% 15.84/2.52    inference(cnf_transformation,[],[f68])).
% 15.84/2.52  
% 15.84/2.52  cnf(c_4,plain,
% 15.84/2.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f73]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_0,plain,
% 15.84/2.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f119]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8994,plain,
% 15.84/2.52      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_3,plain,
% 15.84/2.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f122]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8521,plain,
% 15.84/2.52      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9652,plain,
% 15.84/2.52      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_8994,c_8521]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1,plain,
% 15.84/2.52      ( r1_xboole_0(X0,X1)
% 15.84/2.52      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f120]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8504,plain,
% 15.84/2.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 15.84/2.52      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10152,plain,
% 15.84/2.52      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_9652,c_8504]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_38,plain,
% 15.84/2.52      ( v3_pre_topc(k2_struct_0(X0),X0)
% 15.84/2.52      | ~ v2_pre_topc(X0)
% 15.84/2.52      | ~ l1_pre_topc(X0) ),
% 15.84/2.52      inference(cnf_transformation,[],[f108]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_48,negated_conjecture,
% 15.84/2.52      ( v2_pre_topc(sK6) ),
% 15.84/2.52      inference(cnf_transformation,[],[f111]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_629,plain,
% 15.84/2.52      ( v3_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK6 != X0 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_38,c_48]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_630,plain,
% 15.84/2.52      ( v3_pre_topc(k2_struct_0(sK6),sK6) | ~ l1_pre_topc(sK6) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_629]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_47,negated_conjecture,
% 15.84/2.52      ( l1_pre_topc(sK6) ),
% 15.84/2.52      inference(cnf_transformation,[],[f112]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_66,plain,
% 15.84/2.52      ( v3_pre_topc(k2_struct_0(sK6),sK6)
% 15.84/2.52      | ~ v2_pre_topc(sK6)
% 15.84/2.52      | ~ l1_pre_topc(sK6) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_38]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_632,plain,
% 15.84/2.52      ( v3_pre_topc(k2_struct_0(sK6),sK6) ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_630,c_48,c_47,c_66]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8479,plain,
% 15.84/2.52      ( v3_pre_topc(k2_struct_0(sK6),sK6) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_27,plain,
% 15.84/2.52      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 15.84/2.52      inference(cnf_transformation,[],[f97]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_26,plain,
% 15.84/2.52      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 15.84/2.52      inference(cnf_transformation,[],[f96]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_615,plain,
% 15.84/2.52      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 15.84/2.52      inference(resolution,[status(thm)],[c_27,c_26]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_920,plain,
% 15.84/2.52      ( k2_struct_0(X0) = u1_struct_0(X0) | sK6 != X0 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_615,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_921,plain,
% 15.84/2.52      ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_920]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8511,plain,
% 15.84/2.52      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_8479,c_921]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_19,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f89]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8491,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_18,plain,
% 15.84/2.52      ( sP0(X0,X1,X2)
% 15.84/2.52      | ~ v3_pre_topc(X3,X1)
% 15.84/2.52      | ~ r2_hidden(sK2(X0,X1,X2),X3)
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2)
% 15.84/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ r1_xboole_0(X0,X3) ),
% 15.84/2.52      inference(cnf_transformation,[],[f90]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8492,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | v3_pre_topc(X3,X1) != iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 15.84/2.52      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X0,X3) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_14472,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 15.84/2.52      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8491,c_8492]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_7,plain,
% 15.84/2.52      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f77]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8501,plain,
% 15.84/2.52      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_5,plain,
% 15.84/2.52      ( k2_subset_1(X0) = X0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f75]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8518,plain,
% 15.84/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_8501,c_5]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_70054,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 15.84/2.52      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 15.84/2.52      inference(forward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_14472,c_8518]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_70058,plain,
% 15.84/2.52      ( sP0(X0,sK6,X1) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
% 15.84/2.52      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8511,c_70054]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_44,negated_conjecture,
% 15.84/2.52      ( ~ v1_tops_1(sK7,sK6)
% 15.84/2.52      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 15.84/2.52      inference(cnf_transformation,[],[f115]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8482,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9,plain,
% 15.84/2.52      ( ~ r2_hidden(X0,X1)
% 15.84/2.52      | r2_hidden(X0,X2)
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f79]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8499,plain,
% 15.84/2.52      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.52      | r2_hidden(X0,X2) = iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_11925,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8482,c_8499]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_14,plain,
% 15.84/2.52      ( sP0(X0,X1,X2)
% 15.84/2.52      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 15.84/2.52      | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f94]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8496,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 15.84/2.52      | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_12526,plain,
% 15.84/2.52      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 15.84/2.52      | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8491,c_8496]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_17,plain,
% 15.84/2.52      ( sP0(X0,X1,X2)
% 15.84/2.52      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 15.84/2.52      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
% 15.84/2.52      inference(cnf_transformation,[],[f91]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8493,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 15.84/2.52      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_13155,plain,
% 15.84/2.52      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 15.84/2.52      | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8491,c_8493]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_45,negated_conjecture,
% 15.84/2.52      ( v1_tops_1(sK7,sK6)
% 15.84/2.52      | ~ v3_pre_topc(X0,sK6)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ r1_xboole_0(sK7,X0)
% 15.84/2.52      | k1_xboole_0 = X0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f114]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8481,plain,
% 15.84/2.52      ( k1_xboole_0 = X0
% 15.84/2.52      | v1_tops_1(sK7,sK6) = iProver_top
% 15.84/2.52      | v3_pre_topc(X0,sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(sK7,X0) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_46504,plain,
% 15.84/2.52      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 15.84/2.52      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 15.84/2.52      | v1_tops_1(sK7,sK6) = iProver_top
% 15.84/2.52      | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
% 15.84/2.52      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_13155,c_8481]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_16,plain,
% 15.84/2.52      ( sP0(X0,X1,X2)
% 15.84/2.52      | v3_pre_topc(sK3(X0,X1,X2),X1)
% 15.84/2.52      | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
% 15.84/2.52      inference(cnf_transformation,[],[f92]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8494,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_12496,plain,
% 15.84/2.52      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 15.84/2.52      | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8491,c_8494]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_48879,plain,
% 15.84/2.52      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 15.84/2.52      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 15.84/2.52      | v1_tops_1(sK7,sK6) = iProver_top
% 15.84/2.52      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(forward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_46504,c_12496]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_48883,plain,
% 15.84/2.52      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 15.84/2.52      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 15.84/2.52      | v1_tops_1(sK7,sK6) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_12526,c_48879]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_46,negated_conjecture,
% 15.84/2.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 15.84/2.52      inference(cnf_transformation,[],[f113]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_51,plain,
% 15.84/2.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_99,plain,
% 15.84/2.52      ( l1_struct_0(sK6) | ~ l1_pre_topc(sK6) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_27]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_102,plain,
% 15.84/2.52      ( ~ l1_struct_0(sK6) | k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_36,plain,
% 15.84/2.52      ( v1_tops_1(X0,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ l1_pre_topc(X1)
% 15.84/2.52      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 15.84/2.52      inference(cnf_transformation,[],[f107]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_961,plain,
% 15.84/2.52      ( v1_tops_1(X0,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 15.84/2.52      | sK6 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_36,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_962,plain,
% 15.84/2.52      ( v1_tops_1(X0,sK6)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,X0) != k2_struct_0(sK6) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_961]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8861,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6)
% 15.84/2.52      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_962]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8862,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 15.84/2.52      | v1_tops_1(sK7,sK6) = iProver_top
% 15.84/2.52      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_8861]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_7568,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8997,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) != X0
% 15.84/2.52      | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 15.84/2.52      | k2_struct_0(sK6) != X0 ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_7568]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9230,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 15.84/2.52      | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
% 15.84/2.52      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_8997]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8480,plain,
% 15.84/2.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_12,plain,
% 15.84/2.52      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | k2_pre_topc(X1,X2) = X0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f83]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_25,plain,
% 15.84/2.52      ( sP1(X0,X1,X2)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ l1_pre_topc(X1) ),
% 15.84/2.52      inference(cnf_transformation,[],[f95]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1086,plain,
% 15.84/2.52      ( sP1(X0,X1,X2)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | sK6 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_25,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1087,plain,
% 15.84/2.52      ( sP1(X0,sK6,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_1086]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1154,plain,
% 15.84/2.52      ( ~ sP0(X0,X1,X2)
% 15.84/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | X3 != X2
% 15.84/2.52      | X4 != X0
% 15.84/2.52      | k2_pre_topc(X1,X0) = X2
% 15.84/2.52      | sK6 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_12,c_1087]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1155,plain,
% 15.84/2.52      ( ~ sP0(X0,sK6,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,X0) = X1 ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_1154]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8468,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,X0) = X1
% 15.84/2.52      | sP0(X0,sK6,X1) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9409,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = X0
% 15.84/2.52      | sP0(sK7,sK6,X0) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8480,c_8468]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9752,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 15.84/2.52      | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8518,c_9409]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_54144,plain,
% 15.84/2.52      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 15.84/2.52      | v1_tops_1(sK7,sK6) = iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_48883,c_47,c_51,c_99,c_102,c_8862,c_9230,c_9752]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_37,plain,
% 15.84/2.52      ( ~ v1_tops_1(X0,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ l1_pre_topc(X1)
% 15.84/2.52      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 15.84/2.52      inference(cnf_transformation,[],[f106]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_946,plain,
% 15.84/2.52      ( ~ v1_tops_1(X0,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 15.84/2.52      | sK6 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_37,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_947,plain,
% 15.84/2.52      ( ~ v1_tops_1(X0,sK6)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,X0) = k2_struct_0(sK6) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_946]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8475,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,X0) = k2_struct_0(sK6)
% 15.84/2.52      | v1_tops_1(X0,sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8581,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,X0) = u1_struct_0(sK6)
% 15.84/2.52      | v1_tops_1(X0,sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_8475,c_921]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9170,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 15.84/2.52      | v1_tops_1(sK7,sK6) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8480,c_8581]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_54163,plain,
% 15.84/2.52      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 15.84/2.52      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_54144,c_9170]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_15,plain,
% 15.84/2.52      ( sP0(X0,X1,X2)
% 15.84/2.52      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f93]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8495,plain,
% 15.84/2.52      ( sP0(X0,X1,X2) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 15.84/2.52      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_55101,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 15.84/2.52      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_54163,c_8495]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9056,plain,
% 15.84/2.52      ( sP0(sK7,sK6,X0) | r2_hidden(sK2(sK7,sK6,X0),u1_struct_0(sK6)) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_19]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_17349,plain,
% 15.84/2.52      ( sP0(sK7,sK6,u1_struct_0(sK6))
% 15.84/2.52      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_9056]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_17352,plain,
% 15.84/2.52      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 15.84/2.52      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_17349]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_62271,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 15.84/2.52      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_55101,c_9752,c_17352]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10,plain,
% 15.84/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f80]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8498,plain,
% 15.84/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_6,plain,
% 15.84/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.84/2.52      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.84/2.52      inference(cnf_transformation,[],[f76]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8502,plain,
% 15.84/2.52      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10780,plain,
% 15.84/2.52      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8498,c_8502]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10805,plain,
% 15.84/2.52      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_10780,c_4]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_39,plain,
% 15.84/2.52      ( v4_pre_topc(X0,X1)
% 15.84/2.52      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ l1_pre_topc(X1) ),
% 15.84/2.52      inference(cnf_transformation,[],[f110]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_29,plain,
% 15.84/2.52      ( ~ v4_pre_topc(X0,X1)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ l1_pre_topc(X1)
% 15.84/2.52      | k2_pre_topc(X1,X0) = X0 ),
% 15.84/2.52      inference(cnf_transformation,[],[f98]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_715,plain,
% 15.84/2.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.84/2.52      | ~ l1_pre_topc(X0)
% 15.84/2.52      | k2_pre_topc(X0,X1) = X1 ),
% 15.84/2.52      inference(resolution,[status(thm)],[c_39,c_29]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_905,plain,
% 15.84/2.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.84/2.52      | k2_pre_topc(X0,X1) = X1
% 15.84/2.52      | sK6 != X0 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_715,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_906,plain,
% 15.84/2.52      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6)
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,X0) = X0 ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_905]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8477,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,X0) = X0
% 15.84/2.52      | v3_pre_topc(k3_subset_1(u1_struct_0(sK6),X0),sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10814,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 15.84/2.52      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_10805,c_8477]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8892,plain,
% 15.84/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 15.84/2.52      inference(instantiation,[status(thm)],[c_10]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8898,plain,
% 15.84/2.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_8892]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_11618,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_10814,c_8511,c_8898]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_34,plain,
% 15.84/2.52      ( ~ v3_pre_topc(X0,X1)
% 15.84/2.52      | ~ r2_hidden(X2,X0)
% 15.84/2.52      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 15.84/2.52      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.84/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ r1_xboole_0(X3,X0)
% 15.84/2.52      | ~ l1_pre_topc(X1) ),
% 15.84/2.52      inference(cnf_transformation,[],[f101]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_994,plain,
% 15.84/2.52      ( ~ v3_pre_topc(X0,X1)
% 15.84/2.52      | ~ r2_hidden(X2,X0)
% 15.84/2.52      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 15.84/2.52      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.84/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ r1_xboole_0(X3,X0)
% 15.84/2.52      | sK6 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_34,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_995,plain,
% 15.84/2.52      ( ~ v3_pre_topc(X0,sK6)
% 15.84/2.52      | ~ r2_hidden(X1,X0)
% 15.84/2.52      | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
% 15.84/2.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ r1_xboole_0(X2,X0) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_994]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_11,plain,
% 15.84/2.52      ( ~ r2_hidden(X0,X1)
% 15.84/2.52      | m1_subset_1(X0,X2)
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 15.84/2.52      inference(cnf_transformation,[],[f81]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1013,plain,
% 15.84/2.52      ( ~ v3_pre_topc(X0,sK6)
% 15.84/2.52      | ~ r2_hidden(X1,X0)
% 15.84/2.52      | ~ r2_hidden(X1,k2_pre_topc(sK6,X2))
% 15.84/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ r1_xboole_0(X2,X0) ),
% 15.84/2.52      inference(forward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_995,c_11]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8472,plain,
% 15.84/2.52      ( v3_pre_topc(X0,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X1,X0) != iProver_top
% 15.84/2.52      | r2_hidden(X1,k2_pre_topc(sK6,X2)) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X2,X0) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10635,plain,
% 15.84/2.52      ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8518,c_8472]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_32414,plain,
% 15.84/2.52      ( r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X1,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_10635,c_8511]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_32437,plain,
% 15.84/2.52      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.84/2.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_11618,c_32414]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_53770,plain,
% 15.84/2.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.84/2.52      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_32437,c_8898]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_53771,plain,
% 15.84/2.52      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.84/2.52      | r1_xboole_0(k1_xboole_0,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(renaming,[status(thm)],[c_53770]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_11924,plain,
% 15.84/2.52      ( r2_hidden(X0,X1) = iProver_top
% 15.84/2.52      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8498,c_8499]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_53779,plain,
% 15.84/2.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.84/2.52      inference(forward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_53771,c_10152,c_11924]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_62277,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 15.84/2.52      inference(forward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_62271,c_53779]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_35,plain,
% 15.84/2.52      ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
% 15.84/2.52      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ v2_struct_0(X1)
% 15.84/2.52      | ~ l1_pre_topc(X1) ),
% 15.84/2.52      inference(cnf_transformation,[],[f100]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_976,plain,
% 15.84/2.52      ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
% 15.84/2.52      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.84/2.52      | ~ v2_struct_0(X1)
% 15.84/2.52      | sK6 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_35,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_977,plain,
% 15.84/2.52      ( ~ r2_hidden(X0,k2_pre_topc(sK6,X1))
% 15.84/2.52      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ v2_struct_0(sK6) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_976]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8473,plain,
% 15.84/2.52      ( r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | v2_struct_0(sK6) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_62795,plain,
% 15.84/2.52      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | v2_struct_0(sK6) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_62277,c_8473]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_67846,plain,
% 15.84/2.52      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | v2_struct_0(sK6) != iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_62795,c_51]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_67847,plain,
% 15.84/2.52      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | v2_struct_0(sK6) != iProver_top ),
% 15.84/2.52      inference(renaming,[status(thm)],[c_67846]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8497,plain,
% 15.84/2.52      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,X2) = iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_11818,plain,
% 15.84/2.52      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,X1) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8518,c_8497]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_67855,plain,
% 15.84/2.52      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | v2_struct_0(sK6) != iProver_top ),
% 15.84/2.52      inference(forward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_67847,c_11818]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_67861,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top
% 15.84/2.52      | v2_struct_0(sK6) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_11925,c_67855]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_41,negated_conjecture,
% 15.84/2.52      ( ~ v1_tops_1(sK7,sK6) | r1_xboole_0(sK7,sK8) ),
% 15.84/2.52      inference(cnf_transformation,[],[f118]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1467,plain,
% 15.84/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | r1_xboole_0(sK7,sK8)
% 15.84/2.52      | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
% 15.84/2.52      | sK6 != sK6
% 15.84/2.52      | sK7 != X0 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_41,c_962]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1468,plain,
% 15.84/2.52      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | r1_xboole_0(sK7,sK8)
% 15.84/2.52      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_1467]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1470,plain,
% 15.84/2.52      ( r1_xboole_0(sK7,sK8) | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_1468,c_46]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1472,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 15.84/2.52      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8474,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
% 15.84/2.52      | v1_tops_1(X0,sK6) = iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_8574,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,X0) != u1_struct_0(sK6)
% 15.84/2.52      | v1_tops_1(X0,sK6) = iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(light_normalisation,[status(thm)],[c_8474,c_921]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_62783,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) = iProver_top
% 15.84/2.52      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_62277,c_8574]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_10632,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | v3_pre_topc(sK8,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X1,sK8) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8482,c_8472]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_55,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_42,negated_conjecture,
% 15.84/2.52      ( ~ v1_tops_1(sK7,sK6) | v3_pre_topc(sK8,sK6) ),
% 15.84/2.52      inference(cnf_transformation,[],[f117]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_2753,plain,
% 15.84/2.52      ( ~ v1_tops_1(sK7,sK6)
% 15.84/2.52      | ~ r2_hidden(X0,X1)
% 15.84/2.52      | ~ r2_hidden(X0,k2_pre_topc(sK6,X2))
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ r1_xboole_0(X2,X1)
% 15.84/2.52      | sK6 != sK6
% 15.84/2.52      | sK8 != X1 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_42,c_1013]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_2754,plain,
% 15.84/2.52      ( ~ v1_tops_1(sK7,sK6)
% 15.84/2.52      | ~ r2_hidden(X0,k2_pre_topc(sK6,X1))
% 15.84/2.52      | ~ r2_hidden(X0,sK8)
% 15.84/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | ~ r1_xboole_0(X1,sK8) ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_2753]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_2755,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X1,sK8) != iProver_top ),
% 15.84/2.52      inference(predicate_to_equality,[status(thm)],[c_2754]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_11381,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top
% 15.84/2.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(X1,sK8) != iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_10632,c_55,c_2755]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_62793,plain,
% 15.84/2.52      ( v1_tops_1(sK7,sK6) != iProver_top
% 15.84/2.52      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top
% 15.84/2.52      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_62277,c_11381]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_62950,plain,
% 15.84/2.52      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 15.84/2.52      | r2_hidden(X0,sK8) != iProver_top
% 15.84/2.52      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 15.84/2.52      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 15.84/2.52      inference(backward_subsumption_resolution,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_62783,c_62793]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_68327,plain,
% 15.84/2.52      ( r2_hidden(X0,sK8) != iProver_top ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_67861,c_47,c_51,c_99,c_102,c_1469,c_8862,c_9230,
% 15.84/2.52                 c_11925,c_62277,c_62950]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_70842,plain,
% 15.84/2.52      ( sP0(X0,sK6,sK8) = iProver_top
% 15.84/2.52      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_70058,c_68327]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_71513,plain,
% 15.84/2.52      ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_10152,c_70842]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_9501,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,k1_xboole_0) = X0
% 15.84/2.52      | sP0(k1_xboole_0,sK6,X0) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8498,c_8468]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_17765,plain,
% 15.84/2.52      ( k1_xboole_0 = X0
% 15.84/2.52      | sP0(k1_xboole_0,sK6,X0) != iProver_top
% 15.84/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 15.84/2.52      inference(demodulation,[status(thm)],[c_9501,c_11618]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_17773,plain,
% 15.84/2.52      ( sK8 = k1_xboole_0
% 15.84/2.52      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 15.84/2.52      | v1_tops_1(sK7,sK6) != iProver_top ),
% 15.84/2.52      inference(superposition,[status(thm)],[c_8482,c_17765]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_43,negated_conjecture,
% 15.84/2.52      ( ~ v1_tops_1(sK7,sK6) | k1_xboole_0 != sK8 ),
% 15.84/2.52      inference(cnf_transformation,[],[f116]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1442,plain,
% 15.84/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,X0) != k2_struct_0(sK6)
% 15.84/2.52      | sK6 != sK6
% 15.84/2.52      | sK8 != k1_xboole_0
% 15.84/2.52      | sK7 != X0 ),
% 15.84/2.52      inference(resolution_lifted,[status(thm)],[c_43,c_962]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1443,plain,
% 15.84/2.52      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 15.84/2.52      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 15.84/2.52      | sK8 != k1_xboole_0 ),
% 15.84/2.52      inference(unflattening,[status(thm)],[c_1442]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(c_1445,plain,
% 15.84/2.52      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) | sK8 != k1_xboole_0 ),
% 15.84/2.52      inference(global_propositional_subsumption,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_1443,c_46]) ).
% 15.84/2.52  
% 15.84/2.52  cnf(contradiction,plain,
% 15.84/2.52      ( $false ),
% 15.84/2.52      inference(minisat,
% 15.84/2.52                [status(thm)],
% 15.84/2.52                [c_71513,c_62277,c_17773,c_9230,c_8862,c_1445,c_102,c_99,
% 15.84/2.52                 c_51,c_47]) ).
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.84/2.52  
% 15.84/2.52  ------                               Statistics
% 15.84/2.52  
% 15.84/2.52  ------ General
% 15.84/2.52  
% 15.84/2.52  abstr_ref_over_cycles:                  0
% 15.84/2.52  abstr_ref_under_cycles:                 0
% 15.84/2.52  gc_basic_clause_elim:                   0
% 15.84/2.52  forced_gc_time:                         0
% 15.84/2.52  parsing_time:                           0.009
% 15.84/2.52  unif_index_cands_time:                  0.
% 15.84/2.52  unif_index_add_time:                    0.
% 15.84/2.52  orderings_time:                         0.
% 15.84/2.52  out_proof_time:                         0.022
% 15.84/2.52  total_time:                             1.731
% 15.84/2.52  num_of_symbols:                         58
% 15.84/2.52  num_of_terms:                           38440
% 15.84/2.52  
% 15.84/2.52  ------ Preprocessing
% 15.84/2.52  
% 15.84/2.52  num_of_splits:                          0
% 15.84/2.52  num_of_split_atoms:                     0
% 15.84/2.52  num_of_reused_defs:                     0
% 15.84/2.52  num_eq_ax_congr_red:                    55
% 15.84/2.52  num_of_sem_filtered_clauses:            1
% 15.84/2.52  num_of_subtypes:                        0
% 15.84/2.52  monotx_restored_types:                  0
% 15.84/2.52  sat_num_of_epr_types:                   0
% 15.84/2.52  sat_num_of_non_cyclic_types:            0
% 15.84/2.52  sat_guarded_non_collapsed_types:        0
% 15.84/2.52  num_pure_diseq_elim:                    0
% 15.84/2.52  simp_replaced_by:                       0
% 15.84/2.52  res_preprocessed:                       211
% 15.84/2.52  prep_upred:                             0
% 15.84/2.52  prep_unflattend:                        285
% 15.84/2.52  smt_new_axioms:                         0
% 15.84/2.52  pred_elim_cands:                        7
% 15.84/2.52  pred_elim:                              5
% 15.84/2.52  pred_elim_cl:                           6
% 15.84/2.52  pred_elim_cycles:                       17
% 15.84/2.52  merged_defs:                            8
% 15.84/2.52  merged_defs_ncl:                        0
% 15.84/2.52  bin_hyper_res:                          8
% 15.84/2.52  prep_cycles:                            4
% 15.84/2.52  pred_elim_time:                         0.102
% 15.84/2.52  splitting_time:                         0.
% 15.84/2.52  sem_filter_time:                        0.
% 15.84/2.52  monotx_time:                            0.
% 15.84/2.52  subtype_inf_time:                       0.
% 15.84/2.52  
% 15.84/2.52  ------ Problem properties
% 15.84/2.52  
% 15.84/2.52  clauses:                                43
% 15.84/2.52  conjectures:                            6
% 15.84/2.52  epr:                                    3
% 15.84/2.52  horn:                                   28
% 15.84/2.52  ground:                                 7
% 15.84/2.52  unary:                                  9
% 15.84/2.52  binary:                                 9
% 15.84/2.52  lits:                                   128
% 15.84/2.52  lits_eq:                                16
% 15.84/2.52  fd_pure:                                0
% 15.84/2.52  fd_pseudo:                              0
% 15.84/2.52  fd_cond:                                1
% 15.84/2.52  fd_pseudo_cond:                         1
% 15.84/2.52  ac_symbols:                             0
% 15.84/2.52  
% 15.84/2.52  ------ Propositional Solver
% 15.84/2.52  
% 15.84/2.52  prop_solver_calls:                      32
% 15.84/2.52  prop_fast_solver_calls:                 5731
% 15.84/2.52  smt_solver_calls:                       0
% 15.84/2.52  smt_fast_solver_calls:                  0
% 15.84/2.52  prop_num_of_clauses:                    19527
% 15.84/2.52  prop_preprocess_simplified:             36878
% 15.84/2.52  prop_fo_subsumed:                       220
% 15.84/2.52  prop_solver_time:                       0.
% 15.84/2.52  smt_solver_time:                        0.
% 15.84/2.52  smt_fast_solver_time:                   0.
% 15.84/2.52  prop_fast_solver_time:                  0.
% 15.84/2.52  prop_unsat_core_time:                   0.002
% 15.84/2.52  
% 15.84/2.52  ------ QBF
% 15.84/2.52  
% 15.84/2.52  qbf_q_res:                              0
% 15.84/2.52  qbf_num_tautologies:                    0
% 15.84/2.52  qbf_prep_cycles:                        0
% 15.84/2.52  
% 15.84/2.52  ------ BMC1
% 15.84/2.52  
% 15.84/2.52  bmc1_current_bound:                     -1
% 15.84/2.52  bmc1_last_solved_bound:                 -1
% 15.84/2.52  bmc1_unsat_core_size:                   -1
% 15.84/2.52  bmc1_unsat_core_parents_size:           -1
% 15.84/2.52  bmc1_merge_next_fun:                    0
% 15.84/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.84/2.52  
% 15.84/2.52  ------ Instantiation
% 15.84/2.52  
% 15.84/2.52  inst_num_of_clauses:                    6013
% 15.84/2.52  inst_num_in_passive:                    2267
% 15.84/2.52  inst_num_in_active:                     1670
% 15.84/2.52  inst_num_in_unprocessed:                2077
% 15.84/2.52  inst_num_of_loops:                      2670
% 15.84/2.52  inst_num_of_learning_restarts:          0
% 15.84/2.52  inst_num_moves_active_passive:          997
% 15.84/2.52  inst_lit_activity:                      0
% 15.84/2.52  inst_lit_activity_moves:                1
% 15.84/2.52  inst_num_tautologies:                   0
% 15.84/2.52  inst_num_prop_implied:                  0
% 15.84/2.52  inst_num_existing_simplified:           0
% 15.84/2.52  inst_num_eq_res_simplified:             0
% 15.84/2.52  inst_num_child_elim:                    0
% 15.84/2.52  inst_num_of_dismatching_blockings:      2897
% 15.84/2.52  inst_num_of_non_proper_insts:           6326
% 15.84/2.52  inst_num_of_duplicates:                 0
% 15.84/2.52  inst_inst_num_from_inst_to_res:         0
% 15.84/2.52  inst_dismatching_checking_time:         0.
% 15.84/2.52  
% 15.84/2.52  ------ Resolution
% 15.84/2.52  
% 15.84/2.52  res_num_of_clauses:                     0
% 15.84/2.52  res_num_in_passive:                     0
% 15.84/2.52  res_num_in_active:                      0
% 15.84/2.52  res_num_of_loops:                       215
% 15.84/2.52  res_forward_subset_subsumed:            396
% 15.84/2.52  res_backward_subset_subsumed:           2
% 15.84/2.52  res_forward_subsumed:                   2
% 15.84/2.52  res_backward_subsumed:                  0
% 15.84/2.52  res_forward_subsumption_resolution:     28
% 15.84/2.52  res_backward_subsumption_resolution:    0
% 15.84/2.52  res_clause_to_clause_subsumption:       32712
% 15.84/2.52  res_orphan_elimination:                 0
% 15.84/2.52  res_tautology_del:                      459
% 15.84/2.52  res_num_eq_res_simplified:              0
% 15.84/2.52  res_num_sel_changes:                    0
% 15.84/2.52  res_moves_from_active_to_pass:          0
% 15.84/2.52  
% 15.84/2.52  ------ Superposition
% 15.84/2.52  
% 15.84/2.52  sup_time_total:                         0.
% 15.84/2.52  sup_time_generating:                    0.
% 15.84/2.52  sup_time_sim_full:                      0.
% 15.84/2.52  sup_time_sim_immed:                     0.
% 15.84/2.52  
% 15.84/2.52  sup_num_of_clauses:                     1026
% 15.84/2.52  sup_num_in_active:                      445
% 15.84/2.52  sup_num_in_passive:                     581
% 15.84/2.52  sup_num_of_loops:                       533
% 15.84/2.52  sup_fw_superposition:                   4572
% 15.84/2.52  sup_bw_superposition:                   1279
% 15.84/2.52  sup_immediate_simplified:               2068
% 15.84/2.52  sup_given_eliminated:                   0
% 15.84/2.52  comparisons_done:                       0
% 15.84/2.52  comparisons_avoided:                    129
% 15.84/2.52  
% 15.84/2.52  ------ Simplifications
% 15.84/2.52  
% 15.84/2.52  
% 15.84/2.52  sim_fw_subset_subsumed:                 161
% 15.84/2.52  sim_bw_subset_subsumed:                 20
% 15.84/2.52  sim_fw_subsumed:                        336
% 15.84/2.52  sim_bw_subsumed:                        40
% 15.84/2.52  sim_fw_subsumption_res:                 35
% 15.84/2.52  sim_bw_subsumption_res:                 19
% 15.84/2.52  sim_tautology_del:                      43
% 15.84/2.52  sim_eq_tautology_del:                   8
% 15.84/2.52  sim_eq_res_simp:                        952
% 15.84/2.52  sim_fw_demodulated:                     1508
% 15.84/2.52  sim_bw_demodulated:                     76
% 15.84/2.52  sim_light_normalised:                   1141
% 15.84/2.52  sim_joinable_taut:                      0
% 15.84/2.52  sim_joinable_simp:                      0
% 15.84/2.52  sim_ac_normalised:                      0
% 15.84/2.52  sim_smt_subsumption:                    0
% 15.84/2.52  
%------------------------------------------------------------------------------
