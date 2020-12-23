%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:52 EST 2020

% Result     : Theorem 35.58s
% Output     : CNFRefutation 35.58s
% Verified   : 
% Statistics : Number of formulae       :  339 (3816 expanded)
%              Number of clauses        :  221 (1324 expanded)
%              Number of leaves         :   37 ( 975 expanded)
%              Depth                    :   26
%              Number of atoms          : 1253 (27023 expanded)
%              Number of equality atoms :  531 (4916 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f133,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f87,f81])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f76,f81])).

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

fof(f46,plain,(
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
    inference(flattening,[],[f46])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f47])).

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
    inference(flattening,[],[f68])).

fof(f70,plain,(
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
    inference(rectify,[],[f69])).

fof(f73,plain,(
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

fof(f72,plain,(
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

fof(f71,plain,
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

fof(f74,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f70,f73,f72,f71])).

fof(f121,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f105,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f104,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f116,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f48,plain,(
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

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f48])).

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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f56,f59,f58,f57])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_xboole_0(X0,X5)
      | ~ r2_hidden(sK2(X0,X1,X2),X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_xboole_0(X0,sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f123,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK7,X3)
      | ~ v3_pre_topc(X3,sK6)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | v1_tops_1(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f122,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f74])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f34,f49,f48])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X1,X2) = X0
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f117,plain,(
    ! [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f40])).

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
    inference(flattening,[],[f61])).

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
    inference(rectify,[],[f62])).

fof(f64,plain,(
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

fof(f65,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f126,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f127,plain,
    ( r1_xboole_0(sK7,sK8)
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f125,plain,
    ( k1_xboole_0 != sK8
    | ~ v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1643,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3560,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1642])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1647,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1705,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1647,c_11])).

cnf(c_4483,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3560,c_1705])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1649,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1715,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1649,c_11])).

cnf(c_7292,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_1715])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1604,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_29,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1625,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2816,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_1625])).

cnf(c_28,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1626,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3174,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_2816,c_1626])).

cnf(c_40,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1614,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3721,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3174,c_1614])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_52,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_53,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_4267,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3721,c_52,c_53])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1633,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_1634,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12235,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1634])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_555,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6583,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_562,c_555])).

cnf(c_556,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4985,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_556,c_555])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5181,plain,
    ( X0 = k2_subset_1(X0) ),
    inference(resolution,[status(thm)],[c_4985,c_6])).

cnf(c_17879,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_6583,c_5181])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18966,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_17879,c_8])).

cnf(c_13800,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
    inference(resolution,[status(thm)],[c_20,c_21])).

cnf(c_18972,plain,
    ( sP0(X0,X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_18966,c_13800])).

cnf(c_18973,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18972])).

cnf(c_47668,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12235,c_18973])).

cnf(c_47669,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47668])).

cnf(c_47676,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4267,c_47669])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1638,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7611,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1638])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1635,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8523,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1635])).

cnf(c_48,negated_conjecture,
    ( v1_tops_1(sK7,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_xboole_0(sK7,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1606,plain,
    ( k1_xboole_0 = X0
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_17152,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8523,c_1606])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2)
    | v3_pre_topc(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1636,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7474,plain,
    ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
    | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1636])).

cnf(c_17313,plain,
    ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top
    | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17152,c_7474])).

cnf(c_17317,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7611,c_17313])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_54,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_105,plain,
    ( l1_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_108,plain,
    ( ~ l1_struct_0(sK6)
    | k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2248,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2249,plain,
    ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_2409,plain,
    ( k2_pre_topc(sK6,sK7) != X0
    | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_2801,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
    | k2_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_1605,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_1645,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1645,c_6])).

cnf(c_27,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1627,plain,
    ( sP1(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8761,plain,
    ( sP1(u1_struct_0(X0),X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1627])).

cnf(c_22533,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_8761])).

cnf(c_569,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_585,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_590,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_2190,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2195,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_2197,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_2209,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2491,plain,
    ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_2494,plain,
    ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2491])).

cnf(c_3848,plain,
    ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2636,plain,
    ( X0 != X1
    | X0 = k2_subset_1(X2)
    | k2_subset_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_3800,plain,
    ( X0 != X1
    | X0 = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_4839,plain,
    ( X0 != u1_struct_0(sK6)
    | X0 = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3800])).

cnf(c_9035,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X0) = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4839])).

cnf(c_9036,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK6)
    | u1_struct_0(sK6) = k2_subset_1(u1_struct_0(sK6))
    | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_9035])).

cnf(c_567,plain,
    ( ~ sP1(X0,X1,X2)
    | sP1(X3,X1,X2)
    | X3 != X0 ),
    theory(equality)).

cnf(c_2794,plain,
    ( sP1(X0,sK6,sK7)
    | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | X0 != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_16521,plain,
    ( sP1(u1_struct_0(X0),sK6,sK7)
    | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
    | u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2794])).

cnf(c_16522,plain,
    ( u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
    | sP1(u1_struct_0(X0),sK6,sK7) = iProver_top
    | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16521])).

cnf(c_16524,plain,
    ( u1_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
    | sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
    | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16522])).

cnf(c_22728,plain,
    ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22533,c_53,c_54,c_585,c_590,c_2197,c_2494,c_3848,c_9036,c_16524])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k2_pre_topc(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1640,plain,
    ( k2_pre_topc(X0,X1) = X2
    | sP1(X2,X0,X1) != iProver_top
    | sP0(X1,X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_22733,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22728,c_1640])).

cnf(c_28119,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | v1_tops_1(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17317,c_50,c_53,c_54,c_105,c_108,c_2249,c_2801,c_22733])).

cnf(c_39,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1615,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4689,plain,
    ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1615])).

cnf(c_4700,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4689,c_3174])).

cnf(c_5387,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4700,c_53])).

cnf(c_5388,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5387])).

cnf(c_28133,plain,
    ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_28119,c_5388])).

cnf(c_17147,plain,
    ( k2_pre_topc(X0,sK3(X1,X0,u1_struct_0(X0))) = k2_struct_0(X0)
    | sP0(X1,X0,u1_struct_0(X0)) = iProver_top
    | v1_tops_1(sK3(X1,X0,u1_struct_0(X0)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8523,c_1615])).

cnf(c_80797,plain,
    ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = k2_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_28133,c_17147])).

cnf(c_80827,plain,
    ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = u1_struct_0(sK6)
    | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | v1_tops_1(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_80797,c_3174])).

cnf(c_2577,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_2891,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2577])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1646,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4733,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1662,c_1646])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1665,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_5])).

cnf(c_4735,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4733,c_1665])).

cnf(c_43,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1611,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_7187,plain,
    ( v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | v3_pre_topc(k1_xboole_0,X0) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4735,c_1611])).

cnf(c_7208,plain,
    ( v4_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK6) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7187])).

cnf(c_41,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1613,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3171,plain,
    ( k2_pre_topc(sK6,k2_struct_0(sK6)) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_1604,c_1613])).

cnf(c_3341,plain,
    ( k2_pre_topc(sK6,u1_struct_0(sK6)) = u1_struct_0(sK6) ),
    inference(demodulation,[status(thm)],[c_3174,c_3171])).

cnf(c_30,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1624,plain,
    ( k2_pre_topc(X0,X1) != X1
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10261,plain,
    ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_1624])).

cnf(c_2251,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_3244,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X0 != k2_subset_1(X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2251])).

cnf(c_3626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X0 != k2_subset_1(X2)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_3244])).

cnf(c_5981,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_16520,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5981])).

cnf(c_16526,plain,
    ( u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16520])).

cnf(c_16528,plain,
    ( u1_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16526])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1637,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_29087,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28133,c_1637])).

cnf(c_12168,plain,
    ( sP0(X0,X1,u1_struct_0(X1))
    | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_55351,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6))
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12168])).

cnf(c_55352,plain,
    ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55351])).

cnf(c_84378,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29087,c_22733,c_55352])).

cnf(c_36,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1618,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1641,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1972,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X3,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1618,c_1641])).

cnf(c_14760,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k2_pre_topc(X0,X2)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_xboole_0(X2,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1972])).

cnf(c_2317,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_11])).

cnf(c_2810,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2317,c_1665])).

cnf(c_4042,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2810,c_1715])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1644,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6419,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1644])).

cnf(c_83477,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14760,c_4042,c_6419])).

cnf(c_83485,plain,
    ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_83477])).

cnf(c_84388,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v3_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_84378,c_83485])).

cnf(c_85017,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
    | v3_pre_topc(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84388])).

cnf(c_85969,plain,
    ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_80827,c_52,c_53,c_585,c_590,c_2197,c_2891,c_3848,c_7208,c_9036,c_10261,c_16528,c_85017])).

cnf(c_47,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1607,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_14762,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1972])).

cnf(c_45,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | v3_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_60,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | v3_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_15762,plain,
    ( r1_xboole_0(X1,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14762,c_53,c_60])).

cnf(c_15763,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_xboole_0(X1,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_15762])).

cnf(c_15776,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r1_xboole_0(sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_15763])).

cnf(c_44,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | r1_xboole_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_61,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r1_xboole_0(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_16216,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15776,c_61])).

cnf(c_16217,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_16216])).

cnf(c_86031,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_85969,c_16217])).

cnf(c_6420,plain,
    ( v1_tops_1(sK7,sK6) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1644])).

cnf(c_86556,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_86031,c_52,c_50,c_53,c_54,c_105,c_108,c_585,c_590,c_2197,c_2249,c_2801,c_2891,c_3848,c_6420,c_7208,c_9036,c_10261,c_16528,c_85017])).

cnf(c_119794,plain,
    ( sP0(X0,sK6,sK8) = iProver_top
    | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_47676,c_86556])).

cnf(c_120984,plain,
    ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7292,c_119794])).

cnf(c_104928,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_120459,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_104928])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1617,plain,
    ( r2_hidden(X0,k2_pre_topc(X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7317,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_1617])).

cnf(c_8135,plain,
    ( v2_struct_0(sK6) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7317,c_53])).

cnf(c_8136,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_8135])).

cnf(c_8145,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8136,c_1662,c_1641])).

cnf(c_8149,plain,
    ( sP0(X0,sK6,X1) = iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_8145])).

cnf(c_8757,plain,
    ( sP1(k1_xboole_0,X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1627])).

cnf(c_19116,plain,
    ( sP1(k1_xboole_0,X0,k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_8757])).

cnf(c_20057,plain,
    ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
    | sP0(k1_xboole_0,X0,k1_xboole_0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19116,c_1640])).

cnf(c_20244,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v2_struct_0(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8149,c_20057])).

cnf(c_2200,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2205,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2200])).

cnf(c_2207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_4730,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1643,c_1646])).

cnf(c_4744,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4730,c_5])).

cnf(c_42,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1612,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_4928,plain,
    ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4744,c_1612])).

cnf(c_4947,plain,
    ( v4_pre_topc(k1_xboole_0,sK6) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4928])).

cnf(c_31,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1623,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7640,plain,
    ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1623])).

cnf(c_7671,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7640])).

cnf(c_101650,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20244,c_52,c_53,c_2207,c_3721,c_4947,c_7671])).

cnf(c_8759,plain,
    ( sP1(sK8,sK6,X0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1627])).

cnf(c_9439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | sP1(sK8,sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8759,c_53])).

cnf(c_9440,plain,
    ( sP1(sK8,sK6,X0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9439])).

cnf(c_9448,plain,
    ( sP1(sK8,sK6,k1_xboole_0) = iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_9440])).

cnf(c_10992,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = sK8
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9448,c_1640])).

cnf(c_101655,plain,
    ( sK8 = k1_xboole_0
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | v1_tops_1(sK7,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_101650,c_10992])).

cnf(c_118000,plain,
    ( sP0(k1_xboole_0,sK6,sK8) != iProver_top
    | sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_101655,c_52,c_50,c_53,c_54,c_105,c_108,c_585,c_590,c_2197,c_2249,c_2801,c_2891,c_3848,c_7208,c_9036,c_10261,c_16528,c_85017])).

cnf(c_118001,plain,
    ( sK8 = k1_xboole_0
    | sP0(k1_xboole_0,sK6,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_118000])).

cnf(c_2983,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_46,negated_conjecture,
    ( ~ v1_tops_1(sK7,sK6)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_120984,c_120459,c_118001,c_85017,c_16528,c_10261,c_9036,c_7208,c_3848,c_2983,c_2891,c_2801,c_2248,c_2197,c_590,c_585,c_108,c_105,c_46,c_49,c_53,c_50,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.58/5.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.58/5.02  
% 35.58/5.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.58/5.02  
% 35.58/5.02  ------  iProver source info
% 35.58/5.02  
% 35.58/5.02  git: date: 2020-06-30 10:37:57 +0100
% 35.58/5.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.58/5.02  git: non_committed_changes: false
% 35.58/5.02  git: last_make_outside_of_git: false
% 35.58/5.02  
% 35.58/5.02  ------ 
% 35.58/5.02  ------ Parsing...
% 35.58/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.58/5.02  
% 35.58/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.58/5.02  
% 35.58/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.58/5.02  
% 35.58/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.58/5.02  ------ Proving...
% 35.58/5.02  ------ Problem Properties 
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  clauses                                 52
% 35.58/5.02  conjectures                             8
% 35.58/5.02  EPR                                     6
% 35.58/5.02  Horn                                    37
% 35.58/5.02  unary                                   10
% 35.58/5.02  binary                                  14
% 35.58/5.02  lits                                    162
% 35.58/5.02  lits eq                                 18
% 35.58/5.02  fd_pure                                 0
% 35.58/5.02  fd_pseudo                               0
% 35.58/5.02  fd_cond                                 1
% 35.58/5.02  fd_pseudo_cond                          1
% 35.58/5.02  AC symbols                              0
% 35.58/5.02  
% 35.58/5.02  ------ Input Options Time Limit: Unbounded
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  ------ 
% 35.58/5.02  Current options:
% 35.58/5.02  ------ 
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  ------ Proving...
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  % SZS status Theorem for theBenchmark.p
% 35.58/5.02  
% 35.58/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 35.58/5.02  
% 35.58/5.02  fof(f11,axiom,(
% 35.58/5.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f86,plain,(
% 35.58/5.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f11])).
% 35.58/5.02  
% 35.58/5.02  fof(f13,axiom,(
% 35.58/5.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f26,plain,(
% 35.58/5.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 35.58/5.02    inference(unused_predicate_definition_removal,[],[f13])).
% 35.58/5.02  
% 35.58/5.02  fof(f30,plain,(
% 35.58/5.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 35.58/5.02    inference(ennf_transformation,[],[f26])).
% 35.58/5.02  
% 35.58/5.02  fof(f88,plain,(
% 35.58/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f30])).
% 35.58/5.02  
% 35.58/5.02  fof(f3,axiom,(
% 35.58/5.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f27,plain,(
% 35.58/5.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.58/5.02    inference(ennf_transformation,[],[f3])).
% 35.58/5.02  
% 35.58/5.02  fof(f78,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f27])).
% 35.58/5.02  
% 35.58/5.02  fof(f6,axiom,(
% 35.58/5.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f81,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f6])).
% 35.58/5.02  
% 35.58/5.02  fof(f131,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.58/5.02    inference(definition_unfolding,[],[f78,f81])).
% 35.58/5.02  
% 35.58/5.02  fof(f12,axiom,(
% 35.58/5.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f87,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f12])).
% 35.58/5.02  
% 35.58/5.02  fof(f133,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.58/5.02    inference(definition_unfolding,[],[f87,f81])).
% 35.58/5.02  
% 35.58/5.02  fof(f1,axiom,(
% 35.58/5.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f51,plain,(
% 35.58/5.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.58/5.02    inference(nnf_transformation,[],[f1])).
% 35.58/5.02  
% 35.58/5.02  fof(f76,plain,(
% 35.58/5.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.58/5.02    inference(cnf_transformation,[],[f51])).
% 35.58/5.02  
% 35.58/5.02  fof(f129,plain,(
% 35.58/5.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.58/5.02    inference(definition_unfolding,[],[f76,f81])).
% 35.58/5.02  
% 35.58/5.02  fof(f24,conjecture,(
% 35.58/5.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f25,negated_conjecture,(
% 35.58/5.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 35.58/5.02    inference(negated_conjecture,[],[f24])).
% 35.58/5.02  
% 35.58/5.02  fof(f46,plain,(
% 35.58/5.02    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 35.58/5.02    inference(ennf_transformation,[],[f25])).
% 35.58/5.02  
% 35.58/5.02  fof(f47,plain,(
% 35.58/5.02    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f46])).
% 35.58/5.02  
% 35.58/5.02  fof(f68,plain,(
% 35.58/5.02    ? [X0] : (? [X1] : (((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.58/5.02    inference(nnf_transformation,[],[f47])).
% 35.58/5.02  
% 35.58/5.02  fof(f69,plain,(
% 35.58/5.02    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f68])).
% 35.58/5.02  
% 35.58/5.02  fof(f70,plain,(
% 35.58/5.02    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.58/5.02    inference(rectify,[],[f69])).
% 35.58/5.02  
% 35.58/5.02  fof(f73,plain,(
% 35.58/5.02    ( ! [X0,X1] : (? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK8) & v3_pre_topc(sK8,X0) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f72,plain,(
% 35.58/5.02    ( ! [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (r1_xboole_0(sK7,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(sK7,X0)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f71,plain,(
% 35.58/5.02    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK6) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(X1,sK6)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f74,plain,(
% 35.58/5.02    (((r1_xboole_0(sK7,sK8) & v3_pre_topc(sK8,sK6) & k1_xboole_0 != sK8 & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) | ~v1_tops_1(sK7,sK6)) & (! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) | v1_tops_1(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 35.58/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f70,f73,f72,f71])).
% 35.58/5.02  
% 35.58/5.02  fof(f121,plain,(
% 35.58/5.02    l1_pre_topc(sK6)),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f17,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f36,plain,(
% 35.58/5.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f17])).
% 35.58/5.02  
% 35.58/5.02  fof(f105,plain,(
% 35.58/5.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f36])).
% 35.58/5.02  
% 35.58/5.02  fof(f16,axiom,(
% 35.58/5.02    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f35,plain,(
% 35.58/5.02    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f16])).
% 35.58/5.02  
% 35.58/5.02  fof(f104,plain,(
% 35.58/5.02    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f35])).
% 35.58/5.02  
% 35.58/5.02  fof(f21,axiom,(
% 35.58/5.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f42,plain,(
% 35.58/5.02    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 35.58/5.02    inference(ennf_transformation,[],[f21])).
% 35.58/5.02  
% 35.58/5.02  fof(f43,plain,(
% 35.58/5.02    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f42])).
% 35.58/5.02  
% 35.58/5.02  fof(f116,plain,(
% 35.58/5.02    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f43])).
% 35.58/5.02  
% 35.58/5.02  fof(f120,plain,(
% 35.58/5.02    v2_pre_topc(sK6)),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f48,plain,(
% 35.58/5.02    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0))))),
% 35.58/5.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 35.58/5.02  
% 35.58/5.02  fof(f54,plain,(
% 35.58/5.02    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2))) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 35.58/5.02    inference(nnf_transformation,[],[f48])).
% 35.58/5.02  
% 35.58/5.02  fof(f55,plain,(
% 35.58/5.02    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2)) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X2))) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 35.58/5.02    inference(flattening,[],[f54])).
% 35.58/5.02  
% 35.58/5.02  fof(f56,plain,(
% 35.58/5.02    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 35.58/5.02    inference(rectify,[],[f55])).
% 35.58/5.02  
% 35.58/5.02  fof(f59,plain,(
% 35.58/5.02    ! [X6,X1,X0] : (? [X7] : (r1_xboole_0(X0,X7) & r2_hidden(X6,X7) & v3_pre_topc(X7,X1) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))))),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f58,plain,(
% 35.58/5.02    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(X3,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f57,plain,(
% 35.58/5.02    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X3,X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(X3,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X3,X2)) & r2_hidden(X3,u1_struct_0(X1))) => ((? [X4] : (r1_xboole_0(X0,X4) & r2_hidden(sK2(X0,X1,X2),X4) & v3_pre_topc(X4,X1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f60,plain,(
% 35.58/5.02    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((r1_xboole_0(X0,sK3(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (! [X5] : (~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1,X2),X2)) & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | (r1_xboole_0(X0,sK4(X0,X1,X6)) & r2_hidden(X6,sK4(X0,X1,X6)) & v3_pre_topc(sK4(X0,X1,X6),X1) & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X8] : (~r1_xboole_0(X0,X8) | ~r2_hidden(X6,X8) | ~v3_pre_topc(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X6,X2))) | ~r2_hidden(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 35.58/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f56,f59,f58,f57])).
% 35.58/5.02  
% 35.58/5.02  fof(f97,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f60])).
% 35.58/5.02  
% 35.58/5.02  fof(f98,plain,(
% 35.58/5.02    ( ! [X2,X0,X5,X1] : (sP0(X0,X1,X2) | ~r1_xboole_0(X0,X5) | ~r2_hidden(sK2(X0,X1,X2),X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f60])).
% 35.58/5.02  
% 35.58/5.02  fof(f7,axiom,(
% 35.58/5.02    ! [X0] : k2_subset_1(X0) = X0),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f82,plain,(
% 35.58/5.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 35.58/5.02    inference(cnf_transformation,[],[f7])).
% 35.58/5.02  
% 35.58/5.02  fof(f9,axiom,(
% 35.58/5.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f84,plain,(
% 35.58/5.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f9])).
% 35.58/5.02  
% 35.58/5.02  fof(f102,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_xboole_0(X0,sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f60])).
% 35.58/5.02  
% 35.58/5.02  fof(f99,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f60])).
% 35.58/5.02  
% 35.58/5.02  fof(f123,plain,(
% 35.58/5.02    ( ! [X3] : (~r1_xboole_0(sK7,X3) | ~v3_pre_topc(X3,sK6) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | v1_tops_1(sK7,sK6)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f100,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f60])).
% 35.58/5.02  
% 35.58/5.02  fof(f122,plain,(
% 35.58/5.02    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f20,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f41,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f20])).
% 35.58/5.02  
% 35.58/5.02  fof(f66,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(nnf_transformation,[],[f41])).
% 35.58/5.02  
% 35.58/5.02  fof(f115,plain,(
% 35.58/5.02    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f66])).
% 35.58/5.02  
% 35.58/5.02  fof(f15,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f33,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f15])).
% 35.58/5.02  
% 35.58/5.02  fof(f34,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f33])).
% 35.58/5.02  
% 35.58/5.02  fof(f49,plain,(
% 35.58/5.02    ! [X2,X0,X1] : ((k2_pre_topc(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 35.58/5.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 35.58/5.02  
% 35.58/5.02  fof(f50,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(definition_folding,[],[f34,f49,f48])).
% 35.58/5.02  
% 35.58/5.02  fof(f103,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f50])).
% 35.58/5.02  
% 35.58/5.02  fof(f52,plain,(
% 35.58/5.02    ! [X2,X0,X1] : (((k2_pre_topc(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_pre_topc(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 35.58/5.02    inference(nnf_transformation,[],[f49])).
% 35.58/5.02  
% 35.58/5.02  fof(f53,plain,(
% 35.58/5.02    ! [X0,X1,X2] : (((k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_pre_topc(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 35.58/5.02    inference(rectify,[],[f52])).
% 35.58/5.02  
% 35.58/5.02  fof(f91,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (k2_pre_topc(X1,X2) = X0 | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f53])).
% 35.58/5.02  
% 35.58/5.02  fof(f114,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f66])).
% 35.58/5.02  
% 35.58/5.02  fof(f8,axiom,(
% 35.58/5.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f28,plain,(
% 35.58/5.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.58/5.02    inference(ennf_transformation,[],[f8])).
% 35.58/5.02  
% 35.58/5.02  fof(f83,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f28])).
% 35.58/5.02  
% 35.58/5.02  fof(f4,axiom,(
% 35.58/5.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f79,plain,(
% 35.58/5.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 35.58/5.02    inference(cnf_transformation,[],[f4])).
% 35.58/5.02  
% 35.58/5.02  fof(f132,plain,(
% 35.58/5.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 35.58/5.02    inference(definition_unfolding,[],[f79,f81])).
% 35.58/5.02  
% 35.58/5.02  fof(f5,axiom,(
% 35.58/5.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f80,plain,(
% 35.58/5.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.58/5.02    inference(cnf_transformation,[],[f5])).
% 35.58/5.02  
% 35.58/5.02  fof(f23,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f45,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f23])).
% 35.58/5.02  
% 35.58/5.02  fof(f67,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(nnf_transformation,[],[f45])).
% 35.58/5.02  
% 35.58/5.02  fof(f118,plain,(
% 35.58/5.02    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f67])).
% 35.58/5.02  
% 35.58/5.02  fof(f22,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f44,plain,(
% 35.58/5.02    ! [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f22])).
% 35.58/5.02  
% 35.58/5.02  fof(f117,plain,(
% 35.58/5.02    ( ! [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f44])).
% 35.58/5.02  
% 35.58/5.02  fof(f18,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f37,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f18])).
% 35.58/5.02  
% 35.58/5.02  fof(f38,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f37])).
% 35.58/5.02  
% 35.58/5.02  fof(f107,plain,(
% 35.58/5.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f38])).
% 35.58/5.02  
% 35.58/5.02  fof(f101,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f60])).
% 35.58/5.02  
% 35.58/5.02  fof(f19,axiom,(
% 35.58/5.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f39,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(ennf_transformation,[],[f19])).
% 35.58/5.02  
% 35.58/5.02  fof(f40,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f39])).
% 35.58/5.02  
% 35.58/5.02  fof(f61,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(nnf_transformation,[],[f40])).
% 35.58/5.02  
% 35.58/5.02  fof(f62,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(flattening,[],[f61])).
% 35.58/5.02  
% 35.58/5.02  fof(f63,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(rectify,[],[f62])).
% 35.58/5.02  
% 35.58/5.02  fof(f64,plain,(
% 35.58/5.02    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 35.58/5.02    introduced(choice_axiom,[])).
% 35.58/5.02  
% 35.58/5.02  fof(f65,plain,(
% 35.58/5.02    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK5(X0,X1,X2)) & r2_hidden(X2,sK5(X0,X1,X2)) & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.58/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).
% 35.58/5.02  
% 35.58/5.02  fof(f109,plain,(
% 35.58/5.02    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f65])).
% 35.58/5.02  
% 35.58/5.02  fof(f14,axiom,(
% 35.58/5.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f31,plain,(
% 35.58/5.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 35.58/5.02    inference(ennf_transformation,[],[f14])).
% 35.58/5.02  
% 35.58/5.02  fof(f32,plain,(
% 35.58/5.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 35.58/5.02    inference(flattening,[],[f31])).
% 35.58/5.02  
% 35.58/5.02  fof(f89,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f32])).
% 35.58/5.02  
% 35.58/5.02  fof(f10,axiom,(
% 35.58/5.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 35.58/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.58/5.02  
% 35.58/5.02  fof(f29,plain,(
% 35.58/5.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.58/5.02    inference(ennf_transformation,[],[f10])).
% 35.58/5.02  
% 35.58/5.02  fof(f85,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.58/5.02    inference(cnf_transformation,[],[f29])).
% 35.58/5.02  
% 35.58/5.02  fof(f124,plain,(
% 35.58/5.02    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) | ~v1_tops_1(sK7,sK6)),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f126,plain,(
% 35.58/5.02    v3_pre_topc(sK8,sK6) | ~v1_tops_1(sK7,sK6)),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f127,plain,(
% 35.58/5.02    r1_xboole_0(sK7,sK8) | ~v1_tops_1(sK7,sK6)),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  fof(f108,plain,(
% 35.58/5.02    ( ! [X2,X0,X1] : (~v2_struct_0(X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f65])).
% 35.58/5.02  
% 35.58/5.02  fof(f119,plain,(
% 35.58/5.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f67])).
% 35.58/5.02  
% 35.58/5.02  fof(f106,plain,(
% 35.58/5.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.58/5.02    inference(cnf_transformation,[],[f38])).
% 35.58/5.02  
% 35.58/5.02  fof(f125,plain,(
% 35.58/5.02    k1_xboole_0 != sK8 | ~v1_tops_1(sK7,sK6)),
% 35.58/5.02    inference(cnf_transformation,[],[f74])).
% 35.58/5.02  
% 35.58/5.02  cnf(c_10,plain,
% 35.58/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f86]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1643,plain,
% 35.58/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_12,plain,
% 35.58/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f88]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1642,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.58/5.02      | r1_tarski(X0,X1) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3560,plain,
% 35.58/5.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_1642]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3,plain,
% 35.58/5.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f131]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1647,plain,
% 35.58/5.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 35.58/5.02      | r1_tarski(X0,X1) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_11,plain,
% 35.58/5.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f133]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1705,plain,
% 35.58/5.02      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 35.58/5.02      | r1_tarski(X0,X1) != iProver_top ),
% 35.58/5.02      inference(demodulation,[status(thm)],[c_1647,c_11]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4483,plain,
% 35.58/5.02      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_3560,c_1705]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1,plain,
% 35.58/5.02      ( r1_xboole_0(X0,X1)
% 35.58/5.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f129]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1649,plain,
% 35.58/5.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 35.58/5.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1715,plain,
% 35.58/5.02      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 35.58/5.02      | r1_xboole_0(X0,X1) = iProver_top ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_1649,c_11]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7292,plain,
% 35.58/5.02      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_4483,c_1715]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_50,negated_conjecture,
% 35.58/5.02      ( l1_pre_topc(sK6) ),
% 35.58/5.02      inference(cnf_transformation,[],[f121]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1604,plain,
% 35.58/5.02      ( l1_pre_topc(sK6) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_29,plain,
% 35.58/5.02      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 35.58/5.02      inference(cnf_transformation,[],[f105]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1625,plain,
% 35.58/5.02      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2816,plain,
% 35.58/5.02      ( l1_struct_0(sK6) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1604,c_1625]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_28,plain,
% 35.58/5.02      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 35.58/5.02      inference(cnf_transformation,[],[f104]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1626,plain,
% 35.58/5.02      ( k2_struct_0(X0) = u1_struct_0(X0)
% 35.58/5.02      | l1_struct_0(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3174,plain,
% 35.58/5.02      ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_2816,c_1626]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_40,plain,
% 35.58/5.02      ( v3_pre_topc(k2_struct_0(X0),X0)
% 35.58/5.02      | ~ v2_pre_topc(X0)
% 35.58/5.02      | ~ l1_pre_topc(X0) ),
% 35.58/5.02      inference(cnf_transformation,[],[f116]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1614,plain,
% 35.58/5.02      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 35.58/5.02      | v2_pre_topc(X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3721,plain,
% 35.58/5.02      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
% 35.58/5.02      | v2_pre_topc(sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_3174,c_1614]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_51,negated_conjecture,
% 35.58/5.02      ( v2_pre_topc(sK6) ),
% 35.58/5.02      inference(cnf_transformation,[],[f120]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_52,plain,
% 35.58/5.02      ( v2_pre_topc(sK6) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_53,plain,
% 35.58/5.02      ( l1_pre_topc(sK6) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4267,plain,
% 35.58/5.02      ( v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_3721,c_52,c_53]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_21,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f97]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1633,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_20,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | ~ v3_pre_topc(X3,X1)
% 35.58/5.02      | ~ r2_hidden(sK2(X0,X1,X2),X3)
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2)
% 35.58/5.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ r1_xboole_0(X0,X3) ),
% 35.58/5.02      inference(cnf_transformation,[],[f98]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1634,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | v3_pre_topc(X3,X1) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 35.58/5.02      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X0,X3) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_12235,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1633,c_1634]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_562,plain,
% 35.58/5.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.58/5.02      theory(equality) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_555,plain,( X0 = X0 ),theory(equality) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_6583,plain,
% 35.58/5.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 35.58/5.02      inference(resolution,[status(thm)],[c_562,c_555]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_556,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4985,plain,
% 35.58/5.02      ( X0 != X1 | X1 = X0 ),
% 35.58/5.02      inference(resolution,[status(thm)],[c_556,c_555]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_6,plain,
% 35.58/5.02      ( k2_subset_1(X0) = X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f82]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_5181,plain,
% 35.58/5.02      ( X0 = k2_subset_1(X0) ),
% 35.58/5.02      inference(resolution,[status(thm)],[c_4985,c_6]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_17879,plain,
% 35.58/5.02      ( m1_subset_1(X0,X1) | ~ m1_subset_1(k2_subset_1(X0),X1) ),
% 35.58/5.02      inference(resolution,[status(thm)],[c_6583,c_5181]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8,plain,
% 35.58/5.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f84]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_18966,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 35.58/5.02      inference(resolution,[status(thm)],[c_17879,c_8]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_13800,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | ~ v3_pre_topc(u1_struct_0(X1),X1)
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2)
% 35.58/5.02      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
% 35.58/5.02      inference(resolution,[status(thm)],[c_20,c_21]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_18972,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | ~ v3_pre_topc(u1_struct_0(X1),X1)
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2)
% 35.58/5.02      | ~ r1_xboole_0(X0,u1_struct_0(X1)) ),
% 35.58/5.02      inference(backward_subsumption_resolution,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_18966,c_13800]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_18973,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 35.58/5.02      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_18972]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_47668,plain,
% 35.58/5.02      ( r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 35.58/5.02      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 35.58/5.02      | sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_12235,c_18973]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_47669,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | v3_pre_topc(u1_struct_0(X1),X1) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 35.58/5.02      | r1_xboole_0(X0,u1_struct_0(X1)) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_47668]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_47676,plain,
% 35.58/5.02      ( sP0(X0,sK6,X1) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,sK6,X1),X1) = iProver_top
% 35.58/5.02      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_4267,c_47669]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 35.58/5.02      | r1_xboole_0(X0,sK3(X0,X1,X2)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f102]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1638,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 35.58/5.02      | r1_xboole_0(X0,sK3(X0,X1,X2)) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7611,plain,
% 35.58/5.02      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 35.58/5.02      | r1_xboole_0(X0,sK3(X0,X1,u1_struct_0(X1))) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1633,c_1638]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_19,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 35.58/5.02      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ),
% 35.58/5.02      inference(cnf_transformation,[],[f99]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1635,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 35.58/5.02      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8523,plain,
% 35.58/5.02      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 35.58/5.02      | m1_subset_1(sK3(X0,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1633,c_1635]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_48,negated_conjecture,
% 35.58/5.02      ( v1_tops_1(sK7,sK6)
% 35.58/5.02      | ~ v3_pre_topc(X0,sK6)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | ~ r1_xboole_0(sK7,X0)
% 35.58/5.02      | k1_xboole_0 = X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f123]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1606,plain,
% 35.58/5.02      ( k1_xboole_0 = X0
% 35.58/5.02      | v1_tops_1(sK7,sK6) = iProver_top
% 35.58/5.02      | v3_pre_topc(X0,sK6) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | r1_xboole_0(sK7,X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_17152,plain,
% 35.58/5.02      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 35.58/5.02      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) = iProver_top
% 35.58/5.02      | v3_pre_topc(sK3(X0,sK6,u1_struct_0(sK6)),sK6) != iProver_top
% 35.58/5.02      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_8523,c_1606]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_18,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | v3_pre_topc(sK3(X0,X1,X2),X1)
% 35.58/5.02      | ~ r2_hidden(sK2(X0,X1,X2),X2) ),
% 35.58/5.02      inference(cnf_transformation,[],[f100]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1636,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | v3_pre_topc(sK3(X0,X1,X2),X1) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7474,plain,
% 35.58/5.02      ( sP0(X0,X1,u1_struct_0(X1)) = iProver_top
% 35.58/5.02      | v3_pre_topc(sK3(X0,X1,u1_struct_0(X1)),X1) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1633,c_1636]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_17313,plain,
% 35.58/5.02      ( sK3(X0,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 35.58/5.02      | sP0(X0,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) = iProver_top
% 35.58/5.02      | r1_xboole_0(sK7,sK3(X0,sK6,u1_struct_0(sK6))) != iProver_top ),
% 35.58/5.02      inference(forward_subsumption_resolution,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_17152,c_7474]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_17317,plain,
% 35.58/5.02      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 35.58/5.02      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_7611,c_17313]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_49,negated_conjecture,
% 35.58/5.02      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 35.58/5.02      inference(cnf_transformation,[],[f122]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_54,plain,
% 35.58/5.02      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_105,plain,
% 35.58/5.02      ( l1_struct_0(sK6) | ~ l1_pre_topc(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_29]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_108,plain,
% 35.58/5.02      ( ~ l1_struct_0(sK6) | k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_28]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_38,plain,
% 35.58/5.02      ( v1_tops_1(X0,X1)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ l1_pre_topc(X1)
% 35.58/5.02      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f115]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2248,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6)
% 35.58/5.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | ~ l1_pre_topc(sK6)
% 35.58/5.02      | k2_pre_topc(sK6,sK7) != k2_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_38]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2249,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) != k2_struct_0(sK6)
% 35.58/5.02      | v1_tops_1(sK7,sK6) = iProver_top
% 35.58/5.02      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_2248]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2409,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) != X0
% 35.58/5.02      | k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 35.58/5.02      | k2_struct_0(sK6) != X0 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_556]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2801,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 35.58/5.02      | k2_pre_topc(sK6,sK7) != u1_struct_0(sK6)
% 35.58/5.02      | k2_struct_0(sK6) != u1_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2409]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1605,plain,
% 35.58/5.02      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1645,plain,
% 35.58/5.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1662,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_1645,c_6]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_27,plain,
% 35.58/5.02      ( sP1(X0,X1,X2)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ l1_pre_topc(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f103]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1627,plain,
% 35.58/5.02      ( sP1(X0,X1,X2) = iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X1) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8761,plain,
% 35.58/5.02      ( sP1(u1_struct_0(X0),X0,X1) = iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1662,c_1627]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_22533,plain,
% 35.58/5.02      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1605,c_8761]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_569,plain,
% 35.58/5.02      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 35.58/5.02      theory(equality) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_585,plain,
% 35.58/5.02      ( u1_struct_0(sK6) = u1_struct_0(sK6) | sK6 != sK6 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_569]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_590,plain,
% 35.58/5.02      ( sK6 = sK6 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_555]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2190,plain,
% 35.58/5.02      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_8]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2195,plain,
% 35.58/5.02      ( m1_subset_1(k2_subset_1(u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_2190]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2197,plain,
% 35.58/5.02      ( m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2195]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2209,plain,
% 35.58/5.02      ( sP1(X0,sK6,sK7)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | ~ l1_pre_topc(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_27]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2491,plain,
% 35.58/5.02      ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 35.58/5.02      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | ~ l1_pre_topc(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2209]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2494,plain,
% 35.58/5.02      ( sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) = iProver_top
% 35.58/5.02      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_2491]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3848,plain,
% 35.58/5.02      ( k2_subset_1(u1_struct_0(sK6)) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_6]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2636,plain,
% 35.58/5.02      ( X0 != X1 | X0 = k2_subset_1(X2) | k2_subset_1(X2) != X1 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_556]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3800,plain,
% 35.58/5.02      ( X0 != X1
% 35.58/5.02      | X0 = k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k2_subset_1(u1_struct_0(sK6)) != X1 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2636]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4839,plain,
% 35.58/5.02      ( X0 != u1_struct_0(sK6)
% 35.58/5.02      | X0 = k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_3800]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_9035,plain,
% 35.58/5.02      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 35.58/5.02      | u1_struct_0(X0) = k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_4839]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_9036,plain,
% 35.58/5.02      ( u1_struct_0(sK6) != u1_struct_0(sK6)
% 35.58/5.02      | u1_struct_0(sK6) = k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k2_subset_1(u1_struct_0(sK6)) != u1_struct_0(sK6) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_9035]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_567,plain,
% 35.58/5.02      ( ~ sP1(X0,X1,X2) | sP1(X3,X1,X2) | X3 != X0 ),
% 35.58/5.02      theory(equality) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2794,plain,
% 35.58/5.02      ( sP1(X0,sK6,sK7)
% 35.58/5.02      | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 35.58/5.02      | X0 != k2_subset_1(u1_struct_0(sK6)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_567]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16521,plain,
% 35.58/5.02      ( sP1(u1_struct_0(X0),sK6,sK7)
% 35.58/5.02      | ~ sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7)
% 35.58/5.02      | u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2794]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16522,plain,
% 35.58/5.02      ( u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | sP1(u1_struct_0(X0),sK6,sK7) = iProver_top
% 35.58/5.02      | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_16521]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16524,plain,
% 35.58/5.02      ( u1_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top
% 35.58/5.02      | sP1(k2_subset_1(u1_struct_0(sK6)),sK6,sK7) != iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_16522]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_22728,plain,
% 35.58/5.02      ( sP1(u1_struct_0(sK6),sK6,sK7) = iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_22533,c_53,c_54,c_585,c_590,c_2197,c_2494,c_3848,
% 35.58/5.02                 c_9036,c_16524]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_14,plain,
% 35.58/5.02      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | k2_pre_topc(X1,X2) = X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f91]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1640,plain,
% 35.58/5.02      ( k2_pre_topc(X0,X1) = X2
% 35.58/5.02      | sP1(X2,X0,X1) != iProver_top
% 35.58/5.02      | sP0(X1,X0,X2) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_22733,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | sP0(sK7,sK6,u1_struct_0(sK6)) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_22728,c_1640]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_28119,plain,
% 35.58/5.02      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 35.58/5.02      | v1_tops_1(sK7,sK6) = iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_17317,c_50,c_53,c_54,c_105,c_108,c_2249,c_2801,
% 35.58/5.02                 c_22733]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_39,plain,
% 35.58/5.02      ( ~ v1_tops_1(X0,X1)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ l1_pre_topc(X1)
% 35.58/5.02      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f114]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1615,plain,
% 35.58/5.02      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 35.58/5.02      | v1_tops_1(X1,X0) != iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4689,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = k2_struct_0(sK6)
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1605,c_1615]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4700,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_4689,c_3174]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_5387,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_4700,c_53]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_5388,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_5387]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_28133,plain,
% 35.58/5.02      ( sK3(sK7,sK6,u1_struct_0(sK6)) = k1_xboole_0
% 35.58/5.02      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_28119,c_5388]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_17147,plain,
% 35.58/5.02      ( k2_pre_topc(X0,sK3(X1,X0,u1_struct_0(X0))) = k2_struct_0(X0)
% 35.58/5.02      | sP0(X1,X0,u1_struct_0(X0)) = iProver_top
% 35.58/5.02      | v1_tops_1(sK3(X1,X0,u1_struct_0(X0)),X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_8523,c_1615]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_80797,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = k2_struct_0(sK6)
% 35.58/5.02      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | v1_tops_1(k1_xboole_0,sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_28133,c_17147]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_80827,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK3(sK7,sK6,u1_struct_0(sK6))) = u1_struct_0(sK6)
% 35.58/5.02      | k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | v1_tops_1(k1_xboole_0,sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_80797,c_3174]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2577,plain,
% 35.58/5.02      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_555]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2891,plain,
% 35.58/5.02      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2577]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7,plain,
% 35.58/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.58/5.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 35.58/5.02      inference(cnf_transformation,[],[f83]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1646,plain,
% 35.58/5.02      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4733,plain,
% 35.58/5.02      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1662,c_1646]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4,plain,
% 35.58/5.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f132]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_5,plain,
% 35.58/5.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f80]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1665,plain,
% 35.58/5.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_4,c_5]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4735,plain,
% 35.58/5.02      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_4733,c_1665]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_43,plain,
% 35.58/5.02      ( ~ v4_pre_topc(X0,X1)
% 35.58/5.02      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ l1_pre_topc(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f118]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1611,plain,
% 35.58/5.02      ( v4_pre_topc(X0,X1) != iProver_top
% 35.58/5.02      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X1) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7187,plain,
% 35.58/5.02      ( v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 35.58/5.02      | v3_pre_topc(k1_xboole_0,X0) = iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_4735,c_1611]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7208,plain,
% 35.58/5.02      ( v4_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 35.58/5.02      | v3_pre_topc(k1_xboole_0,sK6) = iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_7187]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_41,plain,
% 35.58/5.02      ( ~ l1_pre_topc(X0)
% 35.58/5.02      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 35.58/5.02      inference(cnf_transformation,[],[f117]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1613,plain,
% 35.58/5.02      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3171,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,k2_struct_0(sK6)) = k2_struct_0(sK6) ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1604,c_1613]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3341,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,u1_struct_0(sK6)) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(demodulation,[status(thm)],[c_3174,c_3171]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_30,plain,
% 35.58/5.02      ( v4_pre_topc(X0,X1)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ v2_pre_topc(X1)
% 35.58/5.02      | ~ l1_pre_topc(X1)
% 35.58/5.02      | k2_pre_topc(X1,X0) != X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f107]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1624,plain,
% 35.58/5.02      ( k2_pre_topc(X0,X1) != X1
% 35.58/5.02      | v4_pre_topc(X1,X0) = iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | v2_pre_topc(X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_10261,plain,
% 35.58/5.02      ( v4_pre_topc(u1_struct_0(sK6),sK6) = iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | v2_pre_topc(sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_3341,c_1624]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2251,plain,
% 35.58/5.02      ( m1_subset_1(X0,X1)
% 35.58/5.02      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 35.58/5.02      | X1 != k1_zfmisc_1(X2)
% 35.58/5.02      | X0 != k2_subset_1(X2) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_562]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3244,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.58/5.02      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 35.58/5.02      | X0 != k2_subset_1(X2)
% 35.58/5.02      | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2251]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_3626,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 35.58/5.02      | X0 != k2_subset_1(X2)
% 35.58/5.02      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_3244]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_5981,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | X0 != k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_3626]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16520,plain,
% 35.58/5.02      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 35.58/5.02      | u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_5981]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16526,plain,
% 35.58/5.02      ( u1_struct_0(X0) != k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK6))
% 35.58/5.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 35.58/5.02      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_16520]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16528,plain,
% 35.58/5.02      ( u1_struct_0(sK6) != k2_subset_1(u1_struct_0(sK6))
% 35.58/5.02      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 35.58/5.02      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 35.58/5.02      | m1_subset_1(k2_subset_1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_16526]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_17,plain,
% 35.58/5.02      ( sP0(X0,X1,X2)
% 35.58/5.02      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f101]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1637,plain,
% 35.58/5.02      ( sP0(X0,X1,X2) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),X2) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_29087,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_28133,c_1637]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_12168,plain,
% 35.58/5.02      ( sP0(X0,X1,u1_struct_0(X1))
% 35.58/5.02      | r2_hidden(sK2(X0,X1,u1_struct_0(X1)),u1_struct_0(X1)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_21]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_55351,plain,
% 35.58/5.02      ( sP0(sK7,sK6,u1_struct_0(sK6))
% 35.58/5.02      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_12168]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_55352,plain,
% 35.58/5.02      ( sP0(sK7,sK6,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_55351]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_84378,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | r2_hidden(sK2(sK7,sK6,u1_struct_0(sK6)),k1_xboole_0) = iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_29087,c_22733,c_55352]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_36,plain,
% 35.58/5.02      ( ~ v3_pre_topc(X0,X1)
% 35.58/5.02      | ~ r2_hidden(X2,X0)
% 35.58/5.02      | ~ r2_hidden(X2,k2_pre_topc(X1,X3))
% 35.58/5.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.58/5.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ r1_xboole_0(X3,X0)
% 35.58/5.02      | ~ l1_pre_topc(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f109]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1618,plain,
% 35.58/5.02      ( v3_pre_topc(X0,X1) != iProver_top
% 35.58/5.02      | r2_hidden(X2,X0) != iProver_top
% 35.58/5.02      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 35.58/5.02      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X3,X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X1) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_13,plain,
% 35.58/5.02      ( ~ r2_hidden(X0,X1)
% 35.58/5.02      | m1_subset_1(X0,X2)
% 35.58/5.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f89]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1641,plain,
% 35.58/5.02      ( r2_hidden(X0,X1) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,X2) = iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1972,plain,
% 35.58/5.02      ( v3_pre_topc(X0,X1) != iProver_top
% 35.58/5.02      | r2_hidden(X2,X0) != iProver_top
% 35.58/5.02      | r2_hidden(X2,k2_pre_topc(X1,X3)) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X3,X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X1) != iProver_top ),
% 35.58/5.02      inference(forward_subsumption_resolution,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_1618,c_1641]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_14760,plain,
% 35.58/5.02      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 35.58/5.02      | r2_hidden(X1,k2_pre_topc(X0,X2)) != iProver_top
% 35.58/5.02      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 35.58/5.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X2,k1_xboole_0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_1972]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2317,plain,
% 35.58/5.02      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_5,c_11]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2810,plain,
% 35.58/5.02      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_2317,c_1665]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4042,plain,
% 35.58/5.02      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_2810,c_1715]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_9,plain,
% 35.58/5.02      ( ~ r2_hidden(X0,X1)
% 35.58/5.02      | r2_hidden(X0,X2)
% 35.58/5.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 35.58/5.02      inference(cnf_transformation,[],[f85]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1644,plain,
% 35.58/5.02      ( r2_hidden(X0,X1) != iProver_top
% 35.58/5.02      | r2_hidden(X0,X2) = iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_6419,plain,
% 35.58/5.02      ( r2_hidden(X0,X1) = iProver_top
% 35.58/5.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_1644]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_83477,plain,
% 35.58/5.02      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 35.58/5.02      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 35.58/5.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(forward_subsumption_resolution,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_14760,c_4042,c_6419]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_83485,plain,
% 35.58/5.02      ( v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 35.58/5.02      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1662,c_83477]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_84388,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | v3_pre_topc(k1_xboole_0,X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_84378,c_83485]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_85017,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6)
% 35.58/5.02      | v3_pre_topc(k1_xboole_0,sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_84388]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_85969,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,sK7) = u1_struct_0(sK6) ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_80827,c_52,c_53,c_585,c_590,c_2197,c_2891,c_3848,
% 35.58/5.02                 c_7208,c_9036,c_10261,c_16528,c_85017]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_47,negated_conjecture,
% 35.58/5.02      ( ~ v1_tops_1(sK7,sK6)
% 35.58/5.02      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 35.58/5.02      inference(cnf_transformation,[],[f124]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1607,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_14762,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | v3_pre_topc(sK8,sK6) != iProver_top
% 35.58/5.02      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X1,sK8) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1607,c_1972]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_45,negated_conjecture,
% 35.58/5.02      ( ~ v1_tops_1(sK7,sK6) | v3_pre_topc(sK8,sK6) ),
% 35.58/5.02      inference(cnf_transformation,[],[f126]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_60,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | v3_pre_topc(sK8,sK6) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_15762,plain,
% 35.58/5.02      ( r1_xboole_0(X1,sK8) != iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top
% 35.58/5.02      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_14762,c_53,c_60]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_15763,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | r2_hidden(X0,k2_pre_topc(sK6,X1)) != iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | r1_xboole_0(X1,sK8) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_15762]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_15776,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top
% 35.58/5.02      | r1_xboole_0(sK7,sK8) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1605,c_15763]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_44,negated_conjecture,
% 35.58/5.02      ( ~ v1_tops_1(sK7,sK6) | r1_xboole_0(sK7,sK8) ),
% 35.58/5.02      inference(cnf_transformation,[],[f127]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_61,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | r1_xboole_0(sK7,sK8) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16216,plain,
% 35.58/5.02      ( r2_hidden(X0,sK8) != iProver_top
% 35.58/5.02      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_15776,c_61]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_16217,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | r2_hidden(X0,k2_pre_topc(sK6,sK7)) != iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_16216]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_86031,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top ),
% 35.58/5.02      inference(demodulation,[status(thm)],[c_85969,c_16217]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_6420,plain,
% 35.58/5.02      ( v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 35.58/5.02      | r2_hidden(X0,sK8) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1607,c_1644]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_86556,plain,
% 35.58/5.02      ( r2_hidden(X0,sK8) != iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_86031,c_52,c_50,c_53,c_54,c_105,c_108,c_585,c_590,
% 35.58/5.02                 c_2197,c_2249,c_2801,c_2891,c_3848,c_6420,c_7208,c_9036,
% 35.58/5.02                 c_10261,c_16528,c_85017]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_119794,plain,
% 35.58/5.02      ( sP0(X0,sK6,sK8) = iProver_top
% 35.58/5.02      | r1_xboole_0(X0,u1_struct_0(sK6)) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_47676,c_86556]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_120984,plain,
% 35.58/5.02      ( sP0(k1_xboole_0,sK6,sK8) = iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_7292,c_119794]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_104928,plain,
% 35.58/5.02      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_556]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_120459,plain,
% 35.58/5.02      ( sK8 != k1_xboole_0
% 35.58/5.02      | k1_xboole_0 = sK8
% 35.58/5.02      | k1_xboole_0 != k1_xboole_0 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_104928]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_37,plain,
% 35.58/5.02      ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
% 35.58/5.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.58/5.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ v2_struct_0(X1)
% 35.58/5.02      | ~ l1_pre_topc(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f108]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1617,plain,
% 35.58/5.02      ( r2_hidden(X0,k2_pre_topc(X1,X2)) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 35.58/5.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | v2_struct_0(X1) != iProver_top
% 35.58/5.02      | l1_pre_topc(X1) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7317,plain,
% 35.58/5.02      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | v2_struct_0(sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_3341,c_1617]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8135,plain,
% 35.58/5.02      ( v2_struct_0(sK6) != iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_7317,c_53]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8136,plain,
% 35.58/5.02      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | v2_struct_0(sK6) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_8135]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8145,plain,
% 35.58/5.02      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 35.58/5.02      | v2_struct_0(sK6) != iProver_top ),
% 35.58/5.02      inference(forward_subsumption_resolution,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_8136,c_1662,c_1641]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8149,plain,
% 35.58/5.02      ( sP0(X0,sK6,X1) = iProver_top | v2_struct_0(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1633,c_8145]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8757,plain,
% 35.58/5.02      ( sP1(k1_xboole_0,X0,X1) = iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_1627]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_19116,plain,
% 35.58/5.02      ( sP1(k1_xboole_0,X0,k1_xboole_0) = iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_8757]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_20057,plain,
% 35.58/5.02      ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
% 35.58/5.02      | sP0(k1_xboole_0,X0,k1_xboole_0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_19116,c_1640]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_20244,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 35.58/5.02      | v2_struct_0(sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_8149,c_20057]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2200,plain,
% 35.58/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_10]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2205,plain,
% 35.58/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_2200]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2207,plain,
% 35.58/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_2205]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4730,plain,
% 35.58/5.02      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_1646]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4744,plain,
% 35.58/5.02      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 35.58/5.02      inference(light_normalisation,[status(thm)],[c_4730,c_5]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_42,plain,
% 35.58/5.02      ( v4_pre_topc(X0,X1)
% 35.58/5.02      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ l1_pre_topc(X1) ),
% 35.58/5.02      inference(cnf_transformation,[],[f119]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1612,plain,
% 35.58/5.02      ( v4_pre_topc(X0,X1) = iProver_top
% 35.58/5.02      | v3_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X1) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4928,plain,
% 35.58/5.02      ( v4_pre_topc(k1_xboole_0,X0) = iProver_top
% 35.58/5.02      | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 35.58/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_4744,c_1612]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_4947,plain,
% 35.58/5.02      ( v4_pre_topc(k1_xboole_0,sK6) = iProver_top
% 35.58/5.02      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 35.58/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_4928]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_31,plain,
% 35.58/5.02      ( ~ v4_pre_topc(X0,X1)
% 35.58/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.58/5.02      | ~ l1_pre_topc(X1)
% 35.58/5.02      | k2_pre_topc(X1,X0) = X0 ),
% 35.58/5.02      inference(cnf_transformation,[],[f106]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_1623,plain,
% 35.58/5.02      ( k2_pre_topc(X0,X1) = X1
% 35.58/5.02      | v4_pre_topc(X1,X0) != iProver_top
% 35.58/5.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7640,plain,
% 35.58/5.02      ( k2_pre_topc(X0,k1_xboole_0) = k1_xboole_0
% 35.58/5.02      | v4_pre_topc(k1_xboole_0,X0) != iProver_top
% 35.58/5.02      | l1_pre_topc(X0) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_1623]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_7671,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 35.58/5.02      | v4_pre_topc(k1_xboole_0,sK6) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_7640]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_101650,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_20244,c_52,c_53,c_2207,c_3721,c_4947,c_7671]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_8759,plain,
% 35.58/5.02      ( sP1(sK8,sK6,X0) = iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | l1_pre_topc(sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1607,c_1627]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_9439,plain,
% 35.58/5.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | sP1(sK8,sK6,X0) = iProver_top ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_8759,c_53]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_9440,plain,
% 35.58/5.02      ( sP1(sK8,sK6,X0) = iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top
% 35.58/5.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_9439]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_9448,plain,
% 35.58/5.02      ( sP1(sK8,sK6,k1_xboole_0) = iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_1643,c_9440]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_10992,plain,
% 35.58/5.02      ( k2_pre_topc(sK6,k1_xboole_0) = sK8
% 35.58/5.02      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top ),
% 35.58/5.02      inference(superposition,[status(thm)],[c_9448,c_1640]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_101655,plain,
% 35.58/5.02      ( sK8 = k1_xboole_0
% 35.58/5.02      | sP0(k1_xboole_0,sK6,sK8) != iProver_top
% 35.58/5.02      | v1_tops_1(sK7,sK6) != iProver_top ),
% 35.58/5.02      inference(demodulation,[status(thm)],[c_101650,c_10992]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_118000,plain,
% 35.58/5.02      ( sP0(k1_xboole_0,sK6,sK8) != iProver_top | sK8 = k1_xboole_0 ),
% 35.58/5.02      inference(global_propositional_subsumption,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_101655,c_52,c_50,c_53,c_54,c_105,c_108,c_585,c_590,
% 35.58/5.02                 c_2197,c_2249,c_2801,c_2891,c_3848,c_7208,c_9036,
% 35.58/5.02                 c_10261,c_16528,c_85017]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_118001,plain,
% 35.58/5.02      ( sK8 = k1_xboole_0 | sP0(k1_xboole_0,sK6,sK8) != iProver_top ),
% 35.58/5.02      inference(renaming,[status(thm)],[c_118000]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_2983,plain,
% 35.58/5.02      ( k1_xboole_0 = k1_xboole_0 ),
% 35.58/5.02      inference(instantiation,[status(thm)],[c_555]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(c_46,negated_conjecture,
% 35.58/5.02      ( ~ v1_tops_1(sK7,sK6) | k1_xboole_0 != sK8 ),
% 35.58/5.02      inference(cnf_transformation,[],[f125]) ).
% 35.58/5.02  
% 35.58/5.02  cnf(contradiction,plain,
% 35.58/5.02      ( $false ),
% 35.58/5.02      inference(minisat,
% 35.58/5.02                [status(thm)],
% 35.58/5.02                [c_120984,c_120459,c_118001,c_85017,c_16528,c_10261,
% 35.58/5.02                 c_9036,c_7208,c_3848,c_2983,c_2891,c_2801,c_2248,c_2197,
% 35.58/5.02                 c_590,c_585,c_108,c_105,c_46,c_49,c_53,c_50,c_52]) ).
% 35.58/5.02  
% 35.58/5.02  
% 35.58/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 35.58/5.02  
% 35.58/5.02  ------                               Statistics
% 35.58/5.02  
% 35.58/5.02  ------ Selected
% 35.58/5.02  
% 35.58/5.02  total_time:                             4.156
% 35.58/5.02  
%------------------------------------------------------------------------------
