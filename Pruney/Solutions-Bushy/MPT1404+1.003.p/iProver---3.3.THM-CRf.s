%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1404+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:39 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  252 (1946 expanded)
%              Number of clauses        :  156 ( 430 expanded)
%              Number of leaves         :   26 ( 565 expanded)
%              Depth                    :   23
%              Number of atoms          : 1137 (16187 expanded)
%              Number of equality atoms :  145 ( 284 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(nnf_transformation,[],[f44])).

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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f54,f53,f52])).

fof(f71,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X0,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_connsp_2(X3,X0,X2)
                     => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f62])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X3,X1)
          & m1_connsp_2(X3,X0,X2) )
     => ( r1_xboole_0(sK10,X1)
        & m1_connsp_2(sK10,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X3,X1)
                & m1_connsp_2(X3,X0,X2) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X4,X1)
                | ~ m1_connsp_2(X4,X0,X2) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( r1_xboole_0(X3,X1)
              & m1_connsp_2(X3,X0,sK9) )
          | ~ r2_hidden(sK9,k2_pre_topc(X0,X1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X4,X1)
              | ~ m1_connsp_2(X4,X0,sK9) )
          | r2_hidden(sK9,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X3,sK8)
                  & m1_connsp_2(X3,X0,X2) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK8)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X4,sK8)
                  | ~ m1_connsp_2(X4,X0,X2) )
              | r2_hidden(X2,k2_pre_topc(X0,sK8)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,sK7,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(sK7,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,sK7,X2) )
                | r2_hidden(X2,k2_pre_topc(sK7,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ( r1_xboole_0(sK10,sK8)
        & m1_connsp_2(sK10,sK7,sK9) )
      | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(X4,sK8)
          | ~ m1_connsp_2(X4,sK7,sK9) )
      | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) )
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f63,f67,f66,f65,f64])).

fof(f100,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f7,f59])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,sK8)
      | ~ m1_connsp_2(X4,sK7,sK9)
      | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f99,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f68])).

fof(f101,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f68])).

fof(f1,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f45,f44])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X0,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK5(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK5(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f57])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK5(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,
    ( m1_connsp_2(sK10,sK7,sK9)
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(cnf_transformation,[],[f68])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,
    ( r1_xboole_0(sK10,sK8)
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4167,plain,
    ( ~ sP0(X0_53,X0_54,X1_53)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(X0_54)))
    | ~ v3_pre_topc(X2_53,X0_54)
    | ~ r2_hidden(X3_53,X2_53)
    | ~ r2_hidden(X3_53,X1_53)
    | ~ r2_hidden(X3_53,u1_struct_0(X0_54))
    | ~ r1_xboole_0(X0_53,X2_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4951,plain,
    ( ~ sP0(X0_53,sK7,k2_pre_topc(sK7,X0_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(X1_53,sK7)
    | ~ r2_hidden(X2_53,X1_53)
    | ~ r2_hidden(X2_53,k2_pre_topc(sK7,X0_53))
    | ~ r2_hidden(X2_53,u1_struct_0(sK7))
    | ~ r1_xboole_0(X0_53,X1_53) ),
    inference(instantiation,[status(thm)],[c_4167])).

cnf(c_5479,plain,
    ( ~ sP0(X0_53,sK7,k2_pre_topc(sK7,X0_53))
    | ~ m1_subset_1(k1_tops_1(sK7,X1_53),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(k1_tops_1(sK7,X1_53),sK7)
    | ~ r2_hidden(X2_53,k1_tops_1(sK7,X1_53))
    | ~ r2_hidden(X2_53,k2_pre_topc(sK7,X0_53))
    | ~ r2_hidden(X2_53,u1_struct_0(sK7))
    | ~ r1_xboole_0(X0_53,k1_tops_1(sK7,X1_53)) ),
    inference(instantiation,[status(thm)],[c_4951])).

cnf(c_6988,plain,
    ( ~ sP0(X0_53,sK7,k2_pre_topc(sK7,X0_53))
    | ~ m1_subset_1(k1_tops_1(sK7,X1_53),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(k1_tops_1(sK7,X1_53),sK7)
    | ~ r2_hidden(sK9,k1_tops_1(sK7,X1_53))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,X0_53))
    | ~ r2_hidden(sK9,u1_struct_0(sK7))
    | ~ r1_xboole_0(X0_53,k1_tops_1(sK7,X1_53)) ),
    inference(instantiation,[status(thm)],[c_5479])).

cnf(c_11592,plain,
    ( ~ sP0(sK8,sK7,k2_pre_topc(sK7,sK8))
    | ~ m1_subset_1(k1_tops_1(sK7,sK10),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(k1_tops_1(sK7,sK10),sK7)
    | ~ r2_hidden(sK9,k1_tops_1(sK7,sK10))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r2_hidden(sK9,u1_struct_0(sK7))
    | ~ r1_xboole_0(sK8,k1_tops_1(sK7,sK10)) ),
    inference(instantiation,[status(thm)],[c_6988])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(k1_tops_1(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_4153,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(k1_tops_1(sK7,X0_53),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_9336,plain,
    ( m1_subset_1(k1_tops_1(sK7,sK10),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_4153])).

cnf(c_20,plain,
    ( m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4166,plain,
    ( m1_subset_1(sK6(X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4794,plain,
    ( m1_subset_1(sK6(X0_53),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4166])).

cnf(c_31,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK7,sK9)
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0,sK8) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_591,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_592,plain,
    ( m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k1_tops_1(sK7,X0))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_596,plain,
    ( m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k1_tops_1(sK7,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_35,c_34])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k1_tops_1(sK7,X0))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X2,sK8)
    | X0 != X2
    | sK7 != sK7
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_596])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ r2_hidden(sK9,k1_tops_1(sK7,X0))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0,sK8) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(sK9,k1_tops_1(sK7,X0))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_32])).

cnf(c_4149,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(sK9,k1_tops_1(sK7,X0_53))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0_53,sK8) ),
    inference(subtyping,[status(esa)],[c_821])).

cnf(c_4811,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK9,k1_tops_1(sK7,X0_53)) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r1_xboole_0(X0_53,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4149])).

cnf(c_6249,plain,
    ( r2_hidden(sK9,k1_tops_1(sK7,sK6(k1_zfmisc_1(u1_struct_0(sK7))))) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r1_xboole_0(sK6(k1_zfmisc_1(u1_struct_0(sK7))),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4794,c_4811])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_491,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X1 != X3
    | X0 != X4
    | k2_pre_topc(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1])).

cnf(c_492,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_17])).

cnf(c_497,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_496])).

cnf(c_676,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_497,c_34])).

cnf(c_677,plain,
    ( sP0(X0,sK7,k2_pre_topc(sK7,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_4157,plain,
    ( sP0(X0_53,sK7,k2_pre_topc(sK7,X0_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(subtyping,[status(esa)],[c_677])).

cnf(c_4251,plain,
    ( sP0(X0_53,sK7,k2_pre_topc(sK7,X0_53)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4157])).

cnf(c_4253,plain,
    ( sP0(sK8,sK7,k2_pre_topc(sK7,sK8)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4171,plain,
    ( ~ sP0(X0_53,X0_54,X1_53)
    | r2_hidden(X2_53,X1_53)
    | ~ r2_hidden(X2_53,u1_struct_0(X0_54))
    | r1_xboole_0(X0_53,sK4(X0_53,X0_54,X2_53)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4880,plain,
    ( ~ sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r2_hidden(sK9,u1_struct_0(X0_54))
    | r1_xboole_0(X0_53,sK4(X0_53,X0_54,sK9)) ),
    inference(instantiation,[status(thm)],[c_4171])).

cnf(c_4881,plain,
    ( sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(X0_54)) != iProver_top
    | r1_xboole_0(X0_53,sK4(X0_53,X0_54,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4880])).

cnf(c_4883,plain,
    ( sP0(sK8,sK7,k2_pre_topc(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK7)) != iProver_top
    | r1_xboole_0(sK8,sK4(sK8,sK7,sK9)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4881])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X3,sK4(X0,X1,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4170,plain,
    ( ~ sP0(X0_53,X0_54,X1_53)
    | r2_hidden(X2_53,X1_53)
    | r2_hidden(X2_53,sK4(X0_53,X0_54,X2_53))
    | ~ r2_hidden(X2_53,u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4879,plain,
    ( ~ sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8))
    | r2_hidden(sK9,sK4(X0_53,X0_54,sK9))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r2_hidden(sK9,u1_struct_0(X0_54)) ),
    inference(instantiation,[status(thm)],[c_4170])).

cnf(c_4885,plain,
    ( sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,sK4(X0_53,X0_54,sK9)) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4879])).

cnf(c_4887,plain,
    ( sP0(sK8,sK7,k2_pre_topc(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,sK4(sK8,sK7,sK9)) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4885])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v3_pre_topc(sK4(X0,X1,X3),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4169,plain,
    ( ~ sP0(X0_53,X0_54,X1_53)
    | v3_pre_topc(sK4(X0_53,X0_54,X2_53),X0_54)
    | r2_hidden(X2_53,X1_53)
    | ~ r2_hidden(X2_53,u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4878,plain,
    ( ~ sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8))
    | v3_pre_topc(sK4(X0_53,X0_54,sK9),X0_54)
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r2_hidden(sK9,u1_struct_0(X0_54)) ),
    inference(instantiation,[status(thm)],[c_4169])).

cnf(c_4889,plain,
    ( sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8)) != iProver_top
    | v3_pre_topc(sK4(X0_53,X0_54,sK9),X0_54) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4878])).

cnf(c_4891,plain,
    ( sP0(sK8,sK7,k2_pre_topc(sK7,sK8)) != iProver_top
    | v3_pre_topc(sK4(sK8,sK7,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4168,plain,
    ( ~ sP0(X0_53,X0_54,X1_53)
    | m1_subset_1(sK4(X0_53,X0_54,X2_53),k1_zfmisc_1(u1_struct_0(X0_54)))
    | r2_hidden(X2_53,X1_53)
    | ~ r2_hidden(X2_53,u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4877,plain,
    ( ~ sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8))
    | m1_subset_1(sK4(X0_53,X0_54,sK9),k1_zfmisc_1(u1_struct_0(X0_54)))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r2_hidden(sK9,u1_struct_0(X0_54)) ),
    inference(instantiation,[status(thm)],[c_4168])).

cnf(c_4893,plain,
    ( sP0(X0_53,X0_54,k2_pre_topc(sK7,sK8)) != iProver_top
    | m1_subset_1(sK4(X0_53,X0_54,sK9),k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4877])).

cnf(c_4895,plain,
    ( sP0(sK8,sK7,k2_pre_topc(sK7,sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4893])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4164,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | r2_hidden(X0_53,X1_53)
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_5003,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(X0_54))
    | r2_hidden(sK9,u1_struct_0(X0_54))
    | v1_xboole_0(u1_struct_0(X0_54)) ),
    inference(instantiation,[status(thm)],[c_4164])).

cnf(c_5004,plain,
    ( m1_subset_1(sK9,u1_struct_0(X0_54)) != iProver_top
    | r2_hidden(sK9,u1_struct_0(X0_54)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5003])).

cnf(c_5006,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK9,u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5004])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_570,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_571,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_575,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_35,c_34])).

cnf(c_19,plain,
    ( m1_connsp_2(sK5(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_615,plain,
    ( m1_connsp_2(sK5(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_616,plain,
    ( m1_connsp_2(sK5(sK7,X0),sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_620,plain,
    ( m1_connsp_2(sK5(sK7,X0),sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_35,c_34])).

cnf(c_881,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | X1 != X2
    | sK5(sK7,X1) != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_620])).

cnf(c_882,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_4146,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0_53),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(subtyping,[status(esa)],[c_882])).

cnf(c_5059,plain,
    ( m1_subset_1(sK5(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4146])).

cnf(c_5060,plain,
    ( m1_subset_1(sK5(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5059])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_222,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_18])).

cnf(c_522,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_36])).

cnf(c_523,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k1_tops_1(sK7,X0))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k1_tops_1(sK7,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_35,c_34])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k1_tops_1(sK7,X2))
    | X0 != X1
    | sK5(sK7,X0) != X2
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_527,c_620])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(X0,k1_tops_1(sK7,sK5(sK7,X0))) ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_4145,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK7))
    | r2_hidden(X0_53,k1_tops_1(sK7,sK5(sK7,X0_53))) ),
    inference(subtyping,[status(esa)],[c_894])).

cnf(c_5075,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | r2_hidden(sK9,k1_tops_1(sK7,sK5(sK7,sK9))) ),
    inference(instantiation,[status(thm)],[c_4145])).

cnf(c_5076,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK9,k1_tops_1(sK7,sK5(sK7,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5075])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4163,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ r2_hidden(X2_53,X0_53)
    | ~ v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_4922,plain,
    ( ~ m1_subset_1(k1_tops_1(sK7,X0_53),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X1_53,k1_tops_1(sK7,X0_53))
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4163])).

cnf(c_5275,plain,
    ( ~ m1_subset_1(k1_tops_1(sK7,sK5(sK7,sK9)),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(sK9,k1_tops_1(sK7,sK5(sK7,sK9)))
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4922])).

cnf(c_5276,plain,
    ( m1_subset_1(k1_tops_1(sK7,sK5(sK7,sK9)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK9,k1_tops_1(sK7,sK5(sK7,sK9))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5275])).

cnf(c_5737,plain,
    ( ~ m1_subset_1(sK5(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(k1_tops_1(sK7,sK5(sK7,sK9)),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_4153])).

cnf(c_5738,plain,
    ( m1_subset_1(sK5(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(k1_tops_1(sK7,sK5(sK7,sK9)),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5737])).

cnf(c_25,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_543,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_544,plain,
    ( m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v3_pre_topc(X0,sK7)
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_548,plain,
    ( m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v3_pre_topc(X0,sK7)
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_35,c_34])).

cnf(c_840,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v3_pre_topc(X0,sK7)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X2,sK8)
    | X0 != X2
    | sK7 != sK7
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_548])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ v3_pre_topc(X0,sK7)
    | ~ r2_hidden(sK9,X0)
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0,sK8) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_845,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(X0,sK7)
    | ~ r2_hidden(sK9,X0)
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_32])).

cnf(c_4148,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(X0_53,sK7)
    | ~ r2_hidden(sK9,X0_53)
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(X0_53,sK8) ),
    inference(subtyping,[status(esa)],[c_845])).

cnf(c_8554,plain,
    ( ~ m1_subset_1(sK4(X0_53,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v3_pre_topc(sK4(X0_53,sK7,sK9),sK7)
    | ~ r2_hidden(sK9,sK4(X0_53,sK7,sK9))
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | ~ r1_xboole_0(sK4(X0_53,sK7,sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_4148])).

cnf(c_8557,plain,
    ( m1_subset_1(sK4(X0_53,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v3_pre_topc(sK4(X0_53,sK7,sK9),sK7) != iProver_top
    | r2_hidden(sK9,sK4(X0_53,sK7,sK9)) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r1_xboole_0(sK4(X0_53,sK7,sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8554])).

cnf(c_8559,plain,
    ( m1_subset_1(sK4(sK8,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v3_pre_topc(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | r2_hidden(sK9,sK4(sK8,sK7,sK9)) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r1_xboole_0(sK4(sK8,sK7,sK9),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8557])).

cnf(c_22,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4165,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_8583,plain,
    ( ~ r1_xboole_0(X0_53,sK4(X0_53,X0_54,sK9))
    | r1_xboole_0(sK4(X0_53,X0_54,sK9),X0_53) ),
    inference(instantiation,[status(thm)],[c_4165])).

cnf(c_8597,plain,
    ( r1_xboole_0(X0_53,sK4(X0_53,X0_54,sK9)) != iProver_top
    | r1_xboole_0(sK4(X0_53,X0_54,sK9),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8583])).

cnf(c_8599,plain,
    ( r1_xboole_0(sK4(sK8,sK7,sK9),sK8) = iProver_top
    | r1_xboole_0(sK8,sK4(sK8,sK7,sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8597])).

cnf(c_8695,plain,
    ( r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6249,c_40,c_41,c_4253,c_4883,c_4887,c_4891,c_4895,c_5006,c_5060,c_5076,c_5276,c_5738,c_8559,c_8599])).

cnf(c_8697,plain,
    ( r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8695])).

cnf(c_4159,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_4801,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4159])).

cnf(c_4812,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v3_pre_topc(X0_53,sK7) != iProver_top
    | r2_hidden(sK9,X0_53) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r1_xboole_0(X0_53,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4148])).

cnf(c_6358,plain,
    ( v3_pre_topc(sK8,sK7) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) = iProver_top
    | r2_hidden(sK9,sK8) != iProver_top
    | r1_xboole_0(sK8,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4801,c_4812])).

cnf(c_30,negated_conjecture,
    ( m1_connsp_2(sK10,sK7,sK9)
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_788,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | sK7 != sK7
    | sK9 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_575])).

cnf(c_789,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_791,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_32])).

cnf(c_4151,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_4809,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4151])).

cnf(c_6413,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v3_pre_topc(sK8,sK7) != iProver_top
    | r2_hidden(sK9,sK8) != iProver_top
    | r1_xboole_0(sK8,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6358,c_4809])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | v3_pre_topc(k1_tops_1(sK7,X0),sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_660,plain,
    ( v3_pre_topc(k1_tops_1(sK7,X0),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_34])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | v3_pre_topc(k1_tops_1(sK7,X0),sK7) ),
    inference(renaming,[status(thm)],[c_660])).

cnf(c_4158,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7)))
    | v3_pre_topc(k1_tops_1(sK7,X0_53),sK7) ),
    inference(subtyping,[status(esa)],[c_661])).

cnf(c_4802,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v3_pre_topc(k1_tops_1(sK7,X0_53),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4158])).

cnf(c_8291,plain,
    ( v3_pre_topc(k1_tops_1(sK7,sK10),sK7) = iProver_top
    | v3_pre_topc(sK8,sK7) != iProver_top
    | r2_hidden(sK9,sK8) != iProver_top
    | r1_xboole_0(sK8,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6413,c_4802])).

cnf(c_790,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_8643,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7)))
    | v3_pre_topc(k1_tops_1(sK7,sK10),sK7) ),
    inference(instantiation,[status(thm)],[c_4158])).

cnf(c_8644,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v3_pre_topc(k1_tops_1(sK7,sK10),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8643])).

cnf(c_8690,plain,
    ( v3_pre_topc(k1_tops_1(sK7,sK10),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8291,c_40,c_41,c_790,c_4253,c_4883,c_4887,c_4891,c_4895,c_5006,c_5060,c_5076,c_5276,c_5738,c_8559,c_8599,c_8644])).

cnf(c_8692,plain,
    ( v3_pre_topc(k1_tops_1(sK7,sK10),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8690])).

cnf(c_8380,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK7,sK10),sK8)
    | r1_xboole_0(sK8,k1_tops_1(sK7,sK10)) ),
    inference(instantiation,[status(thm)],[c_4165])).

cnf(c_24,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | r1_xboole_0(X4,X3)
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | k1_tops_1(X1,X0) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k1_tops_1(X1,X0),X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k1_tops_1(X1,X0),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_34])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_tops_1(sK7,X0),X1) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_4155,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(k1_tops_1(sK7,X0_53),X1_53) ),
    inference(subtyping,[status(esa)],[c_707])).

cnf(c_6608,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_xboole_0(k1_tops_1(sK7,sK10),sK8)
    | ~ r1_xboole_0(sK10,sK8) ),
    inference(instantiation,[status(thm)],[c_4155])).

cnf(c_5005,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | r2_hidden(sK9,u1_struct_0(sK7))
    | v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5003])).

cnf(c_4252,plain,
    ( sP0(sK8,sK7,k2_pre_topc(sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_4157])).

cnf(c_802,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(X0,k1_tops_1(sK7,X1))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | sK7 != sK7
    | sK9 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_527])).

cnf(c_803,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | r2_hidden(sK9,k1_tops_1(sK7,sK10))
    | ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(sK9,k2_pre_topc(sK7,sK8))
    | r1_xboole_0(sK10,sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11592,c_9336,c_8697,c_8692,c_8380,c_6608,c_5737,c_5275,c_5075,c_5059,c_5005,c_4252,c_803,c_789,c_29,c_32,c_33])).


%------------------------------------------------------------------------------
