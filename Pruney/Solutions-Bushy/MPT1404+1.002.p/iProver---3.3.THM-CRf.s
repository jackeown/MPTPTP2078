%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1404+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:39 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 814 expanded)
%              Number of clauses        :  125 ( 191 expanded)
%              Number of leaves         :   23 ( 231 expanded)
%              Depth                    :   22
%              Number of atoms          : 1000 (6599 expanded)
%              Number of equality atoms :   97 ( 118 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(nnf_transformation,[],[f42])).

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

fof(f66,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X0,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X3,X1)
          & m1_connsp_2(X3,X0,X2) )
     => ( r1_xboole_0(sK8,X1)
        & m1_connsp_2(sK8,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
              & m1_connsp_2(X3,X0,sK7) )
          | ~ r2_hidden(sK7,k2_pre_topc(X0,X1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X4,X1)
              | ~ m1_connsp_2(X4,X0,sK7) )
          | r2_hidden(sK7,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                  ( r1_xboole_0(X3,sK6)
                  & m1_connsp_2(X3,X0,X2) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK6)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X4,sK6)
                  | ~ m1_connsp_2(X4,X0,X2) )
              | r2_hidden(X2,k2_pre_topc(X0,sK6)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
                    & m1_connsp_2(X3,sK5,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(sK5,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,sK5,X2) )
                | r2_hidden(X2,k2_pre_topc(sK5,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ( r1_xboole_0(sK8,sK6)
        & m1_connsp_2(sK8,sK5,sK7) )
      | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(X4,sK6)
          | ~ m1_connsp_2(X4,sK5,sK7) )
      | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) )
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f58,f62,f61,f60,f59])).

fof(f95,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,sK6)
      | ~ m1_connsp_2(X4,sK5,sK7)
      | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f91,plain,(
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

fof(f93,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f63])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f43,f42])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X0,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,
    ( m1_connsp_2(sK8,sK5,sK7)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f63])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,
    ( r1_xboole_0(sK8,sK6)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ r1_xboole_0(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4232,plain,
    ( ~ sP0(X0_52,X0_53,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(X0_53)))
    | ~ v3_pre_topc(X2_52,X0_53)
    | ~ r2_hidden(X3_52,X2_52)
    | ~ r2_hidden(X3_52,X1_52)
    | ~ r2_hidden(X3_52,u1_struct_0(X0_53))
    | ~ r1_xboole_0(X0_52,X2_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_5175,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | ~ m1_subset_1(k1_tops_1(sK5,X2_52),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(k1_tops_1(sK5,X2_52),sK5)
    | ~ r2_hidden(X3_52,X1_52)
    | ~ r2_hidden(X3_52,k1_tops_1(sK5,X2_52))
    | ~ r2_hidden(X3_52,u1_struct_0(sK5))
    | ~ r1_xboole_0(X0_52,k1_tops_1(sK5,X2_52)) ),
    inference(instantiation,[status(thm)],[c_4232])).

cnf(c_5287,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | ~ m1_subset_1(k1_tops_1(sK5,X2_52),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(k1_tops_1(sK5,X2_52),sK5)
    | ~ r2_hidden(sK7,X1_52)
    | ~ r2_hidden(sK7,k1_tops_1(sK5,X2_52))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r1_xboole_0(X0_52,k1_tops_1(sK5,X2_52)) ),
    inference(instantiation,[status(thm)],[c_5175])).

cnf(c_5851,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
    | ~ r2_hidden(sK7,X1_52)
    | ~ r2_hidden(sK7,k1_tops_1(sK5,sK8))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r1_xboole_0(X0_52,k1_tops_1(sK5,sK8)) ),
    inference(instantiation,[status(thm)],[c_5287])).

cnf(c_7830,plain,
    ( ~ sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52))
    | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
    | ~ r2_hidden(sK7,k1_tops_1(sK5,sK8))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,X0_52))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r1_xboole_0(X0_52,k1_tops_1(sK5,sK8)) ),
    inference(instantiation,[status(thm)],[c_5851])).

cnf(c_7832,plain,
    ( ~ sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | ~ m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(k1_tops_1(sK5,sK8),sK5)
    | ~ r2_hidden(sK7,k1_tops_1(sK5,sK8))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ r1_xboole_0(sK6,k1_tops_1(sK5,sK8)) ),
    inference(instantiation,[status(thm)],[c_7830])).

cnf(c_22,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4231,plain,
    ( ~ r1_xboole_0(X0_52,X1_52)
    | r1_xboole_0(X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_6785,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK5,sK8),sK6)
    | r1_xboole_0(sK6,k1_tops_1(sK5,sK8)) ),
    inference(instantiation,[status(thm)],[c_4231])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_849,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k1_tops_1(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_4221,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k1_tops_1(sK5,X0_52),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_849])).

cnf(c_6757,plain,
    ( m1_subset_1(k1_tops_1(sK5,sK8),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4221])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4228,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_4813,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4228])).

cnf(c_31,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK5,sK7)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(X0,sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_27,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_666,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_667,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_671,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_35,c_34])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(X2,sK6)
    | X0 != X2
    | sK5 != sK5
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_671])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_1017])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1022,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0,sK5)
    | ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1018,c_32])).

cnf(c_4214,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0_52,sK5)
    | ~ r2_hidden(sK7,X0_52)
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(X0_52,sK6) ),
    inference(subtyping,[status(esa)],[c_1022])).

cnf(c_4827,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(X0_52,sK5) != iProver_top
    | r2_hidden(sK7,X0_52) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r1_xboole_0(X0_52,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4214])).

cnf(c_5906,plain,
    ( v3_pre_topc(sK6,sK5) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | r1_xboole_0(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4813,c_4827])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_558,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X1 != X3
    | X0 != X4
    | k2_pre_topc(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1])).

cnf(c_559,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_17])).

cnf(c_564,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_806,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_564,c_34])).

cnf(c_807,plain,
    ( sP0(X0,sK5,k2_pre_topc(sK5,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_4224,plain,
    ( sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_807])).

cnf(c_4306,plain,
    ( sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4224])).

cnf(c_4308,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4306])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_18,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_498,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_18,c_20])).

cnf(c_738,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_498,c_36])).

cnf(c_739,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_68,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_74,plain,
    ( l1_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_741,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_36,c_34,c_68,c_74])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_741])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_4226,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | r2_hidden(X0_52,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_771])).

cnf(c_5083,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4226])).

cnf(c_5084,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5083])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X3,sK4(X0,X1,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4235,plain,
    ( ~ sP0(X0_52,X0_53,X1_52)
    | r2_hidden(X2_52,X1_52)
    | r2_hidden(X2_52,sK4(X0_52,X0_53,X2_52))
    | ~ r2_hidden(X2_52,u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5197,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | r2_hidden(sK7,X1_52)
    | r2_hidden(sK7,sK4(X0_52,sK5,sK7))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4235])).

cnf(c_5338,plain,
    ( ~ sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52))
    | r2_hidden(sK7,sK4(X0_52,sK5,sK7))
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5197])).

cnf(c_5339,plain,
    ( sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52)) != iProver_top
    | r2_hidden(sK7,sK4(X0_52,sK5,sK7)) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5338])).

cnf(c_5341,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,sK4(sK6,sK5,sK7)) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5339])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v3_pre_topc(sK4(X0,X1,X3),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4234,plain,
    ( ~ sP0(X0_52,X0_53,X1_52)
    | v3_pre_topc(sK4(X0_52,X0_53,X2_52),X0_53)
    | r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(X2_52,u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_5198,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | v3_pre_topc(sK4(X0_52,sK5,sK7),sK5)
    | r2_hidden(sK7,X1_52)
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4234])).

cnf(c_5359,plain,
    ( ~ sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52))
    | v3_pre_topc(sK4(X0_52,sK5,sK7),sK5)
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5198])).

cnf(c_5360,plain,
    ( sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52)) != iProver_top
    | v3_pre_topc(sK4(X0_52,sK5,sK7),sK5) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5359])).

cnf(c_5362,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6)) != iProver_top
    | v3_pre_topc(sK4(sK6,sK5,sK7),sK5) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4233,plain,
    ( ~ sP0(X0_52,X0_53,X1_52)
    | m1_subset_1(sK4(X0_52,X0_53,X2_52),k1_zfmisc_1(u1_struct_0(X0_53)))
    | r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(X2_52,u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5199,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | m1_subset_1(sK4(X0_52,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK7,X1_52)
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4233])).

cnf(c_5365,plain,
    ( ~ sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52))
    | m1_subset_1(sK4(X0_52,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5199])).

cnf(c_5366,plain,
    ( sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52)) != iProver_top
    | m1_subset_1(sK4(X0_52,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5365])).

cnf(c_5368,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6)) != iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5366])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4236,plain,
    ( ~ sP0(X0_52,X0_53,X1_52)
    | r2_hidden(X2_52,X1_52)
    | ~ r2_hidden(X2_52,u1_struct_0(X0_53))
    | r1_xboole_0(X0_52,sK4(X0_52,X0_53,X2_52)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_5196,plain,
    ( ~ sP0(X0_52,sK5,X1_52)
    | r2_hidden(sK7,X1_52)
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | r1_xboole_0(X0_52,sK4(X0_52,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_4236])).

cnf(c_5393,plain,
    ( ~ sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52))
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52))
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | r1_xboole_0(X0_52,sK4(X0_52,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5196])).

cnf(c_5394,plain,
    ( sP0(X0_52,sK5,k2_pre_topc(sK5,X0_52)) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,X0_52)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top
    | r1_xboole_0(X0_52,sK4(X0_52,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5393])).

cnf(c_5396,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top
    | r1_xboole_0(sK6,sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5394])).

cnf(c_5966,plain,
    ( ~ m1_subset_1(sK4(X0_52,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK4(X0_52,sK5,sK7),sK5)
    | ~ r2_hidden(sK7,sK4(X0_52,sK5,sK7))
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | ~ r1_xboole_0(sK4(X0_52,sK5,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_4214])).

cnf(c_5967,plain,
    ( m1_subset_1(sK4(X0_52,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK4(X0_52,sK5,sK7),sK5) != iProver_top
    | r2_hidden(sK7,sK4(X0_52,sK5,sK7)) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r1_xboole_0(sK4(X0_52,sK5,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5966])).

cnf(c_5969,plain,
    ( m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK4(sK6,sK5,sK7),sK5) != iProver_top
    | r2_hidden(sK7,sK4(sK6,sK5,sK7)) != iProver_top
    | r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top
    | r1_xboole_0(sK4(sK6,sK5,sK7),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5967])).

cnf(c_6046,plain,
    ( ~ r1_xboole_0(X0_52,sK4(X0_52,sK5,sK7))
    | r1_xboole_0(sK4(X0_52,sK5,sK7),X0_52) ),
    inference(instantiation,[status(thm)],[c_4231])).

cnf(c_6052,plain,
    ( r1_xboole_0(X0_52,sK4(X0_52,sK5,sK7)) != iProver_top
    | r1_xboole_0(sK4(X0_52,sK5,sK7),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6046])).

cnf(c_6054,plain,
    ( r1_xboole_0(sK4(sK6,sK5,sK7),sK6) = iProver_top
    | r1_xboole_0(sK6,sK4(sK6,sK5,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6052])).

cnf(c_6124,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5906,c_40,c_41,c_4308,c_5084,c_5341,c_5362,c_5368,c_5396,c_5969,c_6054])).

cnf(c_6126,plain,
    ( r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6124])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(k1_tops_1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_790,plain,
    ( v3_pre_topc(k1_tops_1(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_34])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0),sK5) ),
    inference(renaming,[status(thm)],[c_790])).

cnf(c_4225,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,X0_52),sK5) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_5946,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(k1_tops_1(sK5,sK8),sK5) ),
    inference(instantiation,[status(thm)],[c_4225])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_26,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_860,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_861,plain,
    ( r1_tarski(k1_tops_1(sK5,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_860])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X3,X2)
    | X0 != X1
    | k1_tops_1(sK5,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_861])).

cnf(c_903,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_tops_1(sK5,X0),X1) ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_4220,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_xboole_0(X0_52,X1_52)
    | r1_xboole_0(k1_tops_1(sK5,X0_52),X1_52) ),
    inference(subtyping,[status(esa)],[c_903])).

cnf(c_5615,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_xboole_0(k1_tops_1(sK5,sK8),sK6)
    | ~ r1_xboole_0(sK8,sK6) ),
    inference(instantiation,[status(thm)],[c_4220])).

cnf(c_4307,plain,
    ( sP0(sK6,sK5,k2_pre_topc(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4224])).

cnf(c_30,negated_conjecture,
    ( m1_connsp_2(sK8,sK5,sK7)
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_224,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_19])).

cnf(c_645,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_36])).

cnf(c_646,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_650,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k1_tops_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_35,c_34])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k1_tops_1(sK5,X1))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | sK5 != sK5
    | sK7 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_650])).

cnf(c_980,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,k1_tops_1(sK5,sK8))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_979])).

cnf(c_693,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_694,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_698,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_35,c_34])).

cnf(c_965,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | sK5 != sK5
    | sK7 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_698])).

cnf(c_966,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_965])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(sK7,k2_pre_topc(sK5,sK6))
    | r1_xboole_0(sK8,sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7832,c_6785,c_6757,c_6126,c_5946,c_5615,c_5083,c_4307,c_980,c_966,c_29,c_32,c_33])).


%------------------------------------------------------------------------------
