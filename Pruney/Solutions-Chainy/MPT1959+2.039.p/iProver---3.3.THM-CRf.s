%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:32 EST 2020

% Result     : Theorem 54.99s
% Output     : CNFRefutation 54.99s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 693 expanded)
%              Number of clauses        :  141 ( 203 expanded)
%              Number of leaves         :   23 ( 137 expanded)
%              Depth                    :   21
%              Number of atoms          :  932 (4968 expanded)
%              Number of equality atoms :  132 ( 176 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
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

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ? [X4] :
                ( r2_hidden(X4,X1)
                & r1_orders_2(X0,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X4,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X4,X3)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X4,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X4,X3)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r1_orders_2(X1,X5,X3)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X7,X6)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ? [X8] :
                    ( r2_hidden(X8,X0)
                    & r1_orders_2(X1,X8,X6)
                    & m1_subset_1(X8,u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f54,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK6(X0,X1,X6),X0)
        & r1_orders_2(X1,sK6(X0,X1,X6),X6)
        & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X5,X3)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r1_orders_2(X1,sK5(X0,X1,X2),X3)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r1_orders_2(X1,X5,X3)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r1_orders_2(X1,X4,sK4(X0,X1,X2))
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r1_orders_2(X1,X5,sK4(X0,X1,X2))
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,sK4(X0,X1,X2))
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X0)
              & r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
              & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK4(X0,X1,X2),X2) )
          & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X7,X6)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ( r2_hidden(sK6(X0,X1,X6),X0)
                  & r1_orders_2(X1,sK6(X0,X1,X6),X6)
                  & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).

fof(f82,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK8)
          | ~ v1_subset_1(sK8,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK8)
          | v1_subset_1(sK8,u1_struct_0(X0)) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK8,X0)
        & ~ v1_xboole_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK7),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK7)) )
          & ( ~ r2_hidden(k3_yellow_0(sK7),X1)
            | v1_subset_1(X1,u1_struct_0(sK7)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
          & v13_waybel_0(X1,sK7)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK7)
      & v1_yellow_0(sK7)
      & v5_orders_2(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( r2_hidden(k3_yellow_0(sK7),sK8)
      | ~ v1_subset_1(sK8,u1_struct_0(sK7)) )
    & ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
      | v1_subset_1(sK8,u1_struct_0(sK7)) )
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & v13_waybel_0(sK8,sK7)
    & ~ v1_xboole_0(sK8)
    & l1_orders_2(sK7)
    & v1_yellow_0(sK7)
    & v5_orders_2(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f59,f61,f60])).

fof(f95,plain,(
    v1_yellow_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f93,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | ~ r1_orders_2(X1,X4,sK4(X0,X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ~ r1_tarski(k4_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k4_waybel_0(X0,X1),X1)
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    v13_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f62])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ( k4_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ( ( k4_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k4_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( k4_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k4_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k4_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k4_waybel_0(X1,X2))
      | ~ sP1(k4_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f30,f36,f35])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f101,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | ~ v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f103,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f100,plain,
    ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_172769,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK8)
    | ~ r1_tarski(sK8,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_177011,plain,
    ( r2_hidden(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X0,sK8)
    | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_172769])).

cnf(c_186462,plain,
    ( r2_hidden(sK3(X0,sK8,X1),u1_struct_0(sK7))
    | ~ r2_hidden(sK3(X0,sK8,X1),sK8)
    | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_177011])).

cnf(c_215990,plain,
    ( r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
    | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_186462])).

cnf(c_177059,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_waybel_0(sK7,sK8))
    | ~ r1_tarski(k4_waybel_0(sK7,sK8),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_183459,plain,
    ( ~ r2_hidden(X0,k4_waybel_0(sK7,sK8))
    | r2_hidden(X0,sK8)
    | ~ r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_177059])).

cnf(c_191329,plain,
    ( ~ r2_hidden(sK4(sK8,X0,sK8),k4_waybel_0(sK7,sK8))
    | r2_hidden(sK4(sK8,X0,sK8),sK8)
    | ~ r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_183459])).

cnf(c_191331,plain,
    ( ~ r2_hidden(sK4(sK8,sK7,sK8),k4_waybel_0(sK7,sK8))
    | r2_hidden(sK4(sK8,sK7,sK8),sK8)
    | ~ r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_191329])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X4,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6658,plain,
    ( ~ sP0(sK8,X0,X1)
    | ~ r1_orders_2(X0,k3_yellow_0(X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k3_yellow_0(X2),u1_struct_0(X0))
    | r2_hidden(X3,X1)
    | ~ r2_hidden(k3_yellow_0(X2),sK8) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_7983,plain,
    ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
    | ~ r1_orders_2(sK7,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
    | r2_hidden(X1,k4_waybel_0(sK7,sK8))
    | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
    inference(instantiation,[status(thm)],[c_6658])).

cnf(c_12154,plain,
    ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
    | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK4(X1,sK7,X2))
    | ~ m1_subset_1(sK4(X1,sK7,X2),u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
    | r2_hidden(sK4(X1,sK7,X2),k4_waybel_0(sK7,sK8))
    | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
    inference(instantiation,[status(thm)],[c_7983])).

cnf(c_32056,plain,
    ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
    | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK4(X1,sK7,sK8))
    | ~ m1_subset_1(sK4(X1,sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
    | r2_hidden(sK4(X1,sK7,sK8),k4_waybel_0(sK7,sK8))
    | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
    inference(instantiation,[status(thm)],[c_12154])).

cnf(c_70325,plain,
    ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
    | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK4(sK8,sK7,sK8))
    | ~ m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
    | r2_hidden(sK4(sK8,sK7,sK8),k4_waybel_0(sK7,sK8))
    | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
    inference(instantiation,[status(thm)],[c_32056])).

cnf(c_70327,plain,
    ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
    | ~ r1_orders_2(sK7,k3_yellow_0(sK7),sK4(sK8,sK7,sK8))
    | ~ m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | r2_hidden(sK4(sK8,sK7,sK8),k4_waybel_0(sK7,sK8))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_70325])).

cnf(c_13,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,negated_conjecture,
    ( v1_yellow_0(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_548,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_549,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v2_struct_0(sK7)
    | ~ v5_orders_2(sK7)
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r1_orders_2(sK7,k3_yellow_0(sK7),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_38,c_37,c_35])).

cnf(c_554,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_5040,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),sK4(X0,sK7,X1))
    | ~ m1_subset_1(sK4(X0,sK7,X1),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_27949,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),sK4(X0,sK7,sK8))
    | ~ m1_subset_1(sK4(X0,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5040])).

cnf(c_55980,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),sK4(sK8,sK7,sK8))
    | ~ m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_27949])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X1,X3,sK4(X0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(sK4(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7275,plain,
    ( sP0(sK8,X0,X1)
    | ~ r1_orders_2(X0,X2,sK4(sK8,X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,sK8)
    | ~ r2_hidden(sK4(sK8,X0,X1),X1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_13544,plain,
    ( sP0(sK8,X0,sK8)
    | ~ r1_orders_2(X0,X1,sK4(sK8,X0,sK8))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,sK8)
    | ~ r2_hidden(sK4(sK8,X0,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_7275])).

cnf(c_31754,plain,
    ( sP0(sK8,X0,sK8)
    | ~ r1_orders_2(X0,k3_yellow_0(sK7),sK4(sK8,X0,sK8))
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(X0))
    | ~ r2_hidden(sK4(sK8,X0,sK8),sK8)
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_13544])).

cnf(c_31756,plain,
    ( sP0(sK8,sK7,sK8)
    | ~ r1_orders_2(sK7,k3_yellow_0(sK7),sK4(sK8,sK7,sK8))
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | ~ r2_hidden(sK4(sK8,sK7,sK8),sK8)
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_31754])).

cnf(c_26369,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)))
    | ~ m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_7988,plain,
    ( ~ sP0(sK8,sK7,sK8)
    | ~ r1_orders_2(sK7,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
    | r2_hidden(X1,sK8)
    | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
    inference(instantiation,[status(thm)],[c_6658])).

cnf(c_24068,plain,
    ( ~ sP0(sK8,sK7,sK8)
    | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)))
    | ~ m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
    | r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
    | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
    inference(instantiation,[status(thm)],[c_7988])).

cnf(c_24075,plain,
    ( ~ sP0(sK8,sK7,sK8)
    | ~ r1_orders_2(sK7,k3_yellow_0(sK7),sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)))
    | ~ m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_24068])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,X0,X2),X2)
    | ~ r2_hidden(sK3(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_301,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_302,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,X2,X0),X0)
    | ~ r2_hidden(sK3(X1,X2,X0),X2)
    | ~ r1_tarski(X2,X1)
    | X0 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_302])).

cnf(c_2542,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_2543,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_2542])).

cnf(c_2601,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X2)
    | ~ r2_hidden(sK3(X0,X1,X2),X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_384,c_2543])).

cnf(c_4858,plain,
    ( ~ r2_hidden(sK3(X0,X1,u1_struct_0(sK7)),X1)
    | ~ r2_hidden(sK3(X0,X1,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(u1_struct_0(sK7),X0)
    | u1_struct_0(sK7) = X1 ),
    inference(instantiation,[status(thm)],[c_2601])).

cnf(c_8875,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK7),X0,u1_struct_0(sK7)),X0)
    | ~ r2_hidden(sK3(u1_struct_0(sK7),X0,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r1_tarski(X0,u1_struct_0(sK7))
    | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
    | u1_struct_0(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_4858])).

cnf(c_19864,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
    | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
    | ~ r1_tarski(sK8,u1_struct_0(sK7))
    | u1_struct_0(sK7) = sK8 ),
    inference(instantiation,[status(thm)],[c_8875])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK3(X1,X0,X2),X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK3(X1,X2,X0),X1)
    | ~ r1_tarski(X2,X1)
    | X0 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_302])).

cnf(c_2603,plain,
    ( m1_subset_1(sK3(X0,X1,X2),X0)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_386,c_2543])).

cnf(c_4859,plain,
    ( m1_subset_1(sK3(X0,X1,u1_struct_0(sK7)),X0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(u1_struct_0(sK7),X0)
    | u1_struct_0(sK7) = X1 ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_8877,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK7),X0,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r1_tarski(X0,u1_struct_0(sK7))
    | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
    | u1_struct_0(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_4859])).

cnf(c_19084,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
    | ~ r1_tarski(sK8,u1_struct_0(sK7))
    | u1_struct_0(sK7) = sK8 ),
    inference(instantiation,[status(thm)],[c_8877])).

cnf(c_27,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k4_waybel_0(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( v13_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k4_waybel_0(X1,X0),X0)
    | ~ l1_orders_2(X1)
    | sK8 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_618,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_tarski(k4_waybel_0(sK7,sK8),sK8)
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_620,plain,
    ( r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_35,c_32])).

cnf(c_4289,plain,
    ( r1_tarski(k4_waybel_0(sK7,sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4307,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4306,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5555,plain,
    ( r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4307,c_4306])).

cnf(c_10018,plain,
    ( r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5555,c_4306])).

cnf(c_16321,plain,
    ( r2_hidden(sK2(k4_waybel_0(sK7,sK8),X0),X1) = iProver_top
    | r1_tarski(k4_waybel_0(sK7,sK8),X0) = iProver_top
    | r1_tarski(sK8,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4289,c_10018])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4308,plain,
    ( r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16904,plain,
    ( r1_tarski(k4_waybel_0(sK7,sK8),X0) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16321,c_4308])).

cnf(c_4304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( ~ sP1(k4_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k4_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_637,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_638,plain,
    ( sP1(X0,sK7,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_676,plain,
    ( sP0(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))
    | X3 != X0
    | k4_waybel_0(X1,X0) != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_638])).

cnf(c_677,plain,
    ( sP0(X0,sK7,k4_waybel_0(sK7,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(k4_waybel_0(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_4286,plain,
    ( sP0(X0,sK7,k4_waybel_0(sK7,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(k4_waybel_0(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_4919,plain,
    ( sP0(X0,sK7,k4_waybel_0(sK7,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r1_tarski(k4_waybel_0(sK7,X0),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4304,c_4286])).

cnf(c_17128,plain,
    ( sP0(sK8,sK7,k4_waybel_0(sK7,sK8)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r1_tarski(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16904,c_4919])).

cnf(c_17138,plain,
    ( sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17128])).

cnf(c_4554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_tarski(X0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8872,plain,
    ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4554])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5039,plain,
    ( sP0(X0,sK7,X1)
    | m1_subset_1(sK4(X0,sK7,X1),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6806,plain,
    ( sP0(X0,sK7,sK8)
    | m1_subset_1(sK4(X0,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5039])).

cnf(c_7994,plain,
    ( sP0(sK8,sK7,sK8)
    | m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_6806])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_299,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_28,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_389,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_28,c_302])).

cnf(c_30,negated_conjecture,
    ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_305,plain,
    ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_703,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK7) != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_305])).

cnf(c_704,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | ~ r1_tarski(sK8,u1_struct_0(sK7))
    | u1_struct_0(sK7) = sK8 ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) != X1
    | u1_struct_0(sK7) = sK8
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_300,c_704])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) = sK8 ),
    inference(unflattening,[status(thm)],[c_1138])).

cnf(c_1141,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1139,c_32])).

cnf(c_4284,plain,
    ( u1_struct_0(sK7) = sK8
    | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_42,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_97,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_99,plain,
    ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7)) = iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_705,plain,
    ( u1_struct_0(sK7) = sK8
    | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top
    | r1_tarski(sK8,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_3621,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_3630,plain,
    ( k3_yellow_0(sK7) = k3_yellow_0(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3621])).

cnf(c_3615,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3636,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3615])).

cnf(c_3616,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4596,plain,
    ( u1_struct_0(sK7) != X0
    | sK8 != X0
    | sK8 = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3616])).

cnf(c_4703,plain,
    ( u1_struct_0(sK7) != sK8
    | sK8 = u1_struct_0(sK7)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_4596])).

cnf(c_4704,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_3615])).

cnf(c_4292,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4303,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4899,plain,
    ( r1_tarski(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4292,c_4303])).

cnf(c_3620,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4586,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | X1 != u1_struct_0(sK7)
    | X0 != k3_yellow_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_4827,plain,
    ( m1_subset_1(X0,sK8)
    | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | X0 != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4586])).

cnf(c_5264,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | m1_subset_1(k3_yellow_0(sK7),sK8)
    | k3_yellow_0(sK7) != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4827])).

cnf(c_5267,plain,
    ( k3_yellow_0(sK7) != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7)
    | m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5264])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,sK8)
    | r2_hidden(X0,sK8) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_5644,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK7),sK8)
    | r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_5645,plain,
    ( m1_subset_1(k3_yellow_0(sK7),sK8) != iProver_top
    | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5644])).

cnf(c_7320,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4284,c_42,c_99,c_705,c_3630,c_3636,c_4703,c_4704,c_4899,c_5267,c_5645])).

cnf(c_7322,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7320])).

cnf(c_4682,plain,
    ( r2_hidden(sK2(X0,u1_struct_0(sK7)),X0)
    | r1_tarski(X0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7141,plain,
    ( r2_hidden(sK2(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))
    | r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4682])).

cnf(c_4683,plain,
    ( ~ r2_hidden(sK2(X0,u1_struct_0(sK7)),u1_struct_0(sK7))
    | r1_tarski(X0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4975,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))
    | r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4683])).

cnf(c_4911,plain,
    ( r1_tarski(sK8,u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4899])).

cnf(c_29,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_31,negated_conjecture,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_303,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) != X0
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_303])).

cnf(c_717,plain,
    ( ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | sK8 != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_98,plain,
    ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_215990,c_191331,c_70327,c_55980,c_31756,c_26369,c_24075,c_19864,c_19084,c_17138,c_8872,c_7994,c_7322,c_7141,c_4975,c_4911,c_4704,c_4703,c_717,c_618,c_98,c_32,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 54.99/7.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.99/7.49  
% 54.99/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.99/7.49  
% 54.99/7.49  ------  iProver source info
% 54.99/7.49  
% 54.99/7.49  git: date: 2020-06-30 10:37:57 +0100
% 54.99/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.99/7.49  git: non_committed_changes: false
% 54.99/7.49  git: last_make_outside_of_git: false
% 54.99/7.49  
% 54.99/7.49  ------ 
% 54.99/7.49  
% 54.99/7.49  ------ Input Options
% 54.99/7.49  
% 54.99/7.49  --out_options                           all
% 54.99/7.49  --tptp_safe_out                         true
% 54.99/7.49  --problem_path                          ""
% 54.99/7.49  --include_path                          ""
% 54.99/7.49  --clausifier                            res/vclausify_rel
% 54.99/7.49  --clausifier_options                    --mode clausify
% 54.99/7.49  --stdin                                 false
% 54.99/7.49  --stats_out                             all
% 54.99/7.49  
% 54.99/7.49  ------ General Options
% 54.99/7.49  
% 54.99/7.49  --fof                                   false
% 54.99/7.49  --time_out_real                         305.
% 54.99/7.49  --time_out_virtual                      -1.
% 54.99/7.49  --symbol_type_check                     false
% 54.99/7.49  --clausify_out                          false
% 54.99/7.49  --sig_cnt_out                           false
% 54.99/7.49  --trig_cnt_out                          false
% 54.99/7.49  --trig_cnt_out_tolerance                1.
% 54.99/7.49  --trig_cnt_out_sk_spl                   false
% 54.99/7.49  --abstr_cl_out                          false
% 54.99/7.49  
% 54.99/7.49  ------ Global Options
% 54.99/7.49  
% 54.99/7.49  --schedule                              default
% 54.99/7.49  --add_important_lit                     false
% 54.99/7.49  --prop_solver_per_cl                    1000
% 54.99/7.49  --min_unsat_core                        false
% 54.99/7.49  --soft_assumptions                      false
% 54.99/7.49  --soft_lemma_size                       3
% 54.99/7.49  --prop_impl_unit_size                   0
% 54.99/7.49  --prop_impl_unit                        []
% 54.99/7.49  --share_sel_clauses                     true
% 54.99/7.49  --reset_solvers                         false
% 54.99/7.49  --bc_imp_inh                            [conj_cone]
% 54.99/7.49  --conj_cone_tolerance                   3.
% 54.99/7.49  --extra_neg_conj                        none
% 54.99/7.49  --large_theory_mode                     true
% 54.99/7.49  --prolific_symb_bound                   200
% 54.99/7.49  --lt_threshold                          2000
% 54.99/7.49  --clause_weak_htbl                      true
% 54.99/7.49  --gc_record_bc_elim                     false
% 54.99/7.49  
% 54.99/7.49  ------ Preprocessing Options
% 54.99/7.49  
% 54.99/7.49  --preprocessing_flag                    true
% 54.99/7.49  --time_out_prep_mult                    0.1
% 54.99/7.49  --splitting_mode                        input
% 54.99/7.49  --splitting_grd                         true
% 54.99/7.49  --splitting_cvd                         false
% 54.99/7.49  --splitting_cvd_svl                     false
% 54.99/7.49  --splitting_nvd                         32
% 54.99/7.49  --sub_typing                            true
% 54.99/7.49  --prep_gs_sim                           true
% 54.99/7.49  --prep_unflatten                        true
% 54.99/7.49  --prep_res_sim                          true
% 54.99/7.49  --prep_upred                            true
% 54.99/7.49  --prep_sem_filter                       exhaustive
% 54.99/7.49  --prep_sem_filter_out                   false
% 54.99/7.49  --pred_elim                             true
% 54.99/7.49  --res_sim_input                         true
% 54.99/7.49  --eq_ax_congr_red                       true
% 54.99/7.49  --pure_diseq_elim                       true
% 54.99/7.49  --brand_transform                       false
% 54.99/7.49  --non_eq_to_eq                          false
% 54.99/7.49  --prep_def_merge                        true
% 54.99/7.49  --prep_def_merge_prop_impl              false
% 54.99/7.49  --prep_def_merge_mbd                    true
% 54.99/7.49  --prep_def_merge_tr_red                 false
% 54.99/7.49  --prep_def_merge_tr_cl                  false
% 54.99/7.49  --smt_preprocessing                     true
% 54.99/7.49  --smt_ac_axioms                         fast
% 54.99/7.49  --preprocessed_out                      false
% 54.99/7.49  --preprocessed_stats                    false
% 54.99/7.49  
% 54.99/7.49  ------ Abstraction refinement Options
% 54.99/7.49  
% 54.99/7.49  --abstr_ref                             []
% 54.99/7.49  --abstr_ref_prep                        false
% 54.99/7.49  --abstr_ref_until_sat                   false
% 54.99/7.49  --abstr_ref_sig_restrict                funpre
% 54.99/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 54.99/7.49  --abstr_ref_under                       []
% 54.99/7.49  
% 54.99/7.49  ------ SAT Options
% 54.99/7.49  
% 54.99/7.49  --sat_mode                              false
% 54.99/7.49  --sat_fm_restart_options                ""
% 54.99/7.49  --sat_gr_def                            false
% 54.99/7.49  --sat_epr_types                         true
% 54.99/7.49  --sat_non_cyclic_types                  false
% 54.99/7.49  --sat_finite_models                     false
% 54.99/7.49  --sat_fm_lemmas                         false
% 54.99/7.49  --sat_fm_prep                           false
% 54.99/7.49  --sat_fm_uc_incr                        true
% 54.99/7.49  --sat_out_model                         small
% 54.99/7.49  --sat_out_clauses                       false
% 54.99/7.49  
% 54.99/7.49  ------ QBF Options
% 54.99/7.49  
% 54.99/7.49  --qbf_mode                              false
% 54.99/7.49  --qbf_elim_univ                         false
% 54.99/7.49  --qbf_dom_inst                          none
% 54.99/7.49  --qbf_dom_pre_inst                      false
% 54.99/7.49  --qbf_sk_in                             false
% 54.99/7.49  --qbf_pred_elim                         true
% 54.99/7.49  --qbf_split                             512
% 54.99/7.49  
% 54.99/7.49  ------ BMC1 Options
% 54.99/7.49  
% 54.99/7.49  --bmc1_incremental                      false
% 54.99/7.49  --bmc1_axioms                           reachable_all
% 54.99/7.49  --bmc1_min_bound                        0
% 54.99/7.49  --bmc1_max_bound                        -1
% 54.99/7.49  --bmc1_max_bound_default                -1
% 54.99/7.49  --bmc1_symbol_reachability              true
% 54.99/7.49  --bmc1_property_lemmas                  false
% 54.99/7.49  --bmc1_k_induction                      false
% 54.99/7.49  --bmc1_non_equiv_states                 false
% 54.99/7.49  --bmc1_deadlock                         false
% 54.99/7.49  --bmc1_ucm                              false
% 54.99/7.49  --bmc1_add_unsat_core                   none
% 54.99/7.49  --bmc1_unsat_core_children              false
% 54.99/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 54.99/7.49  --bmc1_out_stat                         full
% 54.99/7.49  --bmc1_ground_init                      false
% 54.99/7.49  --bmc1_pre_inst_next_state              false
% 54.99/7.49  --bmc1_pre_inst_state                   false
% 54.99/7.49  --bmc1_pre_inst_reach_state             false
% 54.99/7.49  --bmc1_out_unsat_core                   false
% 54.99/7.49  --bmc1_aig_witness_out                  false
% 54.99/7.49  --bmc1_verbose                          false
% 54.99/7.49  --bmc1_dump_clauses_tptp                false
% 54.99/7.49  --bmc1_dump_unsat_core_tptp             false
% 54.99/7.49  --bmc1_dump_file                        -
% 54.99/7.49  --bmc1_ucm_expand_uc_limit              128
% 54.99/7.49  --bmc1_ucm_n_expand_iterations          6
% 54.99/7.49  --bmc1_ucm_extend_mode                  1
% 54.99/7.49  --bmc1_ucm_init_mode                    2
% 54.99/7.49  --bmc1_ucm_cone_mode                    none
% 54.99/7.49  --bmc1_ucm_reduced_relation_type        0
% 54.99/7.49  --bmc1_ucm_relax_model                  4
% 54.99/7.49  --bmc1_ucm_full_tr_after_sat            true
% 54.99/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 54.99/7.49  --bmc1_ucm_layered_model                none
% 54.99/7.49  --bmc1_ucm_max_lemma_size               10
% 54.99/7.49  
% 54.99/7.49  ------ AIG Options
% 54.99/7.49  
% 54.99/7.49  --aig_mode                              false
% 54.99/7.49  
% 54.99/7.49  ------ Instantiation Options
% 54.99/7.49  
% 54.99/7.49  --instantiation_flag                    true
% 54.99/7.49  --inst_sos_flag                         false
% 54.99/7.49  --inst_sos_phase                        true
% 54.99/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.99/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.99/7.49  --inst_lit_sel_side                     num_symb
% 54.99/7.49  --inst_solver_per_active                1400
% 54.99/7.49  --inst_solver_calls_frac                1.
% 54.99/7.49  --inst_passive_queue_type               priority_queues
% 54.99/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.99/7.49  --inst_passive_queues_freq              [25;2]
% 54.99/7.49  --inst_dismatching                      true
% 54.99/7.49  --inst_eager_unprocessed_to_passive     true
% 54.99/7.49  --inst_prop_sim_given                   true
% 54.99/7.49  --inst_prop_sim_new                     false
% 54.99/7.49  --inst_subs_new                         false
% 54.99/7.49  --inst_eq_res_simp                      false
% 54.99/7.49  --inst_subs_given                       false
% 54.99/7.49  --inst_orphan_elimination               true
% 54.99/7.49  --inst_learning_loop_flag               true
% 54.99/7.49  --inst_learning_start                   3000
% 54.99/7.49  --inst_learning_factor                  2
% 54.99/7.49  --inst_start_prop_sim_after_learn       3
% 54.99/7.49  --inst_sel_renew                        solver
% 54.99/7.49  --inst_lit_activity_flag                true
% 54.99/7.49  --inst_restr_to_given                   false
% 54.99/7.49  --inst_activity_threshold               500
% 54.99/7.49  --inst_out_proof                        true
% 54.99/7.49  
% 54.99/7.49  ------ Resolution Options
% 54.99/7.49  
% 54.99/7.49  --resolution_flag                       true
% 54.99/7.49  --res_lit_sel                           adaptive
% 54.99/7.49  --res_lit_sel_side                      none
% 54.99/7.49  --res_ordering                          kbo
% 54.99/7.49  --res_to_prop_solver                    active
% 54.99/7.49  --res_prop_simpl_new                    false
% 54.99/7.49  --res_prop_simpl_given                  true
% 54.99/7.49  --res_passive_queue_type                priority_queues
% 54.99/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.99/7.49  --res_passive_queues_freq               [15;5]
% 54.99/7.49  --res_forward_subs                      full
% 54.99/7.49  --res_backward_subs                     full
% 54.99/7.49  --res_forward_subs_resolution           true
% 54.99/7.49  --res_backward_subs_resolution          true
% 54.99/7.49  --res_orphan_elimination                true
% 54.99/7.49  --res_time_limit                        2.
% 54.99/7.49  --res_out_proof                         true
% 54.99/7.49  
% 54.99/7.49  ------ Superposition Options
% 54.99/7.49  
% 54.99/7.49  --superposition_flag                    true
% 54.99/7.49  --sup_passive_queue_type                priority_queues
% 54.99/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.99/7.49  --sup_passive_queues_freq               [8;1;4]
% 54.99/7.49  --demod_completeness_check              fast
% 54.99/7.49  --demod_use_ground                      true
% 54.99/7.49  --sup_to_prop_solver                    passive
% 54.99/7.49  --sup_prop_simpl_new                    true
% 54.99/7.49  --sup_prop_simpl_given                  true
% 54.99/7.49  --sup_fun_splitting                     false
% 54.99/7.49  --sup_smt_interval                      50000
% 54.99/7.49  
% 54.99/7.49  ------ Superposition Simplification Setup
% 54.99/7.49  
% 54.99/7.49  --sup_indices_passive                   []
% 54.99/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 54.99/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.99/7.49  --sup_full_bw                           [BwDemod]
% 54.99/7.49  --sup_immed_triv                        [TrivRules]
% 54.99/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.99/7.49  --sup_immed_bw_main                     []
% 54.99/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.99/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 54.99/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.99/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.99/7.49  
% 54.99/7.49  ------ Combination Options
% 54.99/7.49  
% 54.99/7.49  --comb_res_mult                         3
% 54.99/7.49  --comb_sup_mult                         2
% 54.99/7.49  --comb_inst_mult                        10
% 54.99/7.49  
% 54.99/7.49  ------ Debug Options
% 54.99/7.49  
% 54.99/7.49  --dbg_backtrace                         false
% 54.99/7.49  --dbg_dump_prop_clauses                 false
% 54.99/7.49  --dbg_dump_prop_clauses_file            -
% 54.99/7.49  --dbg_out_stat                          false
% 54.99/7.49  ------ Parsing...
% 54.99/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.99/7.49  
% 54.99/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 54.99/7.49  
% 54.99/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.99/7.49  
% 54.99/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.99/7.49  ------ Proving...
% 54.99/7.49  ------ Problem Properties 
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  clauses                                 28
% 54.99/7.49  conjectures                             1
% 54.99/7.49  EPR                                     3
% 54.99/7.49  Horn                                    20
% 54.99/7.49  unary                                   3
% 54.99/7.49  binary                                  9
% 54.99/7.49  lits                                    83
% 54.99/7.49  lits eq                                 6
% 54.99/7.49  fd_pure                                 0
% 54.99/7.49  fd_pseudo                               0
% 54.99/7.49  fd_cond                                 0
% 54.99/7.49  fd_pseudo_cond                          4
% 54.99/7.49  AC symbols                              0
% 54.99/7.49  
% 54.99/7.49  ------ Schedule dynamic 5 is on 
% 54.99/7.49  
% 54.99/7.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  ------ 
% 54.99/7.49  Current options:
% 54.99/7.49  ------ 
% 54.99/7.49  
% 54.99/7.49  ------ Input Options
% 54.99/7.49  
% 54.99/7.49  --out_options                           all
% 54.99/7.49  --tptp_safe_out                         true
% 54.99/7.49  --problem_path                          ""
% 54.99/7.49  --include_path                          ""
% 54.99/7.49  --clausifier                            res/vclausify_rel
% 54.99/7.49  --clausifier_options                    --mode clausify
% 54.99/7.49  --stdin                                 false
% 54.99/7.49  --stats_out                             all
% 54.99/7.49  
% 54.99/7.49  ------ General Options
% 54.99/7.49  
% 54.99/7.49  --fof                                   false
% 54.99/7.49  --time_out_real                         305.
% 54.99/7.49  --time_out_virtual                      -1.
% 54.99/7.49  --symbol_type_check                     false
% 54.99/7.49  --clausify_out                          false
% 54.99/7.49  --sig_cnt_out                           false
% 54.99/7.49  --trig_cnt_out                          false
% 54.99/7.49  --trig_cnt_out_tolerance                1.
% 54.99/7.49  --trig_cnt_out_sk_spl                   false
% 54.99/7.49  --abstr_cl_out                          false
% 54.99/7.49  
% 54.99/7.49  ------ Global Options
% 54.99/7.49  
% 54.99/7.49  --schedule                              default
% 54.99/7.49  --add_important_lit                     false
% 54.99/7.49  --prop_solver_per_cl                    1000
% 54.99/7.49  --min_unsat_core                        false
% 54.99/7.49  --soft_assumptions                      false
% 54.99/7.49  --soft_lemma_size                       3
% 54.99/7.49  --prop_impl_unit_size                   0
% 54.99/7.49  --prop_impl_unit                        []
% 54.99/7.49  --share_sel_clauses                     true
% 54.99/7.49  --reset_solvers                         false
% 54.99/7.49  --bc_imp_inh                            [conj_cone]
% 54.99/7.49  --conj_cone_tolerance                   3.
% 54.99/7.49  --extra_neg_conj                        none
% 54.99/7.49  --large_theory_mode                     true
% 54.99/7.49  --prolific_symb_bound                   200
% 54.99/7.49  --lt_threshold                          2000
% 54.99/7.49  --clause_weak_htbl                      true
% 54.99/7.49  --gc_record_bc_elim                     false
% 54.99/7.49  
% 54.99/7.49  ------ Preprocessing Options
% 54.99/7.49  
% 54.99/7.49  --preprocessing_flag                    true
% 54.99/7.49  --time_out_prep_mult                    0.1
% 54.99/7.49  --splitting_mode                        input
% 54.99/7.49  --splitting_grd                         true
% 54.99/7.49  --splitting_cvd                         false
% 54.99/7.49  --splitting_cvd_svl                     false
% 54.99/7.49  --splitting_nvd                         32
% 54.99/7.49  --sub_typing                            true
% 54.99/7.49  --prep_gs_sim                           true
% 54.99/7.49  --prep_unflatten                        true
% 54.99/7.49  --prep_res_sim                          true
% 54.99/7.49  --prep_upred                            true
% 54.99/7.49  --prep_sem_filter                       exhaustive
% 54.99/7.49  --prep_sem_filter_out                   false
% 54.99/7.49  --pred_elim                             true
% 54.99/7.49  --res_sim_input                         true
% 54.99/7.49  --eq_ax_congr_red                       true
% 54.99/7.49  --pure_diseq_elim                       true
% 54.99/7.49  --brand_transform                       false
% 54.99/7.49  --non_eq_to_eq                          false
% 54.99/7.49  --prep_def_merge                        true
% 54.99/7.49  --prep_def_merge_prop_impl              false
% 54.99/7.49  --prep_def_merge_mbd                    true
% 54.99/7.49  --prep_def_merge_tr_red                 false
% 54.99/7.49  --prep_def_merge_tr_cl                  false
% 54.99/7.49  --smt_preprocessing                     true
% 54.99/7.49  --smt_ac_axioms                         fast
% 54.99/7.49  --preprocessed_out                      false
% 54.99/7.49  --preprocessed_stats                    false
% 54.99/7.49  
% 54.99/7.49  ------ Abstraction refinement Options
% 54.99/7.49  
% 54.99/7.49  --abstr_ref                             []
% 54.99/7.49  --abstr_ref_prep                        false
% 54.99/7.49  --abstr_ref_until_sat                   false
% 54.99/7.49  --abstr_ref_sig_restrict                funpre
% 54.99/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 54.99/7.49  --abstr_ref_under                       []
% 54.99/7.49  
% 54.99/7.49  ------ SAT Options
% 54.99/7.49  
% 54.99/7.49  --sat_mode                              false
% 54.99/7.49  --sat_fm_restart_options                ""
% 54.99/7.49  --sat_gr_def                            false
% 54.99/7.49  --sat_epr_types                         true
% 54.99/7.49  --sat_non_cyclic_types                  false
% 54.99/7.49  --sat_finite_models                     false
% 54.99/7.49  --sat_fm_lemmas                         false
% 54.99/7.49  --sat_fm_prep                           false
% 54.99/7.49  --sat_fm_uc_incr                        true
% 54.99/7.49  --sat_out_model                         small
% 54.99/7.49  --sat_out_clauses                       false
% 54.99/7.49  
% 54.99/7.49  ------ QBF Options
% 54.99/7.49  
% 54.99/7.49  --qbf_mode                              false
% 54.99/7.49  --qbf_elim_univ                         false
% 54.99/7.49  --qbf_dom_inst                          none
% 54.99/7.49  --qbf_dom_pre_inst                      false
% 54.99/7.49  --qbf_sk_in                             false
% 54.99/7.49  --qbf_pred_elim                         true
% 54.99/7.49  --qbf_split                             512
% 54.99/7.49  
% 54.99/7.49  ------ BMC1 Options
% 54.99/7.49  
% 54.99/7.49  --bmc1_incremental                      false
% 54.99/7.49  --bmc1_axioms                           reachable_all
% 54.99/7.49  --bmc1_min_bound                        0
% 54.99/7.49  --bmc1_max_bound                        -1
% 54.99/7.49  --bmc1_max_bound_default                -1
% 54.99/7.49  --bmc1_symbol_reachability              true
% 54.99/7.49  --bmc1_property_lemmas                  false
% 54.99/7.49  --bmc1_k_induction                      false
% 54.99/7.49  --bmc1_non_equiv_states                 false
% 54.99/7.49  --bmc1_deadlock                         false
% 54.99/7.49  --bmc1_ucm                              false
% 54.99/7.49  --bmc1_add_unsat_core                   none
% 54.99/7.49  --bmc1_unsat_core_children              false
% 54.99/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 54.99/7.49  --bmc1_out_stat                         full
% 54.99/7.49  --bmc1_ground_init                      false
% 54.99/7.49  --bmc1_pre_inst_next_state              false
% 54.99/7.49  --bmc1_pre_inst_state                   false
% 54.99/7.49  --bmc1_pre_inst_reach_state             false
% 54.99/7.49  --bmc1_out_unsat_core                   false
% 54.99/7.49  --bmc1_aig_witness_out                  false
% 54.99/7.49  --bmc1_verbose                          false
% 54.99/7.49  --bmc1_dump_clauses_tptp                false
% 54.99/7.49  --bmc1_dump_unsat_core_tptp             false
% 54.99/7.49  --bmc1_dump_file                        -
% 54.99/7.49  --bmc1_ucm_expand_uc_limit              128
% 54.99/7.49  --bmc1_ucm_n_expand_iterations          6
% 54.99/7.49  --bmc1_ucm_extend_mode                  1
% 54.99/7.49  --bmc1_ucm_init_mode                    2
% 54.99/7.49  --bmc1_ucm_cone_mode                    none
% 54.99/7.49  --bmc1_ucm_reduced_relation_type        0
% 54.99/7.49  --bmc1_ucm_relax_model                  4
% 54.99/7.49  --bmc1_ucm_full_tr_after_sat            true
% 54.99/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 54.99/7.49  --bmc1_ucm_layered_model                none
% 54.99/7.49  --bmc1_ucm_max_lemma_size               10
% 54.99/7.49  
% 54.99/7.49  ------ AIG Options
% 54.99/7.49  
% 54.99/7.49  --aig_mode                              false
% 54.99/7.49  
% 54.99/7.49  ------ Instantiation Options
% 54.99/7.49  
% 54.99/7.49  --instantiation_flag                    true
% 54.99/7.49  --inst_sos_flag                         false
% 54.99/7.49  --inst_sos_phase                        true
% 54.99/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.99/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.99/7.49  --inst_lit_sel_side                     none
% 54.99/7.49  --inst_solver_per_active                1400
% 54.99/7.49  --inst_solver_calls_frac                1.
% 54.99/7.49  --inst_passive_queue_type               priority_queues
% 54.99/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.99/7.49  --inst_passive_queues_freq              [25;2]
% 54.99/7.49  --inst_dismatching                      true
% 54.99/7.49  --inst_eager_unprocessed_to_passive     true
% 54.99/7.49  --inst_prop_sim_given                   true
% 54.99/7.49  --inst_prop_sim_new                     false
% 54.99/7.49  --inst_subs_new                         false
% 54.99/7.49  --inst_eq_res_simp                      false
% 54.99/7.49  --inst_subs_given                       false
% 54.99/7.49  --inst_orphan_elimination               true
% 54.99/7.49  --inst_learning_loop_flag               true
% 54.99/7.49  --inst_learning_start                   3000
% 54.99/7.49  --inst_learning_factor                  2
% 54.99/7.49  --inst_start_prop_sim_after_learn       3
% 54.99/7.49  --inst_sel_renew                        solver
% 54.99/7.49  --inst_lit_activity_flag                true
% 54.99/7.49  --inst_restr_to_given                   false
% 54.99/7.49  --inst_activity_threshold               500
% 54.99/7.49  --inst_out_proof                        true
% 54.99/7.49  
% 54.99/7.49  ------ Resolution Options
% 54.99/7.49  
% 54.99/7.49  --resolution_flag                       false
% 54.99/7.49  --res_lit_sel                           adaptive
% 54.99/7.49  --res_lit_sel_side                      none
% 54.99/7.49  --res_ordering                          kbo
% 54.99/7.49  --res_to_prop_solver                    active
% 54.99/7.49  --res_prop_simpl_new                    false
% 54.99/7.49  --res_prop_simpl_given                  true
% 54.99/7.49  --res_passive_queue_type                priority_queues
% 54.99/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.99/7.49  --res_passive_queues_freq               [15;5]
% 54.99/7.49  --res_forward_subs                      full
% 54.99/7.49  --res_backward_subs                     full
% 54.99/7.49  --res_forward_subs_resolution           true
% 54.99/7.49  --res_backward_subs_resolution          true
% 54.99/7.49  --res_orphan_elimination                true
% 54.99/7.49  --res_time_limit                        2.
% 54.99/7.49  --res_out_proof                         true
% 54.99/7.49  
% 54.99/7.49  ------ Superposition Options
% 54.99/7.49  
% 54.99/7.49  --superposition_flag                    true
% 54.99/7.49  --sup_passive_queue_type                priority_queues
% 54.99/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.99/7.49  --sup_passive_queues_freq               [8;1;4]
% 54.99/7.49  --demod_completeness_check              fast
% 54.99/7.49  --demod_use_ground                      true
% 54.99/7.49  --sup_to_prop_solver                    passive
% 54.99/7.49  --sup_prop_simpl_new                    true
% 54.99/7.49  --sup_prop_simpl_given                  true
% 54.99/7.49  --sup_fun_splitting                     false
% 54.99/7.49  --sup_smt_interval                      50000
% 54.99/7.49  
% 54.99/7.49  ------ Superposition Simplification Setup
% 54.99/7.49  
% 54.99/7.49  --sup_indices_passive                   []
% 54.99/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.99/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 54.99/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.99/7.49  --sup_full_bw                           [BwDemod]
% 54.99/7.49  --sup_immed_triv                        [TrivRules]
% 54.99/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.99/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.99/7.49  --sup_immed_bw_main                     []
% 54.99/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.99/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 54.99/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.99/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.99/7.49  
% 54.99/7.49  ------ Combination Options
% 54.99/7.49  
% 54.99/7.49  --comb_res_mult                         3
% 54.99/7.49  --comb_sup_mult                         2
% 54.99/7.49  --comb_inst_mult                        10
% 54.99/7.49  
% 54.99/7.49  ------ Debug Options
% 54.99/7.49  
% 54.99/7.49  --dbg_backtrace                         false
% 54.99/7.49  --dbg_dump_prop_clauses                 false
% 54.99/7.49  --dbg_dump_prop_clauses_file            -
% 54.99/7.49  --dbg_out_stat                          false
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  ------ Proving...
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  % SZS status Theorem for theBenchmark.p
% 54.99/7.49  
% 54.99/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 54.99/7.49  
% 54.99/7.49  fof(f1,axiom,(
% 54.99/7.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f18,plain,(
% 54.99/7.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 54.99/7.49    inference(ennf_transformation,[],[f1])).
% 54.99/7.49  
% 54.99/7.49  fof(f38,plain,(
% 54.99/7.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 54.99/7.49    inference(nnf_transformation,[],[f18])).
% 54.99/7.49  
% 54.99/7.49  fof(f39,plain,(
% 54.99/7.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 54.99/7.49    inference(rectify,[],[f38])).
% 54.99/7.49  
% 54.99/7.49  fof(f40,plain,(
% 54.99/7.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f41,plain,(
% 54.99/7.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 54.99/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 54.99/7.49  
% 54.99/7.49  fof(f63,plain,(
% 54.99/7.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f41])).
% 54.99/7.49  
% 54.99/7.49  fof(f35,plain,(
% 54.99/7.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 54.99/7.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 54.99/7.49  
% 54.99/7.49  fof(f49,plain,(
% 54.99/7.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((! [X4] : (~r2_hidden(X4,X1) | ~r1_orders_2(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r1_orders_2(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)))) & (? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 54.99/7.49    inference(nnf_transformation,[],[f35])).
% 54.99/7.49  
% 54.99/7.49  fof(f50,plain,(
% 54.99/7.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r1_orders_2(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r1_orders_2(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)))) & (? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 54.99/7.49    inference(flattening,[],[f49])).
% 54.99/7.49  
% 54.99/7.49  fof(f51,plain,(
% 54.99/7.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r2_hidden(X4,X0) | ~r1_orders_2(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X0) & r1_orders_2(X1,X5,X3) & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X0) | ~r1_orders_2(X1,X7,X6) | ~m1_subset_1(X7,u1_struct_0(X1)))) & (? [X8] : (r2_hidden(X8,X0) & r1_orders_2(X1,X8,X6) & m1_subset_1(X8,u1_struct_0(X1))) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 54.99/7.49    inference(rectify,[],[f50])).
% 54.99/7.49  
% 54.99/7.49  fof(f54,plain,(
% 54.99/7.49    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X0) & r1_orders_2(X1,X8,X6) & m1_subset_1(X8,u1_struct_0(X1))) => (r2_hidden(sK6(X0,X1,X6),X0) & r1_orders_2(X1,sK6(X0,X1,X6),X6) & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1))))),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f53,plain,(
% 54.99/7.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X0) & r1_orders_2(X1,X5,X3) & m1_subset_1(X5,u1_struct_0(X1))) => (r2_hidden(sK5(X0,X1,X2),X0) & r1_orders_2(X1,sK5(X0,X1,X2),X3) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))) )),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f52,plain,(
% 54.99/7.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X0) | ~r1_orders_2(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X0) & r1_orders_2(X1,X5,X3) & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X1))) => ((! [X4] : (~r2_hidden(X4,X0) | ~r1_orders_2(X1,X4,sK4(X0,X1,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X0) & r1_orders_2(X1,X5,sK4(X0,X1,X2)) & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f55,plain,(
% 54.99/7.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r2_hidden(X4,X0) | ~r1_orders_2(X1,X4,sK4(X0,X1,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X0) | ~r1_orders_2(X1,X7,X6) | ~m1_subset_1(X7,u1_struct_0(X1)))) & ((r2_hidden(sK6(X0,X1,X6),X0) & r1_orders_2(X1,sK6(X0,X1,X6),X6) & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1))) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 54.99/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).
% 54.99/7.49  
% 54.99/7.49  fof(f82,plain,(
% 54.99/7.49    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X0) | ~r1_orders_2(X1,X7,X6) | ~m1_subset_1(X7,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f55])).
% 54.99/7.49  
% 54.99/7.49  fof(f9,axiom,(
% 54.99/7.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f28,plain,(
% 54.99/7.49    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 54.99/7.49    inference(ennf_transformation,[],[f9])).
% 54.99/7.49  
% 54.99/7.49  fof(f29,plain,(
% 54.99/7.49    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 54.99/7.49    inference(flattening,[],[f28])).
% 54.99/7.49  
% 54.99/7.49  fof(f76,plain,(
% 54.99/7.49    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f29])).
% 54.99/7.49  
% 54.99/7.49  fof(f13,conjecture,(
% 54.99/7.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f14,negated_conjecture,(
% 54.99/7.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 54.99/7.49    inference(negated_conjecture,[],[f13])).
% 54.99/7.49  
% 54.99/7.49  fof(f15,plain,(
% 54.99/7.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 54.99/7.49    inference(pure_predicate_removal,[],[f14])).
% 54.99/7.49  
% 54.99/7.49  fof(f16,plain,(
% 54.99/7.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 54.99/7.49    inference(pure_predicate_removal,[],[f15])).
% 54.99/7.49  
% 54.99/7.49  fof(f17,plain,(
% 54.99/7.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 54.99/7.49    inference(pure_predicate_removal,[],[f16])).
% 54.99/7.49  
% 54.99/7.49  fof(f33,plain,(
% 54.99/7.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 54.99/7.49    inference(ennf_transformation,[],[f17])).
% 54.99/7.49  
% 54.99/7.49  fof(f34,plain,(
% 54.99/7.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 54.99/7.49    inference(flattening,[],[f33])).
% 54.99/7.49  
% 54.99/7.49  fof(f58,plain,(
% 54.99/7.49    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 54.99/7.49    inference(nnf_transformation,[],[f34])).
% 54.99/7.49  
% 54.99/7.49  fof(f59,plain,(
% 54.99/7.49    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 54.99/7.49    inference(flattening,[],[f58])).
% 54.99/7.49  
% 54.99/7.49  fof(f61,plain,(
% 54.99/7.49    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK8) | ~v1_subset_1(sK8,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK8) | v1_subset_1(sK8,u1_struct_0(X0))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK8,X0) & ~v1_xboole_0(sK8))) )),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f60,plain,(
% 54.99/7.49    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK7),X1) | ~v1_subset_1(X1,u1_struct_0(sK7))) & (~r2_hidden(k3_yellow_0(sK7),X1) | v1_subset_1(X1,u1_struct_0(sK7))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) & v13_waybel_0(X1,sK7) & ~v1_xboole_0(X1)) & l1_orders_2(sK7) & v1_yellow_0(sK7) & v5_orders_2(sK7) & ~v2_struct_0(sK7))),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f62,plain,(
% 54.99/7.49    ((r2_hidden(k3_yellow_0(sK7),sK8) | ~v1_subset_1(sK8,u1_struct_0(sK7))) & (~r2_hidden(k3_yellow_0(sK7),sK8) | v1_subset_1(sK8,u1_struct_0(sK7))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) & v13_waybel_0(sK8,sK7) & ~v1_xboole_0(sK8)) & l1_orders_2(sK7) & v1_yellow_0(sK7) & v5_orders_2(sK7) & ~v2_struct_0(sK7)),
% 54.99/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f59,f61,f60])).
% 54.99/7.49  
% 54.99/7.49  fof(f95,plain,(
% 54.99/7.49    v1_yellow_0(sK7)),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f93,plain,(
% 54.99/7.49    ~v2_struct_0(sK7)),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f94,plain,(
% 54.99/7.49    v5_orders_2(sK7)),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f96,plain,(
% 54.99/7.49    l1_orders_2(sK7)),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f87,plain,(
% 54.99/7.49    ( ! [X4,X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | ~r1_orders_2(X1,X4,sK4(X0,X1,X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f55])).
% 54.99/7.49  
% 54.99/7.49  fof(f3,axiom,(
% 54.99/7.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f20,plain,(
% 54.99/7.49    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(ennf_transformation,[],[f3])).
% 54.99/7.49  
% 54.99/7.49  fof(f21,plain,(
% 54.99/7.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(flattening,[],[f20])).
% 54.99/7.49  
% 54.99/7.49  fof(f42,plain,(
% 54.99/7.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(nnf_transformation,[],[f21])).
% 54.99/7.49  
% 54.99/7.49  fof(f43,plain,(
% 54.99/7.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(flattening,[],[f42])).
% 54.99/7.49  
% 54.99/7.49  fof(f44,plain,(
% 54.99/7.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 54.99/7.49    introduced(choice_axiom,[])).
% 54.99/7.49  
% 54.99/7.49  fof(f45,plain,(
% 54.99/7.49    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 54.99/7.49  
% 54.99/7.49  fof(f69,plain,(
% 54.99/7.49    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.99/7.49    inference(cnf_transformation,[],[f45])).
% 54.99/7.49  
% 54.99/7.49  fof(f6,axiom,(
% 54.99/7.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f46,plain,(
% 54.99/7.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 54.99/7.49    inference(nnf_transformation,[],[f6])).
% 54.99/7.49  
% 54.99/7.49  fof(f73,plain,(
% 54.99/7.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f46])).
% 54.99/7.49  
% 54.99/7.49  fof(f67,plain,(
% 54.99/7.49    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.99/7.49    inference(cnf_transformation,[],[f45])).
% 54.99/7.49  
% 54.99/7.49  fof(f11,axiom,(
% 54.99/7.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> r1_tarski(k4_waybel_0(X0,X1),X1))))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f31,plain,(
% 54.99/7.49    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> r1_tarski(k4_waybel_0(X0,X1),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 54.99/7.49    inference(ennf_transformation,[],[f11])).
% 54.99/7.49  
% 54.99/7.49  fof(f56,plain,(
% 54.99/7.49    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ~r1_tarski(k4_waybel_0(X0,X1),X1)) & (r1_tarski(k4_waybel_0(X0,X1),X1) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 54.99/7.49    inference(nnf_transformation,[],[f31])).
% 54.99/7.49  
% 54.99/7.49  fof(f89,plain,(
% 54.99/7.49    ( ! [X0,X1] : (r1_tarski(k4_waybel_0(X0,X1),X1) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f56])).
% 54.99/7.49  
% 54.99/7.49  fof(f98,plain,(
% 54.99/7.49    v13_waybel_0(sK8,sK7)),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f99,plain,(
% 54.99/7.49    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f64,plain,(
% 54.99/7.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f41])).
% 54.99/7.49  
% 54.99/7.49  fof(f65,plain,(
% 54.99/7.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f41])).
% 54.99/7.49  
% 54.99/7.49  fof(f36,plain,(
% 54.99/7.49    ! [X2,X0,X1] : ((k4_waybel_0(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 54.99/7.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 54.99/7.49  
% 54.99/7.49  fof(f47,plain,(
% 54.99/7.49    ! [X2,X0,X1] : (((k4_waybel_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_waybel_0(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 54.99/7.49    inference(nnf_transformation,[],[f36])).
% 54.99/7.49  
% 54.99/7.49  fof(f48,plain,(
% 54.99/7.49    ! [X0,X1,X2] : (((k4_waybel_0(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k4_waybel_0(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 54.99/7.49    inference(rectify,[],[f47])).
% 54.99/7.49  
% 54.99/7.49  fof(f77,plain,(
% 54.99/7.49    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k4_waybel_0(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f48])).
% 54.99/7.49  
% 54.99/7.49  fof(f102,plain,(
% 54.99/7.49    ( ! [X2,X1] : (sP0(X2,X1,k4_waybel_0(X1,X2)) | ~sP1(k4_waybel_0(X1,X2),X1,X2)) )),
% 54.99/7.49    inference(equality_resolution,[],[f77])).
% 54.99/7.49  
% 54.99/7.49  fof(f10,axiom,(
% 54.99/7.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k4_waybel_0(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0)))))))))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f30,plain,(
% 54.99/7.49    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_0(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r1_orders_2(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 54.99/7.49    inference(ennf_transformation,[],[f10])).
% 54.99/7.49  
% 54.99/7.49  fof(f37,plain,(
% 54.99/7.49    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 54.99/7.49    inference(definition_folding,[],[f30,f36,f35])).
% 54.99/7.49  
% 54.99/7.49  fof(f88,plain,(
% 54.99/7.49    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f37])).
% 54.99/7.49  
% 54.99/7.49  fof(f83,plain,(
% 54.99/7.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) )),
% 54.99/7.49    inference(cnf_transformation,[],[f55])).
% 54.99/7.49  
% 54.99/7.49  fof(f72,plain,(
% 54.99/7.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 54.99/7.49    inference(cnf_transformation,[],[f46])).
% 54.99/7.49  
% 54.99/7.49  fof(f12,axiom,(
% 54.99/7.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f32,plain,(
% 54.99/7.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(ennf_transformation,[],[f12])).
% 54.99/7.49  
% 54.99/7.49  fof(f57,plain,(
% 54.99/7.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.99/7.49    inference(nnf_transformation,[],[f32])).
% 54.99/7.49  
% 54.99/7.49  fof(f92,plain,(
% 54.99/7.49    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.99/7.49    inference(cnf_transformation,[],[f57])).
% 54.99/7.49  
% 54.99/7.49  fof(f101,plain,(
% 54.99/7.49    r2_hidden(k3_yellow_0(sK7),sK8) | ~v1_subset_1(sK8,u1_struct_0(sK7))),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f8,axiom,(
% 54.99/7.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f27,plain,(
% 54.99/7.49    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 54.99/7.49    inference(ennf_transformation,[],[f8])).
% 54.99/7.49  
% 54.99/7.49  fof(f75,plain,(
% 54.99/7.49    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f27])).
% 54.99/7.49  
% 54.99/7.49  fof(f5,axiom,(
% 54.99/7.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 54.99/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 54.99/7.49  
% 54.99/7.49  fof(f23,plain,(
% 54.99/7.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 54.99/7.49    inference(ennf_transformation,[],[f5])).
% 54.99/7.49  
% 54.99/7.49  fof(f24,plain,(
% 54.99/7.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 54.99/7.49    inference(flattening,[],[f23])).
% 54.99/7.49  
% 54.99/7.49  fof(f71,plain,(
% 54.99/7.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 54.99/7.49    inference(cnf_transformation,[],[f24])).
% 54.99/7.49  
% 54.99/7.49  fof(f97,plain,(
% 54.99/7.49    ~v1_xboole_0(sK8)),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  fof(f91,plain,(
% 54.99/7.49    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.99/7.49    inference(cnf_transformation,[],[f57])).
% 54.99/7.49  
% 54.99/7.49  fof(f103,plain,(
% 54.99/7.49    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 54.99/7.49    inference(equality_resolution,[],[f91])).
% 54.99/7.49  
% 54.99/7.49  fof(f100,plain,(
% 54.99/7.49    ~r2_hidden(k3_yellow_0(sK7),sK8) | v1_subset_1(sK8,u1_struct_0(sK7))),
% 54.99/7.49    inference(cnf_transformation,[],[f62])).
% 54.99/7.49  
% 54.99/7.49  cnf(c_2,plain,
% 54.99/7.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 54.99/7.49      inference(cnf_transformation,[],[f63]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_172769,plain,
% 54.99/7.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,sK8) | ~ r1_tarski(sK8,X1) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_2]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_177011,plain,
% 54.99/7.49      ( r2_hidden(X0,u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(X0,sK8)
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_172769]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_186462,plain,
% 54.99/7.49      ( r2_hidden(sK3(X0,sK8,X1),u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(sK3(X0,sK8,X1),sK8)
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_177011]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_215990,plain,
% 54.99/7.49      ( r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_186462]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_177059,plain,
% 54.99/7.49      ( r2_hidden(X0,X1)
% 54.99/7.49      | ~ r2_hidden(X0,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r1_tarski(k4_waybel_0(sK7,sK8),X1) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_2]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_183459,plain,
% 54.99/7.49      ( ~ r2_hidden(X0,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | r2_hidden(X0,sK8)
% 54.99/7.49      | ~ r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_177059]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_191329,plain,
% 54.99/7.49      ( ~ r2_hidden(sK4(sK8,X0,sK8),k4_waybel_0(sK7,sK8))
% 54.99/7.49      | r2_hidden(sK4(sK8,X0,sK8),sK8)
% 54.99/7.49      | ~ r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_183459]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_191331,plain,
% 54.99/7.49      ( ~ r2_hidden(sK4(sK8,sK7,sK8),k4_waybel_0(sK7,sK8))
% 54.99/7.49      | r2_hidden(sK4(sK8,sK7,sK8),sK8)
% 54.99/7.49      | ~ r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_191329]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_21,plain,
% 54.99/7.49      ( ~ sP0(X0,X1,X2)
% 54.99/7.49      | ~ r1_orders_2(X1,X3,X4)
% 54.99/7.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 54.99/7.49      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 54.99/7.49      | ~ r2_hidden(X3,X0)
% 54.99/7.49      | r2_hidden(X4,X2) ),
% 54.99/7.49      inference(cnf_transformation,[],[f82]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_6658,plain,
% 54.99/7.49      ( ~ sP0(sK8,X0,X1)
% 54.99/7.49      | ~ r1_orders_2(X0,k3_yellow_0(X2),X3)
% 54.99/7.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X2),u1_struct_0(X0))
% 54.99/7.49      | r2_hidden(X3,X1)
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X2),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_21]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7983,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(X0),X1)
% 54.99/7.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(X1,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_6658]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_12154,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK4(X1,sK7,X2))
% 54.99/7.49      | ~ m1_subset_1(sK4(X1,sK7,X2),u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(sK4(X1,sK7,X2),k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_7983]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_32056,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK4(X1,sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(sK4(X1,sK7,sK8),u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(sK4(X1,sK7,sK8),k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_12154]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_70325,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK4(sK8,sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(sK4(sK8,sK7,sK8),k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_32056]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_70327,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(sK7),sK4(sK8,sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(sK4(sK8,sK7,sK8),k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_70325]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_13,plain,
% 54.99/7.49      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 54.99/7.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 54.99/7.49      | v2_struct_0(X0)
% 54.99/7.49      | ~ v5_orders_2(X0)
% 54.99/7.49      | ~ v1_yellow_0(X0)
% 54.99/7.49      | ~ l1_orders_2(X0) ),
% 54.99/7.49      inference(cnf_transformation,[],[f76]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_36,negated_conjecture,
% 54.99/7.49      ( v1_yellow_0(sK7) ),
% 54.99/7.49      inference(cnf_transformation,[],[f95]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_548,plain,
% 54.99/7.49      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 54.99/7.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 54.99/7.49      | v2_struct_0(X0)
% 54.99/7.49      | ~ v5_orders_2(X0)
% 54.99/7.49      | ~ l1_orders_2(X0)
% 54.99/7.49      | sK7 != X0 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_13,c_36]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_549,plain,
% 54.99/7.49      ( r1_orders_2(sK7,k3_yellow_0(sK7),X0)
% 54.99/7.49      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 54.99/7.49      | v2_struct_0(sK7)
% 54.99/7.49      | ~ v5_orders_2(sK7)
% 54.99/7.49      | ~ l1_orders_2(sK7) ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_548]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_38,negated_conjecture,
% 54.99/7.49      ( ~ v2_struct_0(sK7) ),
% 54.99/7.49      inference(cnf_transformation,[],[f93]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_37,negated_conjecture,
% 54.99/7.49      ( v5_orders_2(sK7) ),
% 54.99/7.49      inference(cnf_transformation,[],[f94]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_35,negated_conjecture,
% 54.99/7.49      ( l1_orders_2(sK7) ),
% 54.99/7.49      inference(cnf_transformation,[],[f96]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_553,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 54.99/7.49      | r1_orders_2(sK7,k3_yellow_0(sK7),X0) ),
% 54.99/7.49      inference(global_propositional_subsumption,
% 54.99/7.49                [status(thm)],
% 54.99/7.49                [c_549,c_38,c_37,c_35]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_554,plain,
% 54.99/7.49      ( r1_orders_2(sK7,k3_yellow_0(sK7),X0)
% 54.99/7.49      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(renaming,[status(thm)],[c_553]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5040,plain,
% 54.99/7.49      ( r1_orders_2(sK7,k3_yellow_0(sK7),sK4(X0,sK7,X1))
% 54.99/7.49      | ~ m1_subset_1(sK4(X0,sK7,X1),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_554]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_27949,plain,
% 54.99/7.49      ( r1_orders_2(sK7,k3_yellow_0(sK7),sK4(X0,sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(sK4(X0,sK7,sK8),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_5040]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_55980,plain,
% 54.99/7.49      ( r1_orders_2(sK7,k3_yellow_0(sK7),sK4(sK8,sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_27949]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_16,plain,
% 54.99/7.49      ( sP0(X0,X1,X2)
% 54.99/7.49      | ~ r1_orders_2(X1,X3,sK4(X0,X1,X2))
% 54.99/7.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 54.99/7.49      | ~ r2_hidden(X3,X0)
% 54.99/7.49      | ~ r2_hidden(sK4(X0,X1,X2),X2) ),
% 54.99/7.49      inference(cnf_transformation,[],[f87]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7275,plain,
% 54.99/7.49      ( sP0(sK8,X0,X1)
% 54.99/7.49      | ~ r1_orders_2(X0,X2,sK4(sK8,X0,X1))
% 54.99/7.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 54.99/7.49      | ~ r2_hidden(X2,sK8)
% 54.99/7.49      | ~ r2_hidden(sK4(sK8,X0,X1),X1) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_16]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_13544,plain,
% 54.99/7.49      ( sP0(sK8,X0,sK8)
% 54.99/7.49      | ~ r1_orders_2(X0,X1,sK4(sK8,X0,sK8))
% 54.99/7.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 54.99/7.49      | ~ r2_hidden(X1,sK8)
% 54.99/7.49      | ~ r2_hidden(sK4(sK8,X0,sK8),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_7275]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_31754,plain,
% 54.99/7.49      ( sP0(sK8,X0,sK8)
% 54.99/7.49      | ~ r1_orders_2(X0,k3_yellow_0(sK7),sK4(sK8,X0,sK8))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(X0))
% 54.99/7.49      | ~ r2_hidden(sK4(sK8,X0,sK8),sK8)
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_13544]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_31756,plain,
% 54.99/7.49      ( sP0(sK8,sK7,sK8)
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(sK7),sK4(sK8,sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(sK4(sK8,sK7,sK8),sK8)
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_31754]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_26369,plain,
% 54.99/7.49      ( r1_orders_2(sK7,k3_yellow_0(sK7),sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)))
% 54.99/7.49      | ~ m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_554]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7988,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,sK8)
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(X0),X1)
% 54.99/7.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(X1,sK8)
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_6658]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_24068,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,sK8)
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(X0),sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)))
% 54.99/7.49      | ~ m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(X0),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_7988]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_24075,plain,
% 54.99/7.49      ( ~ sP0(sK8,sK7,sK8)
% 54.99/7.49      | ~ r1_orders_2(sK7,k3_yellow_0(sK7),sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)))
% 54.99/7.49      | ~ m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_24068]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.99/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 54.99/7.49      | ~ r2_hidden(sK3(X1,X0,X2),X2)
% 54.99/7.49      | ~ r2_hidden(sK3(X1,X0,X2),X0)
% 54.99/7.49      | X2 = X0 ),
% 54.99/7.49      inference(cnf_transformation,[],[f69]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_9,plain,
% 54.99/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f73]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_301,plain,
% 54.99/7.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 54.99/7.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_302,plain,
% 54.99/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 54.99/7.49      inference(renaming,[status(thm)],[c_301]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_384,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.99/7.49      | ~ r2_hidden(sK3(X1,X2,X0),X0)
% 54.99/7.49      | ~ r2_hidden(sK3(X1,X2,X0),X2)
% 54.99/7.49      | ~ r1_tarski(X2,X1)
% 54.99/7.49      | X0 = X2 ),
% 54.99/7.49      inference(bin_hyper_res,[status(thm)],[c_4,c_302]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_2542,plain,
% 54.99/7.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 54.99/7.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_2543,plain,
% 54.99/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 54.99/7.49      inference(renaming,[status(thm)],[c_2542]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_2601,plain,
% 54.99/7.49      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
% 54.99/7.49      | ~ r2_hidden(sK3(X0,X1,X2),X1)
% 54.99/7.49      | ~ r1_tarski(X2,X0)
% 54.99/7.49      | ~ r1_tarski(X1,X0)
% 54.99/7.49      | X2 = X1 ),
% 54.99/7.49      inference(bin_hyper_res,[status(thm)],[c_384,c_2543]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4858,plain,
% 54.99/7.49      ( ~ r2_hidden(sK3(X0,X1,u1_struct_0(sK7)),X1)
% 54.99/7.49      | ~ r2_hidden(sK3(X0,X1,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(X1,X0)
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),X0)
% 54.99/7.49      | u1_struct_0(sK7) = X1 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_2601]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_8875,plain,
% 54.99/7.49      ( ~ r2_hidden(sK3(u1_struct_0(sK7),X0,u1_struct_0(sK7)),X0)
% 54.99/7.49      | ~ r2_hidden(sK3(u1_struct_0(sK7),X0,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(X0,u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | u1_struct_0(sK7) = X0 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4858]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_19864,plain,
% 54.99/7.49      ( ~ r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8)
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7))
% 54.99/7.49      | u1_struct_0(sK7) = sK8 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_8875]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_6,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.99/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 54.99/7.49      | m1_subset_1(sK3(X1,X0,X2),X1)
% 54.99/7.49      | X2 = X0 ),
% 54.99/7.49      inference(cnf_transformation,[],[f67]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_386,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.99/7.49      | m1_subset_1(sK3(X1,X2,X0),X1)
% 54.99/7.49      | ~ r1_tarski(X2,X1)
% 54.99/7.49      | X0 = X2 ),
% 54.99/7.49      inference(bin_hyper_res,[status(thm)],[c_6,c_302]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_2603,plain,
% 54.99/7.49      ( m1_subset_1(sK3(X0,X1,X2),X0)
% 54.99/7.49      | ~ r1_tarski(X2,X0)
% 54.99/7.49      | ~ r1_tarski(X1,X0)
% 54.99/7.49      | X2 = X1 ),
% 54.99/7.49      inference(bin_hyper_res,[status(thm)],[c_386,c_2543]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4859,plain,
% 54.99/7.49      ( m1_subset_1(sK3(X0,X1,u1_struct_0(sK7)),X0)
% 54.99/7.49      | ~ r1_tarski(X1,X0)
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),X0)
% 54.99/7.49      | u1_struct_0(sK7) = X1 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_2603]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_8877,plain,
% 54.99/7.49      ( m1_subset_1(sK3(u1_struct_0(sK7),X0,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(X0,u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | u1_struct_0(sK7) = X0 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4859]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_19084,plain,
% 54.99/7.49      ( m1_subset_1(sK3(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7))
% 54.99/7.49      | u1_struct_0(sK7) = sK8 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_8877]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_27,plain,
% 54.99/7.49      ( ~ v13_waybel_0(X0,X1)
% 54.99/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.99/7.49      | r1_tarski(k4_waybel_0(X1,X0),X0)
% 54.99/7.49      | ~ l1_orders_2(X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f89]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_33,negated_conjecture,
% 54.99/7.49      ( v13_waybel_0(sK8,sK7) ),
% 54.99/7.49      inference(cnf_transformation,[],[f98]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_617,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.99/7.49      | r1_tarski(k4_waybel_0(X1,X0),X0)
% 54.99/7.49      | ~ l1_orders_2(X1)
% 54.99/7.49      | sK8 != X0
% 54.99/7.49      | sK7 != X1 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_618,plain,
% 54.99/7.49      ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | r1_tarski(k4_waybel_0(sK7,sK8),sK8)
% 54.99/7.49      | ~ l1_orders_2(sK7) ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_617]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_32,negated_conjecture,
% 54.99/7.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 54.99/7.49      inference(cnf_transformation,[],[f99]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_620,plain,
% 54.99/7.49      ( r1_tarski(k4_waybel_0(sK7,sK8),sK8) ),
% 54.99/7.49      inference(global_propositional_subsumption,
% 54.99/7.49                [status(thm)],
% 54.99/7.49                [c_618,c_35,c_32]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4289,plain,
% 54.99/7.49      ( r1_tarski(k4_waybel_0(sK7,sK8),sK8) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_1,plain,
% 54.99/7.49      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f64]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4307,plain,
% 54.99/7.49      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 54.99/7.49      | r1_tarski(X0,X1) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4306,plain,
% 54.99/7.49      ( r2_hidden(X0,X1) != iProver_top
% 54.99/7.49      | r2_hidden(X0,X2) = iProver_top
% 54.99/7.49      | r1_tarski(X1,X2) != iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5555,plain,
% 54.99/7.49      ( r2_hidden(sK2(X0,X1),X2) = iProver_top
% 54.99/7.49      | r1_tarski(X0,X2) != iProver_top
% 54.99/7.49      | r1_tarski(X0,X1) = iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_4307,c_4306]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_10018,plain,
% 54.99/7.49      ( r2_hidden(sK2(X0,X1),X2) = iProver_top
% 54.99/7.49      | r1_tarski(X0,X3) != iProver_top
% 54.99/7.49      | r1_tarski(X3,X2) != iProver_top
% 54.99/7.49      | r1_tarski(X0,X1) = iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_5555,c_4306]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_16321,plain,
% 54.99/7.49      ( r2_hidden(sK2(k4_waybel_0(sK7,sK8),X0),X1) = iProver_top
% 54.99/7.49      | r1_tarski(k4_waybel_0(sK7,sK8),X0) = iProver_top
% 54.99/7.49      | r1_tarski(sK8,X1) != iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_4289,c_10018]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_0,plain,
% 54.99/7.49      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f65]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4308,plain,
% 54.99/7.49      ( r2_hidden(sK2(X0,X1),X1) != iProver_top
% 54.99/7.49      | r1_tarski(X0,X1) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_16904,plain,
% 54.99/7.49      ( r1_tarski(k4_waybel_0(sK7,sK8),X0) = iProver_top
% 54.99/7.49      | r1_tarski(sK8,X0) != iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_16321,c_4308]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4304,plain,
% 54.99/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 54.99/7.49      | r1_tarski(X0,X1) != iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_15,plain,
% 54.99/7.49      ( ~ sP1(k4_waybel_0(X0,X1),X0,X1) | sP0(X1,X0,k4_waybel_0(X0,X1)) ),
% 54.99/7.49      inference(cnf_transformation,[],[f102]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_25,plain,
% 54.99/7.49      ( sP1(X0,X1,X2)
% 54.99/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.99/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 54.99/7.49      | ~ l1_orders_2(X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f88]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_637,plain,
% 54.99/7.49      ( sP1(X0,X1,X2)
% 54.99/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 54.99/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 54.99/7.49      | sK7 != X1 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_638,plain,
% 54.99/7.49      ( sP1(X0,sK7,X1)
% 54.99/7.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_637]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_676,plain,
% 54.99/7.49      ( sP0(X0,X1,k4_waybel_0(X1,X0))
% 54.99/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | X3 != X0
% 54.99/7.49      | k4_waybel_0(X1,X0) != X2
% 54.99/7.49      | sK7 != X1 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_15,c_638]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_677,plain,
% 54.99/7.49      ( sP0(X0,sK7,k4_waybel_0(sK7,X0))
% 54.99/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ m1_subset_1(k4_waybel_0(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_676]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4286,plain,
% 54.99/7.49      ( sP0(X0,sK7,k4_waybel_0(sK7,X0)) = iProver_top
% 54.99/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 54.99/7.49      | m1_subset_1(k4_waybel_0(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4919,plain,
% 54.99/7.49      ( sP0(X0,sK7,k4_waybel_0(sK7,X0)) = iProver_top
% 54.99/7.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 54.99/7.49      | r1_tarski(k4_waybel_0(sK7,X0),u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_4304,c_4286]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_17128,plain,
% 54.99/7.49      ( sP0(sK8,sK7,k4_waybel_0(sK7,sK8)) = iProver_top
% 54.99/7.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 54.99/7.49      | r1_tarski(sK8,u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_16904,c_4919]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_17138,plain,
% 54.99/7.49      ( sP0(sK8,sK7,k4_waybel_0(sK7,sK8))
% 54.99/7.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_17128]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4554,plain,
% 54.99/7.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ r1_tarski(X0,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_9]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_8872,plain,
% 54.99/7.49      ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4554]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_20,plain,
% 54.99/7.49      ( sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ),
% 54.99/7.49      inference(cnf_transformation,[],[f83]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5039,plain,
% 54.99/7.49      ( sP0(X0,sK7,X1) | m1_subset_1(sK4(X0,sK7,X1),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_20]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_6806,plain,
% 54.99/7.49      ( sP0(X0,sK7,sK8) | m1_subset_1(sK4(X0,sK7,sK8),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_5039]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7994,plain,
% 54.99/7.49      ( sP0(sK8,sK7,sK8)
% 54.99/7.49      | m1_subset_1(sK4(sK8,sK7,sK8),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_6806]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_10,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f72]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_299,plain,
% 54.99/7.49      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 54.99/7.49      inference(prop_impl,[status(thm)],[c_10]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_300,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 54.99/7.49      inference(renaming,[status(thm)],[c_299]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_28,plain,
% 54.99/7.49      ( v1_subset_1(X0,X1)
% 54.99/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.99/7.49      | X0 = X1 ),
% 54.99/7.49      inference(cnf_transformation,[],[f92]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_389,plain,
% 54.99/7.49      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 54.99/7.49      inference(bin_hyper_res,[status(thm)],[c_28,c_302]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_30,negated_conjecture,
% 54.99/7.49      ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(cnf_transformation,[],[f101]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_305,plain,
% 54.99/7.49      ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(prop_impl,[status(thm)],[c_30]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_703,plain,
% 54.99/7.49      ( r2_hidden(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | ~ r1_tarski(X0,X1)
% 54.99/7.49      | X1 = X0
% 54.99/7.49      | u1_struct_0(sK7) != X1
% 54.99/7.49      | sK8 != X0 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_389,c_305]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_704,plain,
% 54.99/7.49      ( r2_hidden(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | ~ r1_tarski(sK8,u1_struct_0(sK7))
% 54.99/7.49      | u1_struct_0(sK7) = sK8 ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_703]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_1138,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | u1_struct_0(sK7) != X1
% 54.99/7.49      | u1_struct_0(sK7) = sK8
% 54.99/7.49      | sK8 != X0 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_300,c_704]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_1139,plain,
% 54.99/7.49      ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | u1_struct_0(sK7) = sK8 ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_1138]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_1141,plain,
% 54.99/7.49      ( r2_hidden(k3_yellow_0(sK7),sK8) | u1_struct_0(sK7) = sK8 ),
% 54.99/7.49      inference(global_propositional_subsumption,
% 54.99/7.49                [status(thm)],
% 54.99/7.49                [c_1139,c_32]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4284,plain,
% 54.99/7.49      ( u1_struct_0(sK7) = sK8
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_42,plain,
% 54.99/7.49      ( l1_orders_2(sK7) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_12,plain,
% 54.99/7.49      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 54.99/7.49      | ~ l1_orders_2(X0) ),
% 54.99/7.49      inference(cnf_transformation,[],[f75]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_97,plain,
% 54.99/7.49      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 54.99/7.49      | l1_orders_2(X0) != iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_99,plain,
% 54.99/7.49      ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7)) = iProver_top
% 54.99/7.49      | l1_orders_2(sK7) != iProver_top ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_97]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_705,plain,
% 54.99/7.49      ( u1_struct_0(sK7) = sK8
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top
% 54.99/7.49      | r1_tarski(sK8,u1_struct_0(sK7)) != iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_3621,plain,
% 54.99/7.49      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 54.99/7.49      theory(equality) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_3630,plain,
% 54.99/7.49      ( k3_yellow_0(sK7) = k3_yellow_0(sK7) | sK7 != sK7 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_3621]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_3615,plain,( X0 = X0 ),theory(equality) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_3636,plain,
% 54.99/7.49      ( sK7 = sK7 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_3615]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_3616,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4596,plain,
% 54.99/7.49      ( u1_struct_0(sK7) != X0 | sK8 != X0 | sK8 = u1_struct_0(sK7) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_3616]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4703,plain,
% 54.99/7.49      ( u1_struct_0(sK7) != sK8 | sK8 = u1_struct_0(sK7) | sK8 != sK8 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4596]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4704,plain,
% 54.99/7.49      ( sK8 = sK8 ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_3615]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4292,plain,
% 54.99/7.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4303,plain,
% 54.99/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 54.99/7.49      | r1_tarski(X0,X1) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4899,plain,
% 54.99/7.49      ( r1_tarski(sK8,u1_struct_0(sK7)) = iProver_top ),
% 54.99/7.49      inference(superposition,[status(thm)],[c_4292,c_4303]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_3620,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 54.99/7.49      theory(equality) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4586,plain,
% 54.99/7.49      ( m1_subset_1(X0,X1)
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | X1 != u1_struct_0(sK7)
% 54.99/7.49      | X0 != k3_yellow_0(sK7) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_3620]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4827,plain,
% 54.99/7.49      ( m1_subset_1(X0,sK8)
% 54.99/7.49      | ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | X0 != k3_yellow_0(sK7)
% 54.99/7.49      | sK8 != u1_struct_0(sK7) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4586]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5264,plain,
% 54.99/7.49      ( ~ m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | m1_subset_1(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | k3_yellow_0(sK7) != k3_yellow_0(sK7)
% 54.99/7.49      | sK8 != u1_struct_0(sK7) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4827]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5267,plain,
% 54.99/7.49      ( k3_yellow_0(sK7) != k3_yellow_0(sK7)
% 54.99/7.49      | sK8 != u1_struct_0(sK7)
% 54.99/7.49      | m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7)) != iProver_top
% 54.99/7.49      | m1_subset_1(k3_yellow_0(sK7),sK8) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_5264]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_8,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 54.99/7.49      inference(cnf_transformation,[],[f71]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_34,negated_conjecture,
% 54.99/7.49      ( ~ v1_xboole_0(sK8) ),
% 54.99/7.49      inference(cnf_transformation,[],[f97]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_533,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK8 != X1 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_534,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,sK8) | r2_hidden(X0,sK8) ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_533]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5644,plain,
% 54.99/7.49      ( ~ m1_subset_1(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_534]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_5645,plain,
% 54.99/7.49      ( m1_subset_1(k3_yellow_0(sK7),sK8) != iProver_top
% 54.99/7.49      | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 54.99/7.49      inference(predicate_to_equality,[status(thm)],[c_5644]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7320,plain,
% 54.99/7.49      ( r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 54.99/7.49      inference(global_propositional_subsumption,
% 54.99/7.49                [status(thm)],
% 54.99/7.49                [c_4284,c_42,c_99,c_705,c_3630,c_3636,c_4703,c_4704,
% 54.99/7.49                 c_4899,c_5267,c_5645]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7322,plain,
% 54.99/7.49      ( r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_7320]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4682,plain,
% 54.99/7.49      ( r2_hidden(sK2(X0,u1_struct_0(sK7)),X0)
% 54.99/7.49      | r1_tarski(X0,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_1]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_7141,plain,
% 54.99/7.49      ( r2_hidden(sK2(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4682]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4683,plain,
% 54.99/7.49      ( ~ r2_hidden(sK2(X0,u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | r1_tarski(X0,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_0]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4975,plain,
% 54.99/7.49      ( ~ r2_hidden(sK2(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))
% 54.99/7.49      | r1_tarski(u1_struct_0(sK7),u1_struct_0(sK7)) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_4683]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_4911,plain,
% 54.99/7.49      ( r1_tarski(sK8,u1_struct_0(sK7)) ),
% 54.99/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_4899]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_29,plain,
% 54.99/7.49      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 54.99/7.49      inference(cnf_transformation,[],[f103]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_31,negated_conjecture,
% 54.99/7.49      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(cnf_transformation,[],[f100]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_303,plain,
% 54.99/7.49      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 54.99/7.49      inference(prop_impl,[status(thm)],[c_31]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_716,plain,
% 54.99/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | u1_struct_0(sK7) != X0
% 54.99/7.49      | sK8 != X0 ),
% 54.99/7.49      inference(resolution_lifted,[status(thm)],[c_29,c_303]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_717,plain,
% 54.99/7.49      ( ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
% 54.99/7.49      | ~ r2_hidden(k3_yellow_0(sK7),sK8)
% 54.99/7.49      | sK8 != u1_struct_0(sK7) ),
% 54.99/7.49      inference(unflattening,[status(thm)],[c_716]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(c_98,plain,
% 54.99/7.49      ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7))
% 54.99/7.49      | ~ l1_orders_2(sK7) ),
% 54.99/7.49      inference(instantiation,[status(thm)],[c_12]) ).
% 54.99/7.49  
% 54.99/7.49  cnf(contradiction,plain,
% 54.99/7.49      ( $false ),
% 54.99/7.49      inference(minisat,
% 54.99/7.49                [status(thm)],
% 54.99/7.49                [c_215990,c_191331,c_70327,c_55980,c_31756,c_26369,
% 54.99/7.49                 c_24075,c_19864,c_19084,c_17138,c_8872,c_7994,c_7322,
% 54.99/7.49                 c_7141,c_4975,c_4911,c_4704,c_4703,c_717,c_618,c_98,
% 54.99/7.49                 c_32,c_35]) ).
% 54.99/7.49  
% 54.99/7.49  
% 54.99/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 54.99/7.49  
% 54.99/7.49  ------                               Statistics
% 54.99/7.49  
% 54.99/7.49  ------ General
% 54.99/7.49  
% 54.99/7.49  abstr_ref_over_cycles:                  0
% 54.99/7.49  abstr_ref_under_cycles:                 0
% 54.99/7.49  gc_basic_clause_elim:                   0
% 54.99/7.49  forced_gc_time:                         0
% 54.99/7.49  parsing_time:                           0.009
% 54.99/7.49  unif_index_cands_time:                  0.
% 54.99/7.49  unif_index_add_time:                    0.
% 54.99/7.49  orderings_time:                         0.
% 54.99/7.49  out_proof_time:                         0.032
% 54.99/7.49  total_time:                             6.555
% 54.99/7.49  num_of_symbols:                         55
% 54.99/7.49  num_of_terms:                           110809
% 54.99/7.49  
% 54.99/7.49  ------ Preprocessing
% 54.99/7.49  
% 54.99/7.49  num_of_splits:                          0
% 54.99/7.49  num_of_split_atoms:                     0
% 54.99/7.49  num_of_reused_defs:                     0
% 54.99/7.49  num_eq_ax_congr_red:                    52
% 54.99/7.49  num_of_sem_filtered_clauses:            1
% 54.99/7.49  num_of_subtypes:                        0
% 54.99/7.49  monotx_restored_types:                  0
% 54.99/7.49  sat_num_of_epr_types:                   0
% 54.99/7.49  sat_num_of_non_cyclic_types:            0
% 54.99/7.49  sat_guarded_non_collapsed_types:        0
% 54.99/7.49  num_pure_diseq_elim:                    0
% 54.99/7.49  simp_replaced_by:                       0
% 54.99/7.49  res_preprocessed:                       145
% 54.99/7.49  prep_upred:                             0
% 54.99/7.49  prep_unflattend:                        186
% 54.99/7.49  smt_new_axioms:                         0
% 54.99/7.49  pred_elim_cands:                        5
% 54.99/7.49  pred_elim:                              8
% 54.99/7.49  pred_elim_cl:                           10
% 54.99/7.50  pred_elim_cycles:                       15
% 54.99/7.50  merged_defs:                            10
% 54.99/7.50  merged_defs_ncl:                        0
% 54.99/7.50  bin_hyper_res:                          18
% 54.99/7.50  prep_cycles:                            4
% 54.99/7.50  pred_elim_time:                         0.056
% 54.99/7.50  splitting_time:                         0.
% 54.99/7.50  sem_filter_time:                        0.
% 54.99/7.50  monotx_time:                            0.001
% 54.99/7.50  subtype_inf_time:                       0.
% 54.99/7.50  
% 54.99/7.50  ------ Problem properties
% 54.99/7.50  
% 54.99/7.50  clauses:                                28
% 54.99/7.50  conjectures:                            1
% 54.99/7.50  epr:                                    3
% 54.99/7.50  horn:                                   20
% 54.99/7.50  ground:                                 5
% 54.99/7.50  unary:                                  3
% 54.99/7.50  binary:                                 9
% 54.99/7.50  lits:                                   83
% 54.99/7.50  lits_eq:                                6
% 54.99/7.50  fd_pure:                                0
% 54.99/7.50  fd_pseudo:                              0
% 54.99/7.50  fd_cond:                                0
% 54.99/7.50  fd_pseudo_cond:                         4
% 54.99/7.50  ac_symbols:                             0
% 54.99/7.50  
% 54.99/7.50  ------ Propositional Solver
% 54.99/7.50  
% 54.99/7.50  prop_solver_calls:                      53
% 54.99/7.50  prop_fast_solver_calls:                 4889
% 54.99/7.50  smt_solver_calls:                       0
% 54.99/7.50  smt_fast_solver_calls:                  0
% 54.99/7.50  prop_num_of_clauses:                    51960
% 54.99/7.50  prop_preprocess_simplified:             75180
% 54.99/7.50  prop_fo_subsumed:                       53
% 54.99/7.50  prop_solver_time:                       0.
% 54.99/7.50  smt_solver_time:                        0.
% 54.99/7.50  smt_fast_solver_time:                   0.
% 54.99/7.50  prop_fast_solver_time:                  0.
% 54.99/7.50  prop_unsat_core_time:                   0.018
% 54.99/7.50  
% 54.99/7.50  ------ QBF
% 54.99/7.50  
% 54.99/7.50  qbf_q_res:                              0
% 54.99/7.50  qbf_num_tautologies:                    0
% 54.99/7.50  qbf_prep_cycles:                        0
% 54.99/7.50  
% 54.99/7.50  ------ BMC1
% 54.99/7.50  
% 54.99/7.50  bmc1_current_bound:                     -1
% 54.99/7.50  bmc1_last_solved_bound:                 -1
% 54.99/7.50  bmc1_unsat_core_size:                   -1
% 54.99/7.50  bmc1_unsat_core_parents_size:           -1
% 54.99/7.50  bmc1_merge_next_fun:                    0
% 54.99/7.50  bmc1_unsat_core_clauses_time:           0.
% 54.99/7.50  
% 54.99/7.50  ------ Instantiation
% 54.99/7.50  
% 54.99/7.50  inst_num_of_clauses:                    1469
% 54.99/7.50  inst_num_in_passive:                    885
% 54.99/7.50  inst_num_in_active:                     2369
% 54.99/7.50  inst_num_in_unprocessed:                64
% 54.99/7.50  inst_num_of_loops:                      3605
% 54.99/7.50  inst_num_of_learning_restarts:          1
% 54.99/7.50  inst_num_moves_active_passive:          1229
% 54.99/7.50  inst_lit_activity:                      0
% 54.99/7.50  inst_lit_activity_moves:                2
% 54.99/7.50  inst_num_tautologies:                   0
% 54.99/7.50  inst_num_prop_implied:                  0
% 54.99/7.50  inst_num_existing_simplified:           0
% 54.99/7.50  inst_num_eq_res_simplified:             0
% 54.99/7.50  inst_num_child_elim:                    0
% 54.99/7.50  inst_num_of_dismatching_blockings:      8832
% 54.99/7.50  inst_num_of_non_proper_insts:           12124
% 54.99/7.50  inst_num_of_duplicates:                 0
% 54.99/7.50  inst_inst_num_from_inst_to_res:         0
% 54.99/7.50  inst_dismatching_checking_time:         0.
% 54.99/7.50  
% 54.99/7.50  ------ Resolution
% 54.99/7.50  
% 54.99/7.50  res_num_of_clauses:                     39
% 54.99/7.50  res_num_in_passive:                     39
% 54.99/7.50  res_num_in_active:                      0
% 54.99/7.50  res_num_of_loops:                       149
% 54.99/7.50  res_forward_subset_subsumed:            378
% 54.99/7.50  res_backward_subset_subsumed:           2
% 54.99/7.50  res_forward_subsumed:                   0
% 54.99/7.50  res_backward_subsumed:                  1
% 54.99/7.50  res_forward_subsumption_resolution:     14
% 54.99/7.50  res_backward_subsumption_resolution:    0
% 54.99/7.50  res_clause_to_clause_subsumption:       127431
% 54.99/7.50  res_orphan_elimination:                 0
% 54.99/7.50  res_tautology_del:                      793
% 54.99/7.50  res_num_eq_res_simplified:              0
% 54.99/7.50  res_num_sel_changes:                    0
% 54.99/7.50  res_moves_from_active_to_pass:          0
% 54.99/7.50  
% 54.99/7.50  ------ Superposition
% 54.99/7.50  
% 54.99/7.50  sup_time_total:                         0.
% 54.99/7.50  sup_time_generating:                    0.
% 54.99/7.50  sup_time_sim_full:                      0.
% 54.99/7.50  sup_time_sim_immed:                     0.
% 54.99/7.50  
% 54.99/7.50  sup_num_of_clauses:                     7722
% 54.99/7.50  sup_num_in_active:                      717
% 54.99/7.50  sup_num_in_passive:                     7005
% 54.99/7.50  sup_num_of_loops:                       720
% 54.99/7.50  sup_fw_superposition:                   3749
% 54.99/7.50  sup_bw_superposition:                   5265
% 54.99/7.50  sup_immediate_simplified:               656
% 54.99/7.50  sup_given_eliminated:                   0
% 54.99/7.50  comparisons_done:                       0
% 54.99/7.50  comparisons_avoided:                    33
% 54.99/7.50  
% 54.99/7.50  ------ Simplifications
% 54.99/7.50  
% 54.99/7.50  
% 54.99/7.50  sim_fw_subset_subsumed:                 122
% 54.99/7.50  sim_bw_subset_subsumed:                 24
% 54.99/7.50  sim_fw_subsumed:                        453
% 54.99/7.50  sim_bw_subsumed:                        83
% 54.99/7.50  sim_fw_subsumption_res:                 9
% 54.99/7.50  sim_bw_subsumption_res:                 0
% 54.99/7.50  sim_tautology_del:                      10
% 54.99/7.50  sim_eq_tautology_del:                   82
% 54.99/7.50  sim_eq_res_simp:                        9
% 54.99/7.50  sim_fw_demodulated:                     0
% 54.99/7.50  sim_bw_demodulated:                     0
% 54.99/7.50  sim_light_normalised:                   0
% 54.99/7.50  sim_joinable_taut:                      0
% 54.99/7.50  sim_joinable_simp:                      0
% 54.99/7.50  sim_ac_normalised:                      0
% 54.99/7.50  sim_smt_subsumption:                    0
% 54.99/7.50  
%------------------------------------------------------------------------------
